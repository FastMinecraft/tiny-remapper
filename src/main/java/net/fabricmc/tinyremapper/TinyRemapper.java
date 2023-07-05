/*
 * Copyright (c) 2016, 2018, Player, asie
 * Copyright (c) 2016, 2022, FabricMC
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package net.fabricmc.tinyremapper;

import it.unimi.dsi.fastutil.ints.*;
import it.unimi.dsi.fastutil.objects.*;
import net.fabricmc.tinyremapper.IMappingProvider.MappingAcceptor;
import net.fabricmc.tinyremapper.IMappingProvider.Member;
import net.fabricmc.tinyremapper.api.TrClass;
import net.fabricmc.tinyremapper.api.TrEnvironment;
import net.fabricmc.tinyremapper.api.TrMember;
import net.fabricmc.tinyremapper.api.TrMember.MemberType;
import org.objectweb.asm.*;
import org.objectweb.asm.commons.Remapper;
import org.objectweb.asm.util.CheckClassAdapter;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.*;
import java.util.concurrent.*;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BiConsumer;
import java.util.function.Consumer;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

@SuppressWarnings({"ForLoopReplaceableByForEach", "WhileLoopReplaceableByForEach"})
public class TinyRemapper {
    private static final int threadCount = Math.max(Runtime.getRuntime().availableProcessors(), 2);
    private static final ThreadPoolExecutor threadPool = new ThreadPoolExecutor(
        threadCount,
        threadCount,
        15L,
        TimeUnit.SECONDS,
        new LinkedBlockingQueue<>()
    );

    static {
        threadPool.allowCoreThreadTimeOut(true);
    }

    final ObjectSet<String> forcePropagation;
    final boolean propagatePrivate;
    final LinkedMethodPropagation propagateBridges;
    final LinkedMethodPropagation propagateRecordComponents;
    final boolean logUnknownInvokeDynamic;
    final Remapper extraRemapper;
    final Consumer<String> logger;
    final AtomicReference<Reference2ObjectMap<InputTag, InputTag[]>> singleInputTags =
        new AtomicReference<>(Reference2ObjectMaps.emptyMap()); // cache for tag -> { tag }
    final ObjectArrayList<CompletableFuture<?>> pendingReads = new ObjectArrayList<>(); // reads that need to be waited for before continuing processing (assumes lack of external waiting)
    final ConcurrentHashMap<String, ClassInstance> readClasses = new ConcurrentHashMap<>(); // classes being potentially concurrently read, to be transferred into unsynchronized classes later
    final MrjState defaultState = new MrjState(this, ClassInstance.MRJ_DEFAULT);
    final Int2ObjectMap<MrjState> mrjStates = new Int2ObjectOpenHashMap<>(4, 0.9f);
    final Object2ObjectOpenHashMap<String, String> classMap = new Object2ObjectOpenHashMap<>();
    final Object2ObjectOpenHashMap<String, String> methodMap = new Object2ObjectOpenHashMap<>();
    final Object2ObjectOpenHashMap<String, String> methodArgMap = new Object2ObjectOpenHashMap<>();
    final Object2ObjectOpenHashMap<String, String> fieldMap = new Object2ObjectOpenHashMap<>();
    final ConcurrentHashMap<MemberInstance, Set<String>> conflicts = new ConcurrentHashMap<>();
    final Set<ClassInstance> classesToMakePublic = Collections.newSetFromMap(new ConcurrentHashMap<>());
    final Set<MemberInstance> membersToMakePublic = Collections.newSetFromMap(new ConcurrentHashMap<>());
    final boolean ignoreFieldDesc;
    private final boolean check = false;
    private final boolean keepInputData;
    private final boolean removeFrames;
    private final boolean ignoreConflicts;
    private final boolean resolveMissing;
    private final boolean checkPackageAccess;
    private final boolean fixPackageAccess;
    private final boolean rebuildSourceFilenames;
    private final boolean skipLocalMapping;
    private final boolean renameInvalidLocals;
    private final Pattern invalidLvNamePattern;
    private final boolean inferNameFromSameLvIndex;
    private final boolean skipConflictsChecking;
    private final boolean cacheMappings;
    private final boolean skipPropagate;
    private final ObjectList<AnalyzeVisitorProvider> analyzeVisitors;
    private final ObjectList<StateProcessor> stateProcessors;
    private final ObjectList<ApplyVisitorProvider> preApplyVisitors;
    private final ObjectList<ApplyVisitorProvider> postApplyVisitors;
    private final ObjectSet<IMappingProvider> mappingProviders;
    private final ObjectArrayList<Future<?>> pendingTasks = new ObjectArrayList<>();
    private boolean mappingsDirty = true;
    private volatile boolean dirty = true; // volatile to make the state debug asserts more reliable, shouldn't actually see concurrent modifications
    private Map<ClassInstance, byte[]> outputBuffer;

    {
        mrjStates.put(defaultState.version, defaultState);
    }

    private TinyRemapper(
        ObjectSet<IMappingProvider> mappingProviders, boolean ignoreFieldDesc,
        int threadCount,
        boolean keepInputData,
        ObjectSet<String> forcePropagation, boolean propagatePrivate,
        LinkedMethodPropagation propagateBridges, LinkedMethodPropagation propagateRecordComponents,
        boolean removeFrames,
        boolean ignoreConflicts,
        boolean resolveMissing,
        boolean checkPackageAccess,
        boolean fixPackageAccess,
        boolean rebuildSourceFilenames,
        boolean skipLocalMapping,
        boolean renameInvalidLocals, Pattern invalidLvNamePattern, boolean inferNameFromSameLvIndex,
        boolean skipConflictsChecking,
        boolean cacheMappings,
        boolean skipPropagate,
        boolean logUnknownInvokeDynamic,
        ObjectList<AnalyzeVisitorProvider> analyzeVisitors, ObjectList<StateProcessor> stateProcessors,
        ObjectList<ApplyVisitorProvider> preApplyVisitors, ObjectList<ApplyVisitorProvider> postApplyVisitors,
        Remapper extraRemapper,
        Consumer<String> logger
    ) {
        this.mappingProviders = mappingProviders;
        this.ignoreFieldDesc = ignoreFieldDesc;
        this.keepInputData = keepInputData;
        this.forcePropagation = forcePropagation;
        this.propagatePrivate = propagatePrivate;
        this.propagateBridges = propagateBridges;
        this.propagateRecordComponents = propagateRecordComponents;
        this.removeFrames = removeFrames;
        this.ignoreConflicts = ignoreConflicts;
        this.resolveMissing = resolveMissing;
        this.checkPackageAccess = checkPackageAccess;
        this.fixPackageAccess = fixPackageAccess;
        this.rebuildSourceFilenames = rebuildSourceFilenames;
        this.skipLocalMapping = skipLocalMapping;
        this.renameInvalidLocals = renameInvalidLocals;
        this.invalidLvNamePattern = invalidLvNamePattern;
        this.inferNameFromSameLvIndex = inferNameFromSameLvIndex;
        this.skipConflictsChecking = skipConflictsChecking;
        this.cacheMappings = cacheMappings;
        this.skipPropagate = skipPropagate;
        this.logUnknownInvokeDynamic = logUnknownInvokeDynamic;
        this.analyzeVisitors = analyzeVisitors;
        this.stateProcessors = stateProcessors;
        this.preApplyVisitors = preApplyVisitors;
        this.postApplyVisitors = postApplyVisitors;
        this.extraRemapper = extraRemapper;
        this.logger = logger;
    }

    public static Builder newRemapper() {
        return new Builder();
    }

    private static int analyzeMrjVersion(MrjPath file, String name) {
        Path pathOrNull = file.pathOrNull();

        if (pathOrNull == null) {
            return ClassInstance.MRJ_DEFAULT;
        }

        return analyzeMrjVersion(pathOrNull, name);
    }

    /**
     * Determine the MRJ version of the supplied class file and name.
     *
     * <p>This assumes that the file path follows the usual META-INF/versions/{@code <version>}/pkg/for/cls.class form.
     */
    private static int analyzeMrjVersion(Path file, String name) {
        assert file.getFileName().toString().endsWith(".class");

        int pkgCount = 0;
        int pos = 0;

        while ((pos = name.indexOf('/', pos) + 1) > 0) {
            pkgCount++;
        }

        name = name + ".class";

        int pathNameCount = file.getNameCount();
        int pathNameOffset = pathNameCount - pkgCount - 1; // path index for root package

        if (pathNameOffset >= 3
            && file.getName(pathNameOffset - 3).toString().equals("META-INF") // root pkg is in META-INF/x/x
            && file.getName(pathNameOffset - 2).toString().equals("versions") // root pkg is in META-INF/versions/x
            && file.subpath(pathNameOffset, pathNameCount).toString().replace('\\', '/').regionMatches(0, name, 0, name.length())) { // verify class name == path from root pkg dir, ignores suffix like .class
            try {
                return Integer.parseInt(file.getName(pathNameOffset - 1).toString());
            } catch (NumberFormatException e) {
                // ignore
            }
        }

        return ClassInstance.MRJ_DEFAULT;
    }

    private static void waitForAll(ObjectArrayList<Future<?>> futures) {
        try {
            for (int i = 0, futuresSize = futures.size(); i < futuresSize; i++) {
                Future<?> future = futures.get(i);
                future.get();
            }
        } catch (InterruptedException | ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    private static String getClassName(String nameDesc, MemberType type) {
        int descStart = getDescStart(nameDesc, type);
        int nameStart = nameDesc.lastIndexOf('/', descStart - 1);
        if (nameStart == -1) nameStart = 0;

        return nameDesc.substring(0, nameStart);
    }

    private static String stripClassName(String nameDesc, MemberType type) {
        int descStart = getDescStart(nameDesc, type);
        int nameStart = nameDesc.lastIndexOf('/', descStart - 1);
        if (nameStart == -1) nameStart = 0;

        return nameDesc.substring(nameStart + 1);
    }

    private static int getDescStart(String nameDesc, MemberType type) {
        int ret;

        if (type == TrMember.MemberType.METHOD) {
            ret = nameDesc.indexOf('(');
        } else {
            ret = nameDesc.indexOf(";;");
        }

        if (ret == -1) ret = nameDesc.length();

        return ret;
    }

    @SuppressWarnings("ForLoopReplaceableByForEach")
    public void finish() {
        long targetTime = System.currentTimeMillis() + 20_000;

        try {
            for (int i = 0; i < pendingTasks.size(); i++) {
                pendingTasks.get(i).get(targetTime - System.currentTimeMillis(), TimeUnit.MILLISECONDS);
            }
        } catch (InterruptedException | TimeoutException | ExecutionException e) {
            e.printStackTrace();
        }

        outputBuffer = null;
        defaultState.classes.clear();
        mrjStates.clear();
    }

    public InputTag createInputTag() {
        InputTag ret = new InputTag();
        InputTag[] array = {ret};

        Reference2ObjectMap<InputTag, InputTag[]> oldTags, newTags;

        do { // cas loop
            oldTags = this.singleInputTags.get();
            newTags = new Reference2ObjectOpenHashMap<>(oldTags.size() + 1);
            newTags.putAll(oldTags);
            newTags.put(ret, array);
        } while (!singleInputTags.compareAndSet(oldTags, newTags));

        return ret;
    }

    public void readInputs(final Path... inputs) {
        readInputs(null, inputs);
    }

    public void readInputs(InputTag tag, Path... inputs) {
        read(inputs, true, tag).join();
    }

    public void readInputs(byte[]... inputs) {
        readInputsAsync(inputs).join();
    }

    public CompletableFuture<List<ClassInstance>> readInputsAsync(byte[]... inputs) {
        return readClassAsync(true, inputs);
    }

    public CompletableFuture<?> readInputsAsync(Path... inputs) {
        return readInputsAsync(null, inputs);
    }

    public CompletableFuture<?> readInputsAsync(InputTag tag, Path... inputs) {
        CompletableFuture<?> ret = read(inputs, true, tag);

        if (!ret.isDone()) {
            pendingReads.add(ret);
        } else {
            ret.join();
        }

        return ret;
    }

    public void readClassPath(final Path... inputs) {
        read(inputs, false, null).join();
    }

    public CompletableFuture<?> readClassPathAsync(final Path... inputs) {
        CompletableFuture<?> ret = read(inputs, false, null);

        if (!ret.isDone()) {
            pendingReads.add(ret);
        } else {
            ret.join();
        }

        return ret;
    }

    public void readClassPath(byte[]... inputs) {
        readClassPathAsync(inputs).join();
    }

    private CompletableFuture<List<ClassInstance>> readClassPathAsync(byte[]... inputs) {
        return readClassAsync(false, inputs);
    }

    private CompletableFuture<List<ClassInstance>> readClassAsync(boolean isInput, byte[]... inputs) {
        InputTag[] tags = singleInputTags.get().get(null);
        ObjectArrayList<CompletableFuture<ClassInstance>> futures = new ObjectArrayList<>();

        for (byte[] entry : inputs) {
            futures.add(CompletableFuture.supplyAsync(() -> {
                try {
                    return analyze(isInput, tags, "/", new StaticMrjPath(entry, null));
                } catch (IOException e) {
                    throw new UncheckedIOException(e);
                }
            }, threadPool));
        }

        dirty = true;
        CompletableFuture<List<ClassInstance>> result = CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]))
            .thenApply(ignore -> futures.stream()
                .map(CompletableFuture::join)
                .filter(Objects::nonNull)
                .collect(Collectors.toList()))
            .whenComplete((res, throwable) -> {
                if (res != null) {
                    for (ClassInstance node : res) {
                        addClass(node, readClasses, true);
                    }
                }
            });
        this.pendingTasks.add(result);
        return result;
    }

    private CompletableFuture<List<ClassInstance>> read(Path[] inputs, boolean isInput, InputTag tag) {
        InputTag[] tags = singleInputTags.get().get(tag);
        ObjectArrayList<CompletableFuture<List<ClassInstance>>> futures = new ObjectArrayList<>();
        ObjectList<FileSystemReference> fsToClose = ObjectLists.synchronize(new ObjectArrayList<>());

        for (Path input : inputs) {
            futures.add(read(input, isInput, tags, fsToClose, true));
        }

        CompletableFuture<List<ClassInstance>> ret;

        if (futures.isEmpty()) {
            return CompletableFuture.completedFuture(Collections.emptyList());
        } else if (futures.size() == 1) {
            ret = futures.get(0);
        } else {
            ret = CompletableFuture.allOf(futures.toArray(new CompletableFuture[0]))
                .thenApply(ignore -> futures.stream().flatMap(f -> f.join().stream()).collect(Collectors.toList()));
        }

        if (!dirty) {
            dirty = true;

            for (MrjState state : mrjStates.values()) {
                state.dirty = true;
            }
        }

        return ret.whenComplete((res, exc) -> {
            for (FileSystemReference fs : fsToClose) {
                try {
                    fs.close();
                } catch (IOException e) {
                    // ignore
                }
            }

            if (res != null) {
                for (ClassInstance node : res) {
                    addClass(node, readClasses, true);
                }
            }

            assert dirty;
        });
    }

    private void addClass(ClassInstance cls, Map<String, ClassInstance> out, boolean isVersionAware) {
        // two different MRJ version will not cause warning if isVersionAware is true
        String name = isVersionAware ? ClassInstance.getMrjName(cls.getName(), cls.getMrjVersion()) : cls.getName();

        // add new class or replace non-input class with input class, warn if two input classes clash
        for (; ; ) {
            ClassInstance prev = out.putIfAbsent(name, cls);
            if (prev == null) return;

            if (prev.isMrjCopy() && prev.getMrjVersion() < cls.getMrjVersion()) {
                // if {@code prev} is MRJ copy and {@code prev}'s origin version is less than {@code cls}'s
                // origin version, then we should update the class.
                if (out.replace(name, prev, cls)) {
                    return;
                } else {
                    // loop
                }
            } else if (cls.isInput) {
                if (prev.isInput) {
                    logger.accept(String.format("duplicate input class %s, from %s and %s", name, prev.srcPath, cls.srcPath));
                    prev.addInputTags(cls.getInputTags());
                    return;
                } else if (out.replace(name, prev, cls)) { // cas with retry-loop on failure
                    cls.addInputTags(prev.getInputTags());
                    return;
                } else {
                    // loop
                }
            } else {
                if (out == readClasses) {
                    for (MrjState value : mrjStates.values()) {
                        value.mergedClasspath = false;
                    }

                    mappingsDirty = true;
                }

                prev.addInputTags(cls.getInputTags());
                return;
            }
        }
    }

    private CompletableFuture<List<ClassInstance>> read(
        final Path file,
        boolean isInput,
        InputTag[] tags,
        final List<FileSystemReference> fsToClose,
        boolean isParentLevel
    ) {
        return read(file, isInput, tags, file.toString(), fsToClose, isParentLevel);
    }

    private CompletableFuture<List<ClassInstance>> read(
        Path file,
        boolean isInput,
        InputTag[] tags,
        final String srcPath,
        List<FileSystemReference> fsToClose,
        boolean isParentLevel
    ) {
        if (file.toString().endsWith(".class")) {
            CompletableFuture<List<ClassInstance>> result = CompletableFuture.supplyAsync(() -> {
                try {
                    ClassInstance res = analyze(isInput, tags, srcPath, new FileMrjPath(file));
                    if (res != null) return Collections.singletonList(res);
                } catch (IOException e) {
                    logger.accept("Failed to read " + file.toAbsolutePath());
                    e.printStackTrace();
                } catch (Throwable throwable) {
                    logger.accept("Failed to read " + file.toAbsolutePath());
                    throw throwable;
                }

                return Collections.emptyList();
            }, threadPool);
            this.pendingTasks.add(result);
            return result;
        } else if (isParentLevel) {
            ObjectArrayList<CompletableFuture<List<ClassInstance>>> ret = new ObjectArrayList<>();

            try {
                if (Files.isDirectory(file)) {
                    Files.walkFileTree(file, new SimpleFileVisitor<Path>() {
                        @Override
                        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                            if (file.toString().endsWith(".class")) {
                                ret.add(read(file, isInput, tags, srcPath, fsToClose, false));
                            }

                            return FileVisitResult.CONTINUE;
                        }
                    });
                } else {
                    FileSystemReference fs = FileSystemReference.openJar(file);
                    fsToClose.add(fs);
                    Files.walkFileTree(fs.getPath("/"), new SimpleFileVisitor<Path>() {
                        @Override
                        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                            if (file.toString().endsWith(".class")) {
                                ret.add(read(file, isInput, tags, srcPath, fsToClose, false));
                            }

                            return FileVisitResult.CONTINUE;
                        }
                    });
                }

                CompletableFuture<List<ClassInstance>> result = CompletableFuture.allOf(ret.toArray(new CompletableFuture[0])).thenApply(
                    unused ->
                        ret.stream()
                            .map(CompletableFuture::join)
                            .flatMap(Collection::stream)
                            .collect(Collectors.toList()));
                this.pendingTasks.add(result);
                return result;
            } catch (IOException e) {
                logger.accept(file.toAbsolutePath().toString());
                e.printStackTrace();
            }
        }

        return CompletableFuture.completedFuture(Collections.emptyList());
    }

    private ClassInstance analyze(boolean isInput, InputTag[] tags, String srcPath, MrjPath file) throws IOException {
        byte[] data = file.bytes();
        ClassReader reader;

        try {
            reader = new ClassReader(data);
        } catch (Throwable t) {
            throw new RuntimeException("error analyzing " + file + " from " + srcPath, t);
        }

        if ((reader.getAccess() & Opcodes.ACC_MODULE) != 0)
            return null; // special attribute for module-info.class, can't be a regular class

        final ClassInstance ret = new ClassInstance(this, isInput, tags, srcPath, isInput ? data : null);

        reader.accept(new ClassVisitor(Opcodes.ASM9) {
            @Override
            public void visit(
                int version,
                int access,
                String name,
                String signature,
                String superName,
                String[] interfaces
            ) {
                int mrjVersion = analyzeMrjVersion(file, name);
                ret.init(name, version, mrjVersion, signature, superName, access, interfaces);

                for (int i = analyzeVisitors.size() - 1; i >= 0; i--) {
                    cv = analyzeVisitors.get(i).insertAnalyzeVisitor(mrjVersion, name, cv);
                }

                super.visit(version, access, name, signature, superName, interfaces);
            }

            @Override
            public MethodVisitor visitMethod(
                int access,
                String name,
                String desc,
                String signature,
                String[] exceptions
            ) {
                MemberInstance prev = ret.addMember(new MemberInstance(TrMember.MemberType.METHOD, ret, name, desc, access, ret.getMembers().size()));
                if (prev != null)
                    throw new RuntimeException(String.format("duplicate method %s/%s%s in inputs", ret.getName(), name, desc));

                return super.visitMethod(access, name, desc, signature, exceptions);
            }

            @Override
            public FieldVisitor visitField(int access, String name, String desc, String signature, Object value) {
                MemberInstance prev = ret.addMember(new MemberInstance(TrMember.MemberType.FIELD, ret, name, desc, access, ret.getMembers().size()));
                if (prev != null)
                    throw new RuntimeException(String.format("duplicate field %s/%s;;%s in inputs", ret.getName(), name, desc));

                return super.visitField(access, name, desc, signature, value);
            }
        }, ClassReader.SKIP_DEBUG | ClassReader.SKIP_FRAMES | ClassReader.SKIP_CODE);

        return ret;
    }

    private void loadMappings(boolean ignoreCached) {
        if (mappingsDirty || ignoreCached) {
            classMap.clear();
            methodMap.clear();
            methodArgMap.clear();
            fieldMap.clear();

            for (MrjState state : mrjStates.values()) {
                unmergeClasses(state);
                state.dirty = true;
            }

            mappingsDirty = true;
        }

        if (!mappingsDirty) return;
        mappingsDirty = false;
        MappingAcceptor acceptor = new MappingAcceptor() {
            @Override
            public void acceptClass(String srcName, String dstName) {
                if (srcName == null) throw new NullPointerException("null src name");
                if (dstName == null) throw new NullPointerException("null dst name");

                classMap.put(srcName, dstName);
            }

            @Override
            public void acceptMethod(Member method, String dstName) {
                if (method == null) throw new NullPointerException("null src method");
                if (method.owner == null) throw new NullPointerException("null src method owner");
                if (method.name == null) throw new NullPointerException("null src method name");
                if (method.desc == null) throw new NullPointerException("null src method desc");
                if (dstName == null) throw new NullPointerException("null dst name");

                methodMap.put(method.owner + "/" + MemberInstance.getMethodId(method.name, method.desc), dstName);
            }

            @Override
            public void acceptMethodArg(Member method, int lvIndex, String dstName) {
                if (method == null) throw new NullPointerException("null src method");
                if (method.owner == null) throw new NullPointerException("null src method owner");
                if (method.name == null) throw new NullPointerException("null src method name");
                if (method.desc == null) throw new NullPointerException("null src method desc");
                if (dstName == null) throw new NullPointerException("null dst name");

                methodArgMap.put(method.owner + "/" + MemberInstance.getMethodId(method.name, method.desc) + lvIndex, dstName);
            }

            @Override
            public void acceptMethodVar(Member method, int lvIndex, int startOpIdx, int asmIndex, String dstName) {
                if (method == null) throw new NullPointerException("null src method");
                if (method.owner == null) throw new NullPointerException("null src method owner");
                if (method.name == null) throw new NullPointerException("null src method name");
                if (method.desc == null) throw new NullPointerException("null src method desc");
                if (dstName == null) throw new NullPointerException("null dst name");

                // TODO Auto-generated method stub
            }

            @Override
            public void acceptField(Member field, String dstName) {
                if (field == null) throw new NullPointerException("null src field");
                if (field.owner == null) throw new NullPointerException("null src field owner");
                if (field.name == null) throw new NullPointerException("null src field name");
                if (field.desc == null && !ignoreFieldDesc) throw new NullPointerException("null src field desc");
                if (dstName == null) throw new NullPointerException("null dst name");

                fieldMap.put(field.owner + "/" + MemberInstance.getFieldId(field.name, field.desc, ignoreFieldDesc), dstName);
            }
        };

        for (IMappingProvider provider : mappingProviders) {
            provider.load(acceptor);
        }

        checkClassMappings();
    }

    public void replaceMappings(Set<IMappingProvider> providers) {
        if (!equalsMappings(providers)) {
            mappingsDirty = true;
            mappingProviders.clear();
            mappingProviders.addAll(providers);
            dirty = true;
        }
    }

    public boolean equalsMappings(Set<IMappingProvider> other) {
        if (other == mappingProviders) {
            return true;
        }

        if (other.size() != mappingProviders.size()) {
            return false;
        }

        return mappingProviders.containsAll(other);
    }

    private void checkClassMappings() {
        // determine classes that map to the same target name, if there are any print duplicates and throw
        ObjectOpenHashSet<String> testSet = new ObjectOpenHashSet<>(classMap.values());

        if (testSet.size() != classMap.size()) { // src->target is not a 1:1 mapping
            ObjectOpenHashSet<String> duplicates = new ObjectOpenHashSet<>();

            for (String name : classMap.values()) {
                if (!testSet.remove(name)) {
                    duplicates.add(name);
                }
            }

            logger.accept("non-unique class target name mappings:");

            for (String target : duplicates) {
                StringBuilder builder = new StringBuilder();
                builder.append("  [");
                boolean first = true;

                ObjectIterator<Object2ObjectMap.Entry<String, String>> iterator = classMap.object2ObjectEntrySet().fastIterator();
                while (iterator.hasNext()) {
                    Object2ObjectMap.Entry<String, String> e = iterator.next();

                    if (e.getValue().equals(target)) {
                        if (first) {
                            first = false;
                        } else {
                            builder.append(", ");
                        }

                        builder.append(e.getKey());
                    }
                }

                builder.append("] -> ").append(target);
                logger.accept(builder.toString());
            }

            throw new RuntimeException("duplicate class target name mappings detected");
        }
    }

    private void unmergeClasses(MrjState state) {
        state.mergedClasspath = false;

        for (ClassInstance node : state.classes.values()) {
            node.parents.clear();
            node.children.clear();
        }
    }

    private void mergeClasspath(MrjState state) {
        if (state.mergedClasspath) return;
        state.mergedClasspath = true;

        for (ClassInstance node : state.classes.values()) {
            if (node.isInput) continue;
            assert node.getSuperName() != null;

            ClassInstance parent = state.getClass(node.getSuperName());

            if (parent != null) {
                node.parents.add(parent);
                parent.children.add(node);
            }

            for (String iface : node.getInterfaceNames0()) {
                parent = state.getClass(iface);

                if (parent != null) {
                    node.parents.add(parent);
                    parent.children.add(node);
                }
            }
        }
    }

    private void mergeInput(MrjState state) {
        for (ClassInstance node : state.classes.values().parallelStream()
            .filter(node -> node.isInput)
            .collect(Collectors.toList())) {
            assert node.getSuperName() != null;

            ClassInstance parent = state.getClass(node.getSuperName());

            if (parent != null) {
                node.parents.add(parent);
                parent.children.add(node);
            }

            for (String iface : node.getInterfaceNames0()) {
                parent = state.getClass(iface);

                if (parent != null) {
                    node.parents.add(parent);
                    parent.children.add(node);
                }
            }
        }
    }

    private void unmergeInput(MrjState state) {
        state.classes.values().parallelStream()
            .filter(node -> node.isInput)
            .flatMap(node -> node.parents.stream())
            .distinct()
            .forEach(node -> node.children.removeIf(child -> child.isInput));
    }

    private void propagate(MrjState state) {
        if (skipPropagate) return;
        conflicts.clear();
        state.classes.values().parallelStream().forEach(value -> {
            value.resolvedMembers = new ConcurrentHashMap<>();

            for (MemberInstance member : value.getMembers()) {
                member.forceSetNewName(null);
                member.newNameOriginatingCls = null;
            }
        });
        ObjectArrayList<Future<?>> futures = new ObjectArrayList<>();
        ObjectArrayList<Object2ObjectMap.Entry<String, String>> tasks = new ObjectArrayList<>();
        int maxTasks = methodMap.size() / threadCount / 4;

        for (Object2ObjectMap.Entry<String, String> entry : methodMap.object2ObjectEntrySet()) {
            tasks.add(entry);

            if (tasks.size() >= maxTasks) {
                futures.add(threadPool.submit(new Propagation(state, MemberType.METHOD, tasks)));
                tasks.clear();
            }
        }

        futures.add(threadPool.submit(new Propagation(state, TrMember.MemberType.METHOD, tasks)));
        tasks.clear();

        for (Object2ObjectMap.Entry<String, String> entry : fieldMap.object2ObjectEntrySet()) {
            tasks.add(entry);

            if (tasks.size() >= maxTasks) {
                futures.add(threadPool.submit(new Propagation(state, MemberType.FIELD, tasks)));
                tasks.clear();
            }
        }

        futures.add(threadPool.submit(new Propagation(state, TrMember.MemberType.FIELD, tasks)));
        tasks.clear();

        waitForAll(futures);

        handleConflicts(state);
    }

    private void handleConflicts(MrjState state) {
        if (skipConflictsChecking) return;

        boolean targetNameCheckFailed = state.classes.values().stream().anyMatch(cls -> {
            boolean _targetNameCheckFailed = false;
            ObjectOpenHashSet<String> testSet = new ObjectOpenHashSet<>();

            for (MemberInstance member : cls.getMembers()) {
                String name = member.getNewMappedName();
                if (name == null) name = member.name;

                testSet.add(MemberInstance.getId(member.type, name, member.desc, ignoreFieldDesc));
            }

            if (testSet.size() != cls.getMembers().size()) {
                _targetNameCheckFailed = true;

                Object2ObjectOpenHashMap<String, ObjectArrayList<MemberInstance>> duplicates = new Object2ObjectOpenHashMap<>();

                for (MemberInstance member : cls.getMembers()) {
                    String name = member.getNewMappedName();
                    if (name == null) name = member.name;

                    duplicates.computeIfAbsent(MemberInstance.getId(member.type, name, member.desc, ignoreFieldDesc), ignore -> new ObjectArrayList<>()).add(member);
                }

                for (ObjectIterator<Object2ObjectMap.Entry<String, ObjectArrayList<MemberInstance>>> iterator = duplicates.object2ObjectEntrySet().fastIterator(); iterator.hasNext(); ) {
                    Object2ObjectMap.Entry<String, ObjectArrayList<MemberInstance>> e = iterator.next();
                    String nameDesc = e.getKey();
                    ObjectArrayList<MemberInstance> members = e.getValue();
                    if (members.size() < 2) continue;

                    MemberInstance anyMember = members.get(0);
                    StringBuilder builder = new StringBuilder();
                    builder.append("  ").append(anyMember.type).append("s ").append(cls.getName()).append("/[");

                    for (int i = 0; i < members.size(); i++) {
                        if (i != 0) builder.append(", ");

                        MemberInstance member = members.get(i);

                        if (member.newNameOriginatingCls != null && !member.newNameOriginatingCls.equals(cls.getName())) {
                            builder.append(member.newNameOriginatingCls);
                            builder.append('/');
                        }

                        builder.append(member.name);
                    }

                    builder.append(']').append(MemberInstance.getId(
                        anyMember.type,
                        "",
                        anyMember.desc,
                        ignoreFieldDesc
                    ));
                    builder.append(" -> ").append(MemberInstance.getNameFromId(
                        anyMember.type,
                        nameDesc,
                        ignoreFieldDesc
                    ));
                    logger.accept(builder.toString());
                }
            }

            return _targetNameCheckFailed;
        });

        if (targetNameCheckFailed) {
            logger.accept("Mapping target name conflicts detected:");
        }

        boolean unfixableConflicts = false;

        if (!conflicts.isEmpty()) {
            logger.accept("Mapping source name conflicts detected:");

            for (Map.Entry<MemberInstance, Set<String>> entry : conflicts.entrySet()) {
                MemberInstance member = entry.getKey();
                String newName = member.getNewMappedName();
                Set<String> names = entry.getValue();
                names.add(member.cls.getName() + "/" + newName);

                logger.accept(String.format("  %s %s %s (%s) -> %s", member.cls.getName(), member.type.name(), member.name, member.desc, names));

                if (ignoreConflicts) {
                    Object2ObjectOpenHashMap<String, String> mappings = member.type == TrMember.MemberType.METHOD ? methodMap : fieldMap;
                    String mappingName = mappings.get(member.cls.getName() + "/" + member.getId());

                    if (mappingName == null) { // no direct mapping match, try parents
                        ObjectArrayFIFOQueue<ClassInstance> queue = new ObjectArrayFIFOQueue<>(member.cls.parents.size());
                        for (ClassInstance parent : member.cls.parents) {
                            queue.enqueue(parent);
                        }

                        while (!queue.isEmpty()) {
                            ClassInstance cls = queue.dequeue();
                            mappingName = mappings.get(cls.getName() + "/" + member.getId());
                            if (mappingName != null) break;

                            for (ClassInstance parent : cls.parents) {
                                queue.enqueue(parent);
                            }
                        }
                    }

                    if (mappingName == null) {
                        unfixableConflicts = true;
                    } else {
                        member.forceSetNewName(mappingName);
                        logger.accept("    fixable: replaced with " + mappingName);
                    }
                }
            }
        }

        if (!conflicts.isEmpty() && !ignoreConflicts || unfixableConflicts || targetNameCheckFailed) {
            if (ignoreConflicts || targetNameCheckFailed) logger.accept("There were unfixable conflicts.");

            throw new RuntimeException("Unfixable conflicts");
        }
    }

    public void apply(final BiConsumer<String, byte[]> outputConsumer) {
        apply(outputConsumer, (InputTag[]) null);
    }

    public void apply(final BiConsumer<String, byte[]> outputConsumer, InputTag... inputTags) {
        // We expect apply() to be invoked only once if the user didn't request any input tags. Invoking it multiple
        // times still works with keepInputData=true, but wastes some time by redoing most processing.
        // With input tags the first apply invocation computes the entire output, but yields only what matches the given
        // input tags. The output data is being kept for eventual further apply() outputs, only finish() clears it.
        boolean hasInputTags = !singleInputTags.get().isEmpty();

        synchronized (this) { // guard against concurrent apply invocations
            refresh();

            if (outputBuffer == null) { // first (inputTags present) or full (no input tags) output invocation, process everything but don't output if input tags are present
                BiConsumer<ClassInstance, byte[]> immediateOutputConsumer;

                if (fixPackageAccess || hasInputTags) { // need re-processing or output buffering for repeated applies
                    outputBuffer = new ConcurrentHashMap<>();
                    immediateOutputConsumer = outputBuffer::put;
                } else {
                    immediateOutputConsumer = (cls, data) -> outputConsumer.accept(ClassInstance.getMrjName(cls.getContext().remapper.map(cls.getName()), cls.getMrjVersion()), data);
                }

                ObjectArrayList<Future<?>> futures = new ObjectArrayList<>();

                for (MrjState state : mrjStates.values()) {
                    mrjRefresh(state);

                    for (final ClassInstance cls : state.classes.values()) {
                        if (!cls.isInput) continue;

                        if (cls.data == null) {
                            if (!hasInputTags && !keepInputData) {
                                throw new IllegalStateException("invoking apply multiple times without input tags or hasInputData");
                            }

                            throw new IllegalStateException("data for input class " + cls + " is missing?!");
                        }

                        futures.add(threadPool.submit(() -> immediateOutputConsumer.accept(cls, apply(cls))));
                    }
                }

                waitForAll(futures);

                boolean needsFixes = !classesToMakePublic.isEmpty() || !membersToMakePublic.isEmpty();

                if (fixPackageAccess) {
                    if (needsFixes) {
                        logger.accept(String.format("Fixing access for %d classes and %d members.", classesToMakePublic.size(), membersToMakePublic.size()));
                    }

                    for (Map.Entry<ClassInstance, byte[]> entry : outputBuffer.entrySet()) {
                        ClassInstance cls = entry.getKey();
                        byte[] data = entry.getValue();

                        if (needsFixes) {
                            data = fixClass(cls, data);
                        }

                        if (hasInputTags) {
                            entry.setValue(data);
                        } else {
                            outputConsumer.accept(ClassInstance.getMrjName(cls.getContext().remapper.map(cls.getName()), cls.getMrjVersion()), data);
                        }
                    }

                    if (!hasInputTags) outputBuffer = null; // don't expect repeat invocations

                    classesToMakePublic.clear();
                    membersToMakePublic.clear();
                } else if (needsFixes) {
                    throw new RuntimeException(String.format("%d classes and %d members need access fixes", classesToMakePublic.size(), membersToMakePublic.size()));
                }
            }

            assert hasInputTags == (outputBuffer != null);

            if (outputBuffer != null) { // partial output selected by input tags
                for (Map.Entry<ClassInstance, byte[]> entry : outputBuffer.entrySet()) {
                    ClassInstance cls = entry.getKey();

                    if (inputTags == null || cls.hasAnyInputTag(inputTags)) {
                        outputConsumer.accept(ClassInstance.getMrjName(cls.getContext().remapper.map(cls.getName()), cls.getMrjVersion()), entry.getValue());
                    }
                }
            }
        }
    }

    /**
     * This function will setup {@code mrjClasses} with any new MRJ version
     * added. It will put the result of {@code constructMrjCopy} from lower
     * MRJ version to the new version.
     *
     * @param newVersions the new versions that need to be added in to {@code mrjClasses}
     */
    private void fixMrjClasses(IntSet newVersions) {
        // ensure the new version is added from lowest to highest
        IntIterator iterator = newVersions.iterator();
        while (iterator.hasNext()) {
            int newVersion = iterator.next();
            MrjState newState = new MrjState(this, newVersion);

            if (mrjStates.put(newVersion, newState) != null) {
                throw new RuntimeException("internal error: duplicate versions in mrjClasses");
            }

            // find the fromVersion that just lower the the toVersion
            OptionalInt fromVersion = Arrays.stream(mrjStates.keySet().toIntArray())
                .filter(v -> v < newVersion)
                .max();

            if (fromVersion.isPresent()) {
                Object2ObjectOpenHashMap<String, ClassInstance> fromClasses = mrjStates.get(fromVersion.getAsInt()).classes;

                for (ClassInstance cls : fromClasses.values()) {
                    addClass(cls.constructMrjCopy(newState), newState.classes, false);
                }
            }
        }
    }

    public void removeInput() {
        for (MrjState state : mrjStates.values()) {
            removeInput(state);
        }
    }

    public void removeInput(MrjState state) {
        synchronized (this) {
            unmergeInput(state);
            state.classes.values().removeIf(node -> node.isInput);
        }
    }

    public void prepareClasses() {
        synchronized (this) {
            _prepareClasses();
        }
    }

    private void _prepareClasses() {
        if (!readClasses.isEmpty()) {
            // fix any new adding MRJ versions
            IntSet verisons = new IntRBTreeSet();
            for (ClassInstance classInstance : readClasses.values()) {
                int mrjVersion = classInstance.getMrjVersion();
                verisons.add(mrjVersion);
            }
            verisons.removeAll(mrjStates.keySet());
            fixMrjClasses(verisons);

            for (ClassInstance cls : readClasses.values()) {
                // TODO: this might be able to optimize, any suggestion?
                int clsVersion = cls.getMrjVersion();
                MrjState state = mrjStates.get(clsVersion);
                cls.setContext(state);
                addClass(cls, state.classes, false);

                IntIterator iterator = mrjStates.keySet().iterator();
                while (iterator.hasNext()) {
                    int version = iterator.nextInt();
                    if (version > clsVersion) {
                        MrjState newState = mrjStates.get(version);
                        addClass(cls.constructMrjCopy(newState), newState.classes, false);
                    }
                }
            }

            readClasses.clear();
        }
    }

    private void refresh() {
        if (!dirty) {
            assert pendingReads.isEmpty();
            assert readClasses.isEmpty();

            return;
        }

        outputBuffer = null;

        if (!pendingReads.isEmpty()) {
            for (CompletableFuture<?> future : pendingReads) {
                future.join();
            }

            pendingReads.clear();
        }

        _prepareClasses();
        loadMappings(!cacheMappings);

        assert dirty;
        dirty = false;
    }

    private void mrjRefresh(MrjState state) {
        if (!state.dirty) {
            return;
        }

        assert new ObjectOpenHashSet<>(state.classes.values()).size() == state.classes.size();
        assert state.classes.values().stream().map(ClassInstance::getName).distinct().count() == state.classes.size();

        mergeInput(state);
        mergeClasspath(state);
        propagate(state);

        for (StateProcessor processor : stateProcessors) {
            processor.process(state);
        }

        state.dirty = false;
    }

    private byte[] apply(final ClassInstance cls) {
        ClassReader reader = new ClassReader(cls.data);
        ClassWriter writer = new ClassWriter(0);
        int flags = removeFrames ? ClassReader.SKIP_FRAMES : ClassReader.EXPAND_FRAMES;

        ClassVisitor visitor = writer;

        boolean check = false;
        if (check) {
            visitor = new CheckClassAdapter(visitor);
        }

        for (int i = postApplyVisitors.size() - 1; i >= 0; i--) {
            visitor = postApplyVisitors.get(i).insertApplyVisitor(cls, visitor);
        }

        visitor = new AsmClassRemapper(visitor, cls.getContext().remapper, rebuildSourceFilenames,
            checkPackageAccess, skipLocalMapping, renameInvalidLocals, invalidLvNamePattern, inferNameFromSameLvIndex);

        for (int i = preApplyVisitors.size() - 1; i >= 0; i--) {
            visitor = preApplyVisitors.get(i).insertApplyVisitor(cls, visitor);
        }

        reader.accept(visitor, flags);

        // TODO: compute frames (-Xverify:all -XX:-FailOverToOldVerifier)

        if (!keepInputData) cls.data = null;

        return writer.toByteArray();
    }

    private byte[] fixClass(ClassInstance cls, byte[] data) {
        boolean makeClsPublic = classesToMakePublic.contains(cls);
        ObjectOpenHashSet<String> clsMembersToMakePublic = null;

        for (MemberInstance member : cls.getMembers()) {
            if (membersToMakePublic.contains(member)) {
                if (clsMembersToMakePublic == null) clsMembersToMakePublic = new ObjectOpenHashSet<>();

                AsmRemapper remapper = cls.getContext().remapper;
                String mappedName, mappedDesc;

                if (member.type == TrMember.MemberType.FIELD) {
                    mappedName = remapper.mapFieldName(cls, member.name, member.desc);
                    mappedDesc = remapper.mapDesc(member.desc);
                } else {
                    mappedName = remapper.mapMethodName(cls, member.name, member.desc);
                    mappedDesc = remapper.mapMethodDesc(member.desc);
                }

                clsMembersToMakePublic.add(MemberInstance.getId(member.type, mappedName, mappedDesc, ignoreFieldDesc));
            }
        }

        if (!makeClsPublic && clsMembersToMakePublic == null) return data;

        final Set<String> finalClsMembersToMakePublic = clsMembersToMakePublic;

        ClassReader reader = new ClassReader(data);
        ClassWriter writer = new ClassWriter(0);

        reader.accept(new ClassVisitor(Opcodes.ASM9, writer) {
            @Override
            public void visit(
                int version,
                int access,
                String name,
                String signature,
                String superName,
                String[] interfaces
            ) {
                if (makeClsPublic) {
                    access = (access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED)) | Opcodes.ACC_PUBLIC;
                }

                super.visit(version, access, name, signature, superName, interfaces);
            }

            @Override
            public FieldVisitor visitField(int access, String name, String descriptor, String signature, Object value) {
                if (finalClsMembersToMakePublic != null
                    && finalClsMembersToMakePublic.contains(MemberInstance.getFieldId(name, descriptor, ignoreFieldDesc))) {
                    access = (access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED)) | Opcodes.ACC_PUBLIC;
                }

                return super.visitField(access, name, descriptor, signature, value);
            }

            @Override
            public MethodVisitor visitMethod(
                int access,
                String name,
                String descriptor,
                String signature,
                String[] exceptions
            ) {
                if (finalClsMembersToMakePublic != null
                    && finalClsMembersToMakePublic.contains(MemberInstance.getMethodId(name, descriptor))) {
                    access = (access & ~(Opcodes.ACC_PRIVATE | Opcodes.ACC_PROTECTED)) | Opcodes.ACC_PUBLIC;
                }

                return super.visitMethod(access, name, descriptor, signature, exceptions);
            }
        }, 0);

        return writer.toByteArray();
    }

    public synchronized TrEnvironment getEnvironment() {
        refresh();
        mrjRefresh(defaultState);
        return defaultState;
    }

    /**
     * @deprecated Use {@link #getEnvironment} and {@link TrEnvironment#getRemapper} instead.
     */
    @Deprecated
    public AsmRemapper getRemapper() {
        return (AsmRemapper) getEnvironment().getRemapper();
    }

    public boolean isMappingsDirty() {
        return mappingsDirty;
    }

    enum Direction {
        ANY,
        UP,
        DOWN
    }

    public enum LinkedMethodPropagation {
        /**
         * Don't propagate names into methods.
         *
         * <p>This is JVM compliant but doesn't mirror Javac's behavior and decouples bridge methods from their target.
         */
        DISABLED,
        /**
         * Propagate names into methods.
         *
         * <p>Mappings reaching bridge method will be applied to the methods they bridge to.
         */
        ENABLED,
        /**
         * Propagate names into methods and create additional bridges to keep the normally mapped method name intact.
         */
        COMPATIBLE
    }

    public interface Extension {
        void attach(TinyRemapper.Builder builder);
    }

    public interface AnalyzeVisitorProvider {
        ClassVisitor insertAnalyzeVisitor(int mrjVersion, String className, ClassVisitor next);
    }

    public interface StateProcessor {
        void process(TrEnvironment env);
    }

    public interface ApplyVisitorProvider {
        ClassVisitor insertApplyVisitor(TrClass cls, ClassVisitor next);
    }

    private interface MrjPath {
        byte[] bytes() throws IOException;

        Path pathOrNull();
    }

    public static class Builder {
        private final ObjectSet<IMappingProvider> mappingProviders = new ObjectOpenHashSet<>();
        private final ObjectSet<String> forcePropagation = new ObjectOpenHashSet<>();
        private final ObjectList<AnalyzeVisitorProvider> analyzeVisitors = new ObjectArrayList<>();
        private final ObjectList<StateProcessor> stateProcessors = new ObjectArrayList<>();
        private final ObjectList<ApplyVisitorProvider> preApplyVisitors = new ObjectArrayList<>();
        private final ObjectList<ApplyVisitorProvider> postApplyVisitors = new ObjectArrayList<>();
        private boolean ignoreFieldDesc;
        private int threadCount;
        private boolean keepInputData = false;
        private boolean propagatePrivate = false;
        private LinkedMethodPropagation propagateBridges = LinkedMethodPropagation.DISABLED;
        private LinkedMethodPropagation propagateRecordComponents = LinkedMethodPropagation.DISABLED;
        private boolean removeFrames = false;
        private boolean ignoreConflicts = false;
        private boolean resolveMissing = false;
        private boolean checkPackageAccess = false;
        private boolean fixPackageAccess = false;
        private boolean rebuildSourceFilenames = false;
        private boolean skipLocalMapping = false;
        private boolean renameInvalidLocals = false;
        private Pattern invalidLvNamePattern;
        private boolean inferNameFromSameLvIndex;
        private boolean skipConflictsChecking = false;
        private boolean cacheMappings = false;
        private boolean skipPropagate = false;
        private boolean logUnknownInvokeDynamic = true;
        private Remapper extraRemapper;
        private Consumer<String> logger = System.out::println;

        private Builder() {
        }

        public Builder withMappings(IMappingProvider provider) {
            mappingProviders.add(provider);
            return this;
        }

        public Builder ignoreFieldDesc(boolean value) {
            this.ignoreFieldDesc = value;
            return this;
        }

        public Builder threads(int threadCount) {
            this.threadCount = threadCount;
            return this;
        }

        /**
         * Keep the input data after consuming it for apply(), allows multiple apply invocations() even without input tag use.
         */
        public Builder keepInputData(boolean value) {
            this.keepInputData = value;
            return this;
        }

        public Builder withForcedPropagation(Set<String> entries) {
            forcePropagation.addAll(entries);
            return this;
        }

        public Builder propagatePrivate(boolean value) {
            propagatePrivate = value;
            return this;
        }

        public Builder propagateBridges(LinkedMethodPropagation value) {
            propagateBridges = value;
            return this;
        }

        public Builder propagateRecordComponents(LinkedMethodPropagation value) {
            propagateRecordComponents = value;
            return this;
        }

        public Builder removeFrames(boolean value) {
            removeFrames = value;
            return this;
        }

        public Builder ignoreConflicts(boolean value) {
            ignoreConflicts = value;
            return this;
        }

        public Builder resolveMissing(boolean value) {
            resolveMissing = value;
            return this;
        }

        public Builder checkPackageAccess(boolean value) {
            checkPackageAccess = value;
            return this;
        }

        public Builder fixPackageAccess(boolean value) {
            fixPackageAccess = value;
            return this;
        }

        public Builder rebuildSourceFilenames(boolean value) {
            rebuildSourceFilenames = value;
            return this;
        }

        public Builder skipLocalVariableMapping(boolean value) {
            skipLocalMapping = value;
            return this;
        }

        public Builder renameInvalidLocals(boolean value) {
            renameInvalidLocals = value;
            return this;
        }

        /**
         * Pattern that flags matching local variable (and arg) names as invalid for the usual renameInvalidLocals processing.
         */
        public Builder invalidLvNamePattern(Pattern value) {
            this.invalidLvNamePattern = value;
            return this;
        }

        /**
         * Whether to copy lv names from other local variables if the original name was missing or invalid.
         */
        public Builder inferNameFromSameLvIndex(boolean value) {
            this.inferNameFromSameLvIndex = value;
            return this;
        }

        @Deprecated
        public Builder extraAnalyzeVisitor(ClassVisitor visitor) {
            return extraAnalyzeVisitor((mrjVersion, className, next) -> {
                if (next != null)
                    throw new UnsupportedOperationException("can't chain fixed instance analyze visitors");

                return visitor;
            });
        }

        public Builder extraAnalyzeVisitor(AnalyzeVisitorProvider provider) {
            analyzeVisitors.add(provider);
            return this;
        }

        public Builder extraStateProcessor(StateProcessor processor) {
            stateProcessors.add(processor);
            return this;
        }

        public Builder extraRemapper(Remapper remapper) {
            extraRemapper = remapper;
            return this;
        }

        public Builder extraPreApplyVisitor(ApplyVisitorProvider provider) {
            preApplyVisitors.add(provider);
            return this;
        }

        public Builder extraPostApplyVisitor(ApplyVisitorProvider provider) {
            this.postApplyVisitors.add(provider);
            return this;
        }

        public Builder extension(TinyRemapper.Extension extension) {
            extension.attach(this);
            return this;
        }

        public Builder skipConflictsChecking(boolean value) {
            skipConflictsChecking = value;
            return this;
        }

        public Builder skipPropagate(boolean value) {
            skipPropagate = value;
            return this;
        }

        public Builder logUnknownInvokeDynamic(boolean value) {
            logUnknownInvokeDynamic = value;
            return this;
        }

        public Builder cacheMappings(boolean value) {
            cacheMappings = value;
            return this;
        }

        public Builder logger(Consumer<String> value) {
            logger = value;
            return this;
        }

        public TinyRemapper build() {
            TinyRemapper remapper = new TinyRemapper(mappingProviders, ignoreFieldDesc, threadCount,
                keepInputData,
                forcePropagation, propagatePrivate,
                propagateBridges, propagateRecordComponents,
                removeFrames, ignoreConflicts, resolveMissing, checkPackageAccess || fixPackageAccess, fixPackageAccess,
                rebuildSourceFilenames, skipLocalMapping, renameInvalidLocals, invalidLvNamePattern, inferNameFromSameLvIndex,
                skipConflictsChecking, cacheMappings, skipPropagate, logUnknownInvokeDynamic,
                analyzeVisitors, stateProcessors, preApplyVisitors, postApplyVisitors,
                extraRemapper, logger);

            return remapper;
        }
    }

    private static class StaticMrjPath implements MrjPath {
        private final byte[] bytes;
        private final Path path;

        StaticMrjPath(byte[] bytes, Path path) {
            this.bytes = bytes;
            this.path = path;
        }

        @Override
        public byte[] bytes() {
            return bytes;
        }

        @Override
        public Path pathOrNull() {
            return path;
        }
    }

    private static class FileMrjPath implements MrjPath {
        private byte[] bytes;
        private Path path;

        FileMrjPath(Path path) {
            this.path = path;
        }

        @Override
        public byte[] bytes() throws IOException {
            synchronized (this) {
                if (bytes == null) {
                    bytes = Files.readAllBytes(path);
                }

                return bytes;
            }
        }

        @Override
        public Path pathOrNull() {
            return path;
        }
    }

    static final class MrjState implements TrEnvironment {
        private final TinyRemapper tr;
        private final int version;
        private final Object2ObjectOpenHashMap<String, ClassInstance> classes = new Object2ObjectOpenHashMap<>(16, 0.95f);
        private final AsmRemapper remapper;
        private boolean mergedClasspath = false;
        private volatile boolean dirty = true;

        MrjState(TinyRemapper tr, int version) {
            Objects.requireNonNull(tr);

            this.tr = tr;
            this.version = version;
            this.remapper = new AsmRemapper(this);
        }

        @Override
        public int getMrjVersion() {
            return version;
        }

        @Override
        public AsmRemapper getRemapper() {
            return remapper;
        }

        public TinyRemapper getTr() {
            return tr;
        }

        @Override
        public ClassInstance getClass(String internalName) {
            return classes.get(internalName);
        }

        @Override
        public void propagate(TrMember m, String newName) {
            MemberInstance member = (MemberInstance) m;
            ReferenceSet<ClassInstance> visitedUp = new ReferenceOpenHashSet<>();
            ReferenceSet<ClassInstance> visitedDown = new ReferenceOpenHashSet<>();

            Propagator.propagate(member, member.getId(), newName, visitedUp, visitedDown);
        }
    }

    class Propagation implements Runnable {
        private final MrjState state;
        private final MemberType type;
        private final ObjectArrayList<Object2ObjectMap.Entry<String, String>> tasks = new ObjectArrayList<>();

        Propagation(MrjState state, MemberType type, ObjectArrayList<Object2ObjectMap.Entry<String, String>> tasks) {
            this.state = state;
            this.type = type;
            this.tasks.addAll(tasks);
        }

        @Override
        public void run() {
            ReferenceSet<ClassInstance> visitedUp = new ReferenceOpenHashSet<>();
            ReferenceSet<ClassInstance> visitedDown = new ReferenceOpenHashSet<>();

            for (int i = 0, tasksSize = tasks.size(); i < tasksSize; i++) {
                Object2ObjectMap.Entry<String, String> entry = tasks.get(i);
                String className = getClassName(entry.getKey(), type);
                ClassInstance cls = state.getClass(className);
                if (cls == null) continue; // not available for this Side

                String idSrc = stripClassName(entry.getKey(), type);
                String nameDst = entry.getValue();
                assert nameDst.indexOf('/') < 0;

                if (MemberInstance.getNameFromId(type, idSrc, ignoreFieldDesc).equals(nameDst)) {
                    continue; // no name change
                }

                MemberInstance member = resolveMissing ? cls.resolve(type, idSrc) : cls.getMember(type, idSrc);

                if (member == null) {
                    // not available for this Side
                    continue;
                }

                Propagator.propagate(member, idSrc, nameDst, visitedUp, visitedDown);
            }
        }
    }
}
