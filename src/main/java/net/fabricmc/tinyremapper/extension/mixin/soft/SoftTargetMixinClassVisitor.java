/*
 * Copyright (c) 2016, 2018, Player, asie
 * Copyright (c) 2021, FabricMC
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

package net.fabricmc.tinyremapper.extension.mixin.soft;

import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectLists;
import net.fabricmc.tinyremapper.extension.mixin.common.data.*;
import net.fabricmc.tinyremapper.extension.mixin.soft.annotation.MixinAnnotationVisitor;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.MethodVisitor;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

public class SoftTargetMixinClassVisitor extends ClassVisitor {
    private final CommonData data;
    // @Mixin
    private final AtomicBoolean remap = new AtomicBoolean();
    private final ObjectArrayList<String> targets = new ObjectArrayList<>();
    private MxClass _class;

    public SoftTargetMixinClassVisitor(CommonData data, ClassVisitor delegate) {
        super(Constant.ASM_VERSION, delegate);
        this.data = Objects.requireNonNull(data);
    }

    /**
     * This is called before visitAnnotation.
     */
    @Override
    public void visit(int version, int access, String name, String signature, String superName, String[] interfaces) {
        this._class = new MxClass(name);
        super.visit(version, access, name, signature, superName, interfaces);
    }

    /**
     * This is called before visitMethod & visitField.
     */
    @Override
    public AnnotationVisitor visitAnnotation(String descriptor, boolean visible) {
        AnnotationVisitor av = super.visitAnnotation(descriptor, visible);

        if (Annotation.MIXIN.equals(descriptor)) {
            av = new MixinAnnotationVisitor(data, av, remap, targets);
        }

        return av;
    }

    @Override
    public MethodVisitor visitMethod(
        int access,
        String name,
        String descriptor,
        String signature,
        String[] exceptions
    ) {
        MethodVisitor mv = super.visitMethod(access, name, descriptor, signature, exceptions);
        MxMember method = _class.getMethod(name, descriptor);

        if (targets.isEmpty()) {
            return mv;
        } else {
            return new SoftTargetMixinMethodVisitor(data, mv, method, remap.get(), ObjectLists.unmodifiable(targets));
        }
    }
}
