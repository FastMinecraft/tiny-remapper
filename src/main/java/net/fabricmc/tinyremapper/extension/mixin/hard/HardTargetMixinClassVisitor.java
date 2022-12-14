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

package net.fabricmc.tinyremapper.extension.mixin.hard;

import it.unimi.dsi.fastutil.objects.ObjectArrayList;
import it.unimi.dsi.fastutil.objects.ObjectLists;
import net.fabricmc.tinyremapper.extension.mixin.common.MapUtility;
import net.fabricmc.tinyremapper.extension.mixin.common.data.*;
import net.fabricmc.tinyremapper.extension.mixin.hard.annotation.ImplementsAnnotationVisitor;
import net.fabricmc.tinyremapper.extension.mixin.hard.annotation.MixinAnnotationVisitor;
import net.fabricmc.tinyremapper.extension.mixin.hard.data.SoftInterface;
import org.objectweb.asm.AnnotationVisitor;
import org.objectweb.asm.ClassVisitor;
import org.objectweb.asm.FieldVisitor;
import org.objectweb.asm.MethodVisitor;

import java.util.Collections;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Consumer;

public class HardTargetMixinClassVisitor extends ClassVisitor {
	private final ObjectArrayList<Consumer<CommonData>> tasks;
	private MxClass _class;

	// @Mixin
	private final AtomicBoolean remap = new AtomicBoolean();
	private final ObjectArrayList<String> targets = new ObjectArrayList<>();

	// @Implements
	private final ObjectArrayList<SoftInterface> interfaces = new ObjectArrayList<>();

	public HardTargetMixinClassVisitor(ObjectArrayList<Consumer<CommonData>> tasks, ClassVisitor delegate) {
		super(Constant.ASM_VERSION, delegate);
		this.tasks = Objects.requireNonNull(tasks);
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
			av = new MixinAnnotationVisitor(av, remap, targets);
		} else if (Annotation.IMPLEMENTS.equals(descriptor)) {
			av = new ImplementsAnnotationVisitor(av, interfaces);
		}

		return av;
	}

	@Override
	public FieldVisitor visitField(int access, String name, String descriptor, String signature, Object value) {
		FieldVisitor fv = super.visitField(access, name, descriptor, signature, value);
		MxMember field = _class.getField(name, descriptor);

		if (targets.isEmpty()) {
			return fv;
		} else {
			return new HardTargetMixinFieldVisitor(tasks, fv, field, remap.get(), Collections.unmodifiableList(targets));
		}
	}

	@Override
	public MethodVisitor visitMethod(int access, String name, String descriptor, String signature, String[] exceptions) {
		MethodVisitor mv = super.visitMethod(access, name, descriptor, signature, exceptions);
		MxMember method = _class.getMethod(name, descriptor);

		if (!interfaces.isEmpty() && !MapUtility.IGNORED_NAME.contains(name)) {
			ImplementsAnnotationVisitor.visitMethod(tasks, method, interfaces);
		}

		if (targets.isEmpty()) {
			return mv;
		} else {
			return new HardTargetMixinMethodVisitor(tasks, mv, method, remap.get(), ObjectLists.unmodifiable(targets));
		}
	}
}
