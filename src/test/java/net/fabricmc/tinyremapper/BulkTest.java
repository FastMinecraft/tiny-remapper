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

package net.fabricmc.tinyremapper;

import it.unimi.dsi.fastutil.objects.Object2ObjectMap;
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap;
import it.unimi.dsi.fastutil.objects.ObjectIterator;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.GZIPInputStream;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

public class BulkTest {
	@Test
	public void fabricApi() throws IOException {
		TinyRemapper remapper;

		try (BufferedReader reader = getMappingReader()) {
			remapper = TinyRemapper.newRemapper()
					.withMappings(TinyUtils.createTinyMappingProvider(reader, "intermediary", "named"))
					.build();

			Object2ObjectOpenHashMap<Path, InputTag> files = new Object2ObjectOpenHashMap<>();

			try (ZipInputStream zis = new ZipInputStream(getInputStream("integration/bulk/fabric-api-0.35.1+1.17.jar"))) {
				ZipEntry entry;

				while ((entry = zis.getNextEntry()) != null) {
					if (!entry.isDirectory() && entry.getName().endsWith(".jar")) {
						String name = entry.getName();
						name = name.substring(name.lastIndexOf('/') + 1);

						Path file = tmpDir.resolve(name);
						Files.copy(zis, file);
						files.put(file, remapper.createInputTag());
					}
				}
			}

			ObjectIterator<Object2ObjectMap.Entry<Path, InputTag>> iter1 = files.object2ObjectEntrySet().fastIterator();
			while (iter1.hasNext()) {
				Object2ObjectMap.Entry<Path, InputTag> entry = iter1.next();
				remapper.readInputsAsync(entry.getValue(), entry.getKey());
			}

			//remapper.readClassPathAsync(Paths.get("/home/m/.gradle/caches/fabric-loom/minecraft-1.17-intermediary-net.fabricmc.yarn-1.17+build.6-v2.jar"));

			ObjectIterator<Object2ObjectMap.Entry<Path, InputTag>> iter2 = files.object2ObjectEntrySet().fastIterator();
			while (iter2.hasNext()) {
				Object2ObjectMap.Entry<Path, InputTag> entry = iter2.next();
				Path file = entry.getKey();

				try (OutputConsumerPath consumer = new OutputConsumerPath.Builder(tmpDir.resolve(file.getFileName().toString().replace(
					".jar",
					"-out.jar"
				))).build()) {
					remapper.apply(consumer, entry.getValue());
				}
			}
		}
	}

	private static BufferedReader getMappingReader() throws IOException {
		InputStream is = getInputStream("mapping/yarn-1.17+build.9-v2.tiny.gz");

		return new BufferedReader(new InputStreamReader(new GZIPInputStream(is), StandardCharsets.UTF_8));
	}

	private static InputStream getInputStream(String file) {
		return BulkTest.class.getClassLoader().getResourceAsStream(file);
	}

	@TempDir
	static Path tmpDir;
}
