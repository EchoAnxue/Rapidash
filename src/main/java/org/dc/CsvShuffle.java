package org.dc;

import java.io.*;
import java.nio.file.*;
import java.util.*;

public class CsvShuffle {

    public static void main(String[] args) throws IOException {

        String inputPath = "D:/big_file_temporary/data/flights_Encoded.csv";
        List<String> lines = Files.readAllLines(Paths.get(inputPath));

        if (lines.isEmpty()) {
            System.out.println("文件为空");
            return;
        }

        // 假设第一行是表头
        String header = lines.get(0);
        List<String> data = new ArrayList<>(lines.subList(1, lines.size()));

        for (int round = 1; round <= 3; round++) {

            // 构造索引
            List<Integer> indices = new ArrayList<>();
            for (int i = 0; i < data.size(); i++) {
                indices.add(i);
            }

            // 打乱索引
            Collections.shuffle(indices);

            // 生成新文件名
            String outputPath = inputPath.replace(".csv", "_rd" + round + ".csv");

            try (BufferedWriter writer = Files.newBufferedWriter(Paths.get(outputPath))) {

                // 写入表头
                writer.write(header);
                writer.newLine();

                // 按打乱顺序写数据
                for (int index : indices) {
                    writer.write(data.get(index));
                    writer.newLine();
                }
            }

            System.out.println("生成文件: " + outputPath);
        }
    }
}
