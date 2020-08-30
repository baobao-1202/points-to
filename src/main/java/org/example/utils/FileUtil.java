package org.example.utils;

import org.apache.commons.io.FileUtils;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

public class FileUtil {

    public static Set<String> resultSet = new HashSet<>(1000);

    public static List<String> getFiles(String dir, String extension) {
        Iterator<File> files = FileUtils.iterateFiles(new File(dir), new String[]{extension}, true);
        List<String> filelist = new ArrayList<String>();
        while (files.hasNext()) {
            File file = files.next();
            String filePath = file.getAbsolutePath();
            filelist.add(filePath);
        }
        return filelist;
    }

    public static void writeLog(String[] log, String folder, String filename) {
        filename = folder + File.separator + filename;
        File folderF = new File(folder);
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, true);
            for (String s : log) {
                if(isWritable(s)) {
                    fw.write(s);
                    fw.write("\r\n");
                }
            }
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void writeResult(String dataOutput, String filename) {
        if(!isWritable(dataOutput)) {
            return;
        }
        filename = "dynamic" + File.separator + filename;
        File folderF = new File("dynamic");
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, false);

//            if(dataOutput == null) {
//                dataOutput = "";
//            }
            fw.write(dataOutput);
            fw.write("\r\n");
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void writeResult(String[] dataOutput, String folder, String filename) {
        filename = folder + File.separator + filename;
        File folderF = new File(folder);
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, false);
            for (String s : dataOutput) {
                if(isWritable(s)) {
                    fw.write(s);
                    fw.write("\r\n");
                }
            }
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void writeResult(List<String> dataOutput, String filename) {
        filename = "dynamic" + File.separator + filename;
        File folderF = new File("dynamic");
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, true);
            for (String s : dataOutput) {
                if(isWritable(s)) {
                    fw.write(s);
                    fw.write("\r\n");
                }
            }
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void writeStaticResult(List<String> dataOutput, String folder, String filename) {
        filename = folder + File.separator + filename;
        File folderF = new File(folder);
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, false);
            for (String s : dataOutput) {
                if(isWritable(s)) {
                    fw.write(s);
                    fw.write("\r\n");
                }
            }
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    public static void writeMap(Map<Integer, String> map, String folder, String filename) {
        filename = folder + File.separator + filename;
        File folderF = new File(folder);
        File file = new File(filename);
        FileWriter fw = null;
        try {
            if(!folderF.exists()) {
                folderF.mkdir();
            }
            if (!file.exists()) {
                file.createNewFile();
            }
            fw = new FileWriter(file, false);
            for(Integer key: map.keySet()) {
                fw.write(key + "::" + map.get(key));
                fw.write("\r\n");
            }
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    private static boolean isWritable(String dataOutput) {
        return dataOutput != null && resultSet.add(dataOutput);
    }
}
