package org.example.environment;
//import com.tfa.structs.CG;
import org.example.utils.FileUtil;
import soot.*;
import soot.jimple.JimpleBody;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.options.Options;
import soot.tagkit.LineNumberTag;

import java.io.*;
import java.util.*;

public class SootEnvironment {

    public static String mainSig = "void main(java.lang.String[])";

    public static Set<SootClass> allClasses;
    public static Set<SootClass> extraClasses;
    public static Map<String, Map<String, Map<Integer, Value>>> locals;
    public static Map<String, Map<String, Map<Integer, Unit>>> units;
    public static Set<SootField> allFields;
    public static Set<SootMethod> allMethods;

    //public static CG cg;


    public static void init(String cp, String pp) {
//        pp = "/home/sean/doop-benchmarks/dacapo-2006/antlr.jar";
        Options.v().set_keep_line_number(true);
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_keep_offset(false);
//        Options.v().setPhaseOption("cg.spark", "vta:true");
//        Options.v().setPhaseOption("cg", "library:anysubtype");
        Scene.v().setSootClassPath(cp + File.pathSeparator + pp);
        List<String> processDir = new ArrayList<String>();
        processDir.add(pp);
        Options.v().set_process_dir(processDir);
//        load(appclass);
//        loadClasses(pp, "class");
        Scene.v().loadNecessaryClasses();
        List<String> pkgList = new ArrayList<>();
//        pkgList.add("cg.cha");
//        Scene.v().setPkgList(pkgList);
        allClasses = new HashSet<SootClass>();
        allClasses.addAll(Scene.v().getApplicationClasses());
        initialStruct();
    }

    public static void loadClasses(String dir, String extension) {
        allClasses = new HashSet<SootClass>();
        if(dir.endsWith(File.separator)) {
            dir = dir.substring(0, dir.length()-1);
        }
        if(extension.startsWith(".")) {
            extension = extension.substring(1);
        }
        List<String> filelist = FileUtil.getFiles(dir, extension);
        for(String filepath : filelist) {
            String className = filepath.substring(dir.length() + 1, filepath.indexOf(extension) - 1).replace(File.separator, ".");
            SootClass c = Scene.v().loadClassAndSupport(className);
            c.setApplicationClass();
            allClasses.add(c);
        }
        Scene.v().loadNecessaryClasses();
    }

    public static void load(String classlistFile) {
        allClasses = new HashSet<SootClass>();
        try {
            BufferedReader br = new BufferedReader(new FileReader(classlistFile));
            String line;
            while((line = br.readLine()) != null) {
                SootClass c = Scene.v().loadClassAndSupport(line);
                c.setApplicationClass();
                allClasses.add(c);
            }
        } catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

        Scene.v().loadNecessaryClasses();
    }

    public static SootClass loadExtraClass(String className) {
        SootClass c = Scene.v().loadClassAndSupport(className);
        if(extraClasses == null) {
            extraClasses = new HashSet<>();
        }
        extraClasses.add(c);
        return c;
    }

    private static void initialStruct() {
        allMethods = new HashSet<SootMethod>();
        allFields = new HashSet<SootField>();
        units = new HashMap<String, Map<String, Map<Integer, Unit>>>();
        locals = new HashMap<String, Map<String, Map<Integer, Value>>>();
        List<SootMethod> entryPoints = new ArrayList<SootMethod>();

        Collection classes = soot.Scene.v().getApplicationClasses();
        Iterator cIter = classes.iterator();
        while(cIter.hasNext()) {
            Map<String, Map<Integer, Value>> methodMap = new HashMap<String, Map<Integer, Value>>();
            SootClass c = (SootClass) cIter.next();
            String className = c.getName();
            List<SootMethod> methods = c.getMethods();
            allMethods.addAll(methods);
            allFields.addAll(c.getFields());
            Iterator mIter = methods.iterator();
            while(mIter.hasNext()) {
                SootMethod m = (SootMethod) mIter.next();
                String methodName = m.getSignature();
                Map<Integer, Value> line2ValueMap = new HashMap<Integer, Value>();
                if(m.isConcrete()) {
                    int paramCount = 0;
                    JimpleBody jb = (JimpleBody) m.retrieveActiveBody();
                    Iterator uIter = jb.getUnits().iterator();
                    while(uIter.hasNext()) {
                        Stmt s = (Stmt) uIter.next();
                        int lineNum = getLineNum(s);
                        if(lineNum == -1) {
                            lineNum = paramCount--;
                        }
                        Iterator bIter = s.getDefBoxes().iterator();
                        while(bIter.hasNext()) {
                            ValueBox vb = (ValueBox) bIter.next();
                            Value v = vb.getValue();
                            if(v instanceof Local) {
                                line2ValueMap.put(lineNum, v);
                            }
                        }
                    }
                }
                methodMap.put(methodName, line2ValueMap);
                if(m.getSubSignature().equals(SootEnvironment.mainSig)) {
                    entryPoints.add(m);
                }
            }
            locals.put(className, methodMap);
        }
        Scene.v().setEntryPoints(entryPoints);
    }

    private static int getLineNum(Stmt s) {
        Iterator iter = s.getTags().iterator();
        while(iter.hasNext()) {
            Object o = iter.next();
            if(o instanceof LineNumberTag) {
                return Integer.parseInt(o.toString());
            }
        }
        return -1;
    }

    public static void travelStruct() {
        for(SootMethod m: allMethods) {
            if(m.isConcrete()) {
                for (Unit u : m.retrieveActiveBody().getUnits()) {
                    if (u instanceof JAssignStmt) {
                        //
                    }
                }
            }
        }
    }
}
