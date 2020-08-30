package org.example.analysis;

import fj.P;
import org.example.environment.SootEnvironment;
import org.example.structure.Relation;
import org.example.utils.FileUtil;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;
import soot.util.ArraySet;
import soot.util.Chain;

import java.util.*;

public class points_to {

    public static Map<String, Set<Relation>> allRelation = new HashMap<String, Set<Relation>>();
    public static Map<String, Map<String, List<Value>>> methodParamAndReturn = new HashMap<String, Map<String, List<Value>>>();
    public static Set<Unit> allInvocation = new HashSet<>();

    public static Map<String, Map<Value, Set<String>>> mvRelaton = new HashMap<>();
    public static Map<String, Map<SootField, Set<String>>> ofoRelation = new HashMap<>();
    Map<String,String> o2cRelation = new HashMap<>();

    //public static Map<String,SootClass> o2cRelation = new HashMap<>();
    //public static Map<String,SootClass> m2oRelation = new HashMap<>();
    //public static Map<String, Map<String, List<Value>>> mRelation = new HashMap<>();
    //public static Map<String,Set<SootField>> m2fRelation = new HashMap<>();

    public static void main(String[] args) {
        String cp = "D:\\rt.jar";
        String pp = "D:\\code";

        new points_to().analysis(cp, pp);
    }

    public void analysis(String cp, String pp) {
        SootEnvironment.init(cp, pp);
        genRelation();
        //dealInvokeStmt();
        extRelation();
        printRelation();
        printResult();
    }

    public void genRelation() {

        Map<SootMethod, Set<Unit>> invokeStmtMap = new HashMap<SootMethod, Set<Unit>>();

        Iterator<SootMethod> mIter = SootEnvironment.allMethods.iterator();
        while (mIter.hasNext()) {
            SootMethod m = mIter.next();

            Map<Value, Set<String>> vRelation = new HashMap<>();

            if (!m.isConcrete()) {//this method can not have a body
                continue;
            }

            Set<Unit> invokeSTMT = new HashSet<Unit>();
            List<Value> params = new ArrayList<Value>();
            List<Value> returns = new ArrayList<Value>();
            Map<String, List<Value>> paramAndReturn = new HashMap<String, List<Value>>();
            Set<Relation> relationSet = new HashSet<Relation>();
            Set<SootField> fields = new HashSet<>();

            JimpleBody jb = (JimpleBody) m.retrieveActiveBody();
            Iterator<Unit> uIter = jb.getUnits().iterator();
            while (uIter.hasNext()) {
                Unit u = uIter.next();
                if (u instanceof JInvokeStmt || (u instanceof JAssignStmt && ((JAssignStmt) u).getRightOp() instanceof InvokeExpr)) {
                    invokeSTMT.add(u);
                    allInvocation.add(u);
                    continue;
                }
                if (u instanceof JReturnStmt) {
                    Value returnValue = ((JReturnStmt) u).getOp();
                    if (returnValue instanceof JArrayRef) {
                        returnValue = ((JArrayRef) returnValue).getBase();
                    }
                    if (returnValue instanceof StringConstant) {

                    }
                    returns.add(returnValue);
                }
                if (u instanceof JIdentityStmt) {

                    Value left = ((JIdentityStmt) u).getLeftOp();
                    Value right = ((JIdentityStmt) u).getRightOp();

                    if (left instanceof JArrayRef) {
                        left = ((JArrayRef) left).getBase();
                    }
                    if (right instanceof JArrayRef) {
                        right = ((JArrayRef) right).getBase();
                    }

                    if (left.getType() instanceof RefType && right.getType() instanceof RefType) {
                        relationSet.add(new Relation(left, right));//产生的包含@this:类名的只想关系
                        params.add(right);
                    }

                    if (right instanceof StringConstant) {

                    }
                }
                if (u instanceof JAssignStmt) {

                    Value left = ((JAssignStmt) u).getLeftOp();
                    Value right = ((JAssignStmt) u).getRightOp();

                    if (left instanceof JArrayRef) {
                        left = ((JArrayRef) left).getBase();
                    }
                    if (right instanceof JArrayRef) {
                        right = ((JArrayRef) right).getBase();
                    }

                    if (right instanceof JNewArrayExpr) {//创建数组
                        relationSet.add(new Relation(right, left));


                    } else {
                        if ((left.getType() instanceof RefType || left.getType() instanceof ArrayType) && (right.getType() instanceof RefType || right.getType() instanceof ArrayRef)) {
                            if (left instanceof FieldRef) {
                                SootField field = ((FieldRef) left).getField();
                                if (field.isStatic()) {


                                } else {
                                    left = ((JInstanceFieldRef) left).getBase();
                                    relationSet.add(new Relation(left, field, right));
                                }
                                if (right instanceof StringConstant) {


                                }
                            } else if (right instanceof FieldRef) {
                                SootField field = ((FieldRef) right).getField();
                                relationSet.add(new Relation(left, right, field));


                            } else if (right instanceof JNewExpr) {//x = new A();
                                //Type t = right.getType();
                                int lineNUm = u.getJavaSourceStartLineNumber();
                                String o = "Object";
                                o += lineNUm;
                                Set<String> os = vRelation.get(left);
                                if(os==null){
                                    os = new HashSet<>();
                                }
                                os.add(o);
                                vRelation.put(left, os);
                                relationSet.add(new Relation(left,right));
                                o2cRelation.put(o,left.getType().toString());
                                //System.out.println(left.getType());//输出类的名称

                            } else if (left instanceof JimpleLocal) {
                                if (right instanceof JCastExpr) {
                                    right = ((JCastExpr) right).getOp();
                                }
                                relationSet.add(new Relation(left, right));
                            }
                        }
                    }

                }
            }
            paramAndReturn.put("param", params);
            paramAndReturn.put("return", returns);
            methodParamAndReturn.put(m.getSignature(), paramAndReturn);


            allRelation.put(m.getSignature(), relationSet);
            invokeStmtMap.put(m, invokeSTMT);



            mvRelaton.put(m.getSignature(), vRelation);
        }
        /*for(SootMethod method:invokeStmtMap.keySet()){
            for(Unit invoke:invokeStmtMap.get(method)){
                System.out.println(method+invoke.toString());
            }
        }*/
        dealInvokeStmt(invokeStmtMap);
    }

    public void dealInvokeStmt(Map<SootMethod,Set<Unit>> invokeMap) {
        /*for(SootMethod m:invokeMap.keySet()){
            for(Unit unit:invokeMap.get(m)){
                System.out.println(m+ unit.toString());
            }
        }*/
        Set<SootMethod> methods= invokeMap.keySet();
        for(SootMethod method:methods ){
            Map<Value,Set<String>> v2oRelation = mvRelaton.get(method);
            Set<Unit> invoke = invokeMap.get(method);
            InvokeExpr invokeExp = null;
            for(Unit u:invoke){
                if(u instanceof JInvokeStmt){
                    invokeExp = ((JInvokeStmt) u).getInvokeExpr();
                    if(invokeExp instanceof JVirtualInvokeExpr) {
                        SootMethod m = invokeExp.getMethod();
                        Map<String,List<Value>> ParamOrReturn = methodParamAndReturn.get(m);
                        List<Value> param = ParamOrReturn.get("param");
                        Iterator<Value> p = param.listIterator();
                        if(p.hasNext()) {
                            for (Value v : invokeExp.getArgs()) {
                                System.out.println(v+p.next().toString());
                            }
                        }
                    }
                }
                /*if(u instanceof JVirtualInvokeExpr){
                    System.out.println(u);
                    //System.out.println(((JVirtualInvokeExpr) u).getType());
                    System.out.println(((JVirtualInvokeExpr) u).getBase());
                    for(Value v:((JVirtualInvokeExpr) u).getArgs()){
                        //Set<String> yObjects = v2oRelation.get();
                    }
                }*/
            }
        }


        /*for(Unit invokeStmt:allInvocation){
            if(invokeStmt instanceof  JInvokeStmt) {
                InvokeExpr invokeExp = ((JInvokeStmt) invokeStmt).getInvokeExpr();
                if (invokeExp instanceof JVirtualInvokeExpr){
                    //System.out.println(invokeExp);
                }
                for(Value v:invokeExp.getArgs()){

                }
            }
        }*/
    }

    public void extRelation() {
        Chain<SootClass> clsIter = Scene.v().getApplicationClasses();
        for (SootClass cls : clsIter) {
            List<SootMethod> methods = cls.getMethods();
            for (SootMethod m : methods) {
                if (!m.isConcrete())
                    continue;
                String mSig = m.getSignature();
                Map<Value, Set<String>> v2o = mvRelaton.get(mSig);
                int i=1;//标记位，判断被修改的集合size是否发生改变
                while(i==1){
                    i=0;
                    Set<Relation> relation = allRelation.get(mSig);
                    for (Relation r : relation) {
                        int oldSize=0;
                        int newSize=0;
                        if (r.type == "v2v") {//x=y
                            Set<String> xo = v2o.get(r.left);
                            Set<String> yo = v2o.get(r.right);
                            if(yo==null)
                                continue;
                            if(xo==null){
                                //oldSize=0;
                                //xo.addAll(yo);
                                v2o.put(r.left,yo);
                                newSize = yo.size();
                            }else {
                                oldSize=xo.size();
                                xo.addAll(yo);
                                v2o.put(r.left,xo);
                                newSize=xo.size();
                            }
                        }
                        if (r.type == "load") {//x=y.f
                            Set<String> xo = v2o.get(r.left);
                            Set<String> yo = v2o.get(r.right);
                            //oldSize = xo.size();
                            if(yo==null)
                                continue;
                            Set<String> os = new HashSet();
                            for(String y : yo){
                                Map<SootField,Set<String>> fo = ofoRelation.get(yo);
                                os.addAll(fo.get(r.field));
                            }
                            if(xo==null){
                                v2o.put(r.left,os);
                                newSize = os.size();
                            }else {
                                oldSize=xo.size();
                                xo.addAll(yo);
                                newSize = xo.size();
                                v2o.put(r.left,xo);
                            }
                        }
                        if(r.type=="store"){
                            Set<String> xo = v2o.get(r.left);
                            Set<String> yo = v2o.get(r.right);
                            Set<String> os;
                            if(xo == null || yo == null)
                                continue;
                            for(String x:xo){
                                Map<SootField,Set<String>> fo = ofoRelation.get(x);
                                if(fo == null){
                                    fo = new HashMap<>();
                                    fo.put(r.field,yo);
                                    newSize += yo.size();
                                }else{
                                    os = fo.get(r.field);
                                    if(os == null){
                                        os = new HashSet();
                                        fo.put(r.field,yo);
                                        newSize += yo.size();
                                    }else{
                                        oldSize += os.size();
                                        os.addAll(yo);
                                        fo.put(r.field,os);
                                        newSize += os.size();
                                    }
                                }
                                ofoRelation.put(x,fo);
                            }
                        }
                        if(oldSize!=newSize)
                            i=1;
                        //System.out.println("oldSize是："+oldSize);
                        //System.out.println("newSize是:"+newSize);
                    }

                }
                mvRelaton.put(mSig, v2o);
            }
        }
    }

    public void printRelation() {
        Chain<SootClass> clsIter = Scene.v().getApplicationClasses();
        List<String> data2write = new ArrayList<>();
        String writeLine = null;
        for (SootClass cls : clsIter) {
            //System.out.println(cls.getName());
            List<SootMethod> methods = cls.getMethods();
            for (SootMethod m : methods) {
                if (!m.isConcrete())
                    continue;
                String mSig = m.getSignature();
                Set<Relation> relation = allRelation.get(mSig);
                //Iterator<Relation> r = relation.iterator();
                for (Relation r : relation) {
                    if (r.type == "v2v") {
                        writeLine = mSig +"::" + r.right + "->" + r.left;

                        //System.out.println(mSig + "::" + r.right + "->" + r.left);
                    }
                    if (r.type == "load") {
                        //System.out.println(mSig + "::" + r.right + "--" + r.field + "-->" + r.left);
                        writeLine = mSig + "::" + r.right + "--" + r.field.getName() + "-->" + r.left;
                        //System.out.println(mSig + "::" + r.right + "--" + r.field.getName() + "-->" + r.left);
                    }
                    if (r.type == "store") {
                        writeLine = mSig + "::" + r.right + "---->" + r.left + "." + r.field.getName();
                        //System.out.println(mSig + "::" + r.right + "---->" + r.left + "." + r.field.getName());
                    }
                    data2write.add(writeLine);
                }
            }
            //System.out.println();
            //writeLine = "\n";
            //data2write.add(writeLine);
        }
        if(!data2write.isEmpty()) {
            FileUtil.writeStaticResult(data2write, "result", "points-to-relation");
        }
    }

    public void printResult(){
        List<String> data2write = new ArrayList<>();
        String writeLine = null;
        Set<String> allMethod = mvRelaton.keySet();
        for(String m : allMethod){
            Map<Value,Set<String>> v2o = mvRelaton.get(m);
            Set<Value> allVriable = v2o.keySet();
            for(Value v: allVriable){
                Set<String> allObject = v2o.get(v);
                //System.out.println(m+v+":");
                for (String o : allObject){
                    writeLine = m+v+"::"+o;
                    data2write.add(writeLine);
                    //System.out.println(o+"\t");
                }
            }
        }
        //writeLine = "\n";
        //data2write.add(writeLine);
        System.out.println();
        Set<String> os = ofoRelation.keySet();
        for(String o:os){
            Map<SootField,Set<String>> fo =ofoRelation.get(o);
            Set<SootField> fs = fo.keySet();
            for(SootField f:fs) {
                Set<String> objects = fo.get(f);
                //System.out.println(o+f+":");
                for(String object:objects){
                    writeLine = o+f+"::"+object;
                    data2write.add(writeLine);
                    //System.out.println(object+"\t");
                }
            }
        }
        if(!data2write.isEmpty()){
            FileUtil.writeStaticResult(data2write,"result","points-to-result");
        }
    }
}
