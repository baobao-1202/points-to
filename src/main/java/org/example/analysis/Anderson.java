package org.example.analysis;

import jas.Var;
import org.example.environment.SootEnvironment;
import org.example.structure.Relation;
import org.example.utils.FileUtil;
import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;
import soot.jimple.spark.ondemand.pautil.SootUtil;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Filter;
import soot.toDex.SootToDexUtils;

import java.util.*;

public class Anderson {
    public static Map<SootMethod,Map<String, List<Value>>> AllParAndReturn = new HashMap<>();//String:"param"or"return";
    public static Map<SootMethod,Value> ThisVar = new HashMap<>();
    public static Map<String, Type> HeapType = new HashMap<>();//String:object+num;
    //public static Map<SootMethod,Map<Unit,SootMethod>> GlobalCallGraph = new HashMap<>();
    public static Map<SootMethod,Set<Unit>> GlobalInvoke = new HashMap<>();
    public static Set<Relation> Relations = new HashSet<>();
    //public static Map<Unit,Set<SootMethod>> CallGraph = new HashMap<>();

    public static Map<String,Map<SootField,Set<String>>> FieldPointsTo = new HashMap<>();//String:object+num;
    public static Map<String,Set<String>> VarPointsTo = new HashMap<>();//firstString:m.getSignature+v.toString;nextString:object+num;

    public static void main(String[] args){
        String cp = "D:\\rt.jar";
        String pp = "D:\\code";
        new Anderson().analysis(cp, pp);
    }

    public void analysis(String cp, String pp) {
        SootEnvironment.init(cp, pp);
        genRelation();
        findFixedPoint();
        //dealInvoke();
        //extRelation();
        printRelation();
        printResult();
    }

    public static void genRelation(){
        int num = 0;
        Iterator<SootMethod> mIter = SootEnvironment.allMethods.iterator();
        while(mIter.hasNext()){
            SootMethod method = mIter.next();
            String mSig = method.getSignature();
            List<Value> Param = new ArrayList<>();
            List<Value> Return = new ArrayList<>();
            Map<String,List<Value>> ParaAndReturn = new HashMap<>();
            Set<Unit> Invokes = new HashSet<>();
            if(!method.isConcrete()){
                continue;
            }
            JimpleBody jb = (JimpleBody)method.retrieveActiveBody();
            Iterator<Unit> uIter = jb.getUnits().iterator();
            while(uIter.hasNext()){
                Unit u = uIter.next();
                if(u instanceof JInvokeStmt || u instanceof JAssignStmt && ((JAssignStmt)u).getRightOp() instanceof InvokeExpr){
                    Invokes.add(u);
                }else if(u instanceof JReturnStmt){
                    Value v = ((JReturnStmt) u).getOp();
                    if(v instanceof JArrayRef){
                        v = ((JArrayRef)v).getBase();
                    }
                    if(v instanceof StringConstant){

                    }
                    Return.add(v);
                }else if(u instanceof JIdentityStmt){
                    Value left = ((JIdentityStmt)u).getLeftOp();
                    Value right = ((JIdentityStmt)u).getRightOp();
                    if(left instanceof JArrayRef){
                        left = ((JArrayRef)left).getBase();
                    }
                    if(right instanceof JArrayRef){
                        right = ((JArrayRef)right).getBase();
                    }
                    if(left.getType() instanceof RefType && right.getType() instanceof RefType){
                        String l = left.toString();
                        String r = right.toString();
                        Relations.add(new Relation(mSig+l,mSig+r));//<Container:void setItem(Item)>@this:Container-><Container:void setItem(Item)>r0
                        Param.add(right);
                    }
                    if(right instanceof StringConstant){

                    }
                }else if(u instanceof JAssignStmt){
                    Value left = ((JAssignStmt)u).getLeftOp();
                    Value right = ((JAssignStmt)u).getRightOp();
                    if(left instanceof JArrayRef){
                        left = ((JArrayRef)left).getBase();
                    }
                    if(right instanceof JArrayRef){
                        right = ((JArrayRef)right).getBase();
                    }
                    if(right instanceof JNewArrayExpr){
                        String l = left.toString();
                        String r = right.toString();
                        //Relations.add(new Relation(mSig+l,mSig+r));
                    }else{
                        if((left.getType() instanceof RefType || left.getType() instanceof ArrayType)&&(left.getType() instanceof ArrayType || right.getType() instanceof RefType)){
                            if(right instanceof JNewExpr){
                                String o = "object";
                                o += num++;
                                HeapType.put(o,right.getType());
                                Set<String> os = VarPointsTo.get(left);
                                if(os==null)
                                    os = new HashSet<>();
                                os.add(o);
                                VarPointsTo.put(mSig+left.toString(),os);
                                Relations.add(new Relation(mSig+left.toString(),mSig+right.toString()));
                            }
                            else if(right instanceof FieldRef){
                                SootField f = ((FieldRef)right).getField();
                                Relations.add(new Relation(mSig+left.toString(),mSig+right.toString(),f));//load
                            }
                            else if(left instanceof FieldRef){
                                SootField f = ((FieldRef)left).getField();
                                if(f.isStatic()){

                                }else{
                                    left = ((JInstanceFieldRef)left).getBase();
                                    Relations.add(new Relation(mSig+left.toString(),f,mSig+right.toString()));//store
                                }
                                if(right instanceof StringConstant){

                                }
                            }
                            else if(left instanceof JimpleLocal){
                                if(right instanceof JCastExpr)
                                    right = ((JCastExpr)right).getOp();
                                Relations.add(new Relation(mSig+left.toString(),mSig+right.toString()));
                            }
                        }
                    }
                }
            }
            Value v = Param.get(0);
            ThisVar.put(method,v);
            Param.remove(0);
            ParaAndReturn.put("param",Param);
            ParaAndReturn.put("return",Return);
            AllParAndReturn.put(method,ParaAndReturn);
            GlobalInvoke.put(method,Invokes);
        }
    }

/*    public static void dealInvoke(){
        Set<SootMethod> Methods = GlobalInvoke.keySet();
        for(SootMethod method:Methods){
            Set<Unit> Invokes = GlobalInvoke.get(method);
            String mSig = method.getSignature();
            for(Unit invoke:Invokes){
                if(invoke instanceof JAssignStmt){
                    Value left = ((JAssignStmt) invoke).getLeftOp();
                    Value right = ((JAssignStmt) invoke).getRightOp();
                    if(!((right) instanceof JVirtualInvokeExpr)){
                        continue;
                    }
                    SootMethod invokedM =  ((InvokeExpr)right).getMethod();
                    List<Value> formalParam = AllParAndReturn.get(invokedM).get("param");
                    List<Value> actualParam = ((InvokeExpr)right).getArgs();
                    Iterator<Value> formal = formalParam.iterator();
                    Iterator<Value> actual = actualParam.iterator();
                    while(formal.hasNext() && actual.hasNext()){
                        Value f = formal.next();
                        Value a = actual.next();
                        Relations.add(new Relation(invokedM.getSignature()+a.toString(),mSig+f.toString()));
                    }
                    Value v = ThisVar.get(invokedM);
                    Relations.add(new Relation(mSig+right.toString(),invokedM.getSignature()+v.toString()));
                    List<Value> returns = AllParAndReturn.get(invokedM).get("return");
                    for(Value ret:returns){
                        String retString = ret.toString();
                        Relations.add(new Relation(invokedM.getSignature()+retString,mSig+left.toString()));
                    }
                }else if(invoke instanceof JInvokeStmt){
                    InvokeExpr invokeExpr = ((JInvokeStmt) invoke).getInvokeExpr();
                    if(!(invokeExpr instanceof JVirtualInvokeExpr)){
                        continue;
                    }
                    SootMethod invokedM = invokeExpr.getMethod();

                    Value value = ((JVirtualInvokeExpr) invokeExpr).getBase();
                    Value v = ThisVar.get(invokedM);
                    Relations.add(new Relation(mSig+value.toString(),invokedM+v.toString()));
                    //Set<String> valueObjects = VarPointsTo.get(mSig+valueString);
                    List<Value> formalParam = AllParAndReturn.get(invokedM).get("param");
                    List<Value> actualParam = invokeExpr.getArgs();
                    Iterator<Value> formal = formalParam.iterator();
                    Iterator<Value> actual = actualParam.iterator();
                    while(formal.hasNext() && actual.hasNext()){
                        Value f = formal.next();
                        Value a = actual.next();
                        Relations.add(new Relation(invokedM.getSignature()+a.toString(),mSig+f.toString()));
                    }
                }
            }
        }
    }*/

    public static boolean dealInvoke(){
        Set<SootMethod> methods = GlobalInvoke.keySet();
        boolean change = false;
        for(SootMethod method:methods){
            Set<Unit> invokes = GlobalInvoke.get(method);
            for(Unit invoke:invokes){
                Value receiver = null;
                InvokeExpr invokeExpr = null;
                if(invoke instanceof JAssignStmt) {
                    receiver = ((JAssignStmt) invoke).getLeftOp();
                    invokeExpr = (InvokeExpr) ((JAssignStmt) invoke).getRightOp();
                }else if(invoke instanceof JInvokeStmt){
                    invokeExpr = ((JInvokeStmt) invoke).getInvokeExpr();
                }
                Value caller = null;
                String callerSub = null;
                if(invokeExpr instanceof JVirtualInvokeExpr){
                    caller = ((JVirtualInvokeExpr) invokeExpr).getBase();
                    callerSub = invokeExpr.getMethod().getSubSignature();
                    Set<String> heaps = VarPointsTo.get(method.getSignature()+caller.toString());
                    if(heaps == null){
                        continue;
                    }
                    for(String heap:heaps){
                        Type type = HeapType.get(heap);
                        SootClass c = ((RefType)type).getSootClass();
                        SootMethod m = c.getMethod(callerSub);
                        List<Value> params = AllParAndReturn.get(m).get("param");
                        List<Value> ret = AllParAndReturn.get(m).get("return");
                        List<Value> args = invokeExpr.getArgs();
                        Value vThis = ThisVar.get(m);
                        if(receiver!=null){
                            for(Value r:ret){
                                Relations.add(new Relation(m.getSignature()+r.toString(),method.getSignature()+receiver.toString()));
                            }
                        }
                        int oldSize=0;
                        Set<String> os = VarPointsTo.get(m.getSignature()+vThis.toString());
                        if(os==null){
                            os = new HashSet<>();
                        }
                        oldSize = os.size();
                        os.add(heap);
                        int newSize = os.size();
                        if(oldSize!=newSize){
                            change = true;
                        }
                        VarPointsTo.put(m.getSignature()+vThis.toString(),os);
                        Iterator<Value> param = params.iterator();
                        Iterator<Value> arg = args.iterator();
                        while(param.hasNext()&&arg.hasNext()){
                            Value p = param.next();
                            Value a = arg.next();
                            Relations.add(new Relation(method.getSignature()+a.toString(),m.getSignature()+p.toString()));
                        }
                    }
                }

/*                else{
                    InvokeExpr invokeExpr = ((JInvokeStmt)invoke).getInvokeExpr();
                    if(!(invokeExpr instanceof JVirtualInvokeExpr)){
                        continue;
                    }
                    System.out.println("invoke::"+invoke);//virtualinvoke r3.<Container:void setItem(Item)>(r4)
                    //System.out.println("invokeExpr::"+invokeExpr);
                    System.out.println(invokeExpr.getMethodRef());//<Container:void setItem(Item)>
                    System.out.println(invoke.getTags());//get line number
                    Value base = ((JVirtualInvokeExpr) invokeExpr).getBase();//r3
                    Set<String> objects = VarPointsTo.get(method.getSignature()+base);
                    System.out.println("invokeExpr.getMethod::"+invokeExpr.getMethod());//<Container:void setItem(Item)>
                    //System.out.println("invoke.getClass::"+invoke.getClass());
                    System.out.println("base.getType::"+base.getType());//Container
                    System.out.println(invokeExpr.getMethod().getName());//setItem
                    System.out.println(((JVirtualInvokeExpr) invokeExpr).getBaseBox());//JimpleLocalBox(r1)
                    System.out.println(invoke.getClass());//class soot.jimple.internal.JInvokeStmt
                    System.out.println(invoke.getBoxesPointingToThis());//[]
                    System.out.println(invokeExpr.getClass());//class soot.jimple.internal.JVirtualInvokeExpr
                    System.out.println(invokeExpr.getMethodRef().getSubSignature());//void setItem(Item)

                    if(objects == null){
                        continue;
                    }
                    for(String object:objects){
                        Type type = HeapType.get(object);
                        SootClass toClass = Scene.v().getSootClass(type.toString());
                    }

                }*/
            }
        }
        return change;
    }

    public static void extRelation() {
        int i=1;
        while(i==1) {
            i=0;
            for (Relation r : Relations) {
                int oldSize = 0;
                int newSize = 0;
                if (r.type == "v2v") {//x=y
                    Set<String> xo = VarPointsTo.get(r.left);
                    Set<String> yo = VarPointsTo.get(r.right);
                    if (yo == null)
                        continue;
                    if (xo == null)
                        xo = new HashSet<>();
                    oldSize = xo.size();
                    xo.addAll(yo);
                    newSize = xo.size();
                    VarPointsTo.put(r.left, xo);
                }
                if (r.type == "load") {//x=y.f
                    Set<String> xo = VarPointsTo.get(r.left);
                    Set<String> yo = VarPointsTo.get(r.right);
                    if (yo == null)
                        continue;
                    if (xo == null)
                        xo = new HashSet<>();
                    Set<String> os = new HashSet();
                    for (String y : yo) {
                        Map<SootField, Set<String>> fo = FieldPointsTo.get(y);
                        os.addAll(fo.get(r.field));
                    }
                    oldSize = xo.size();
                    xo.addAll(os);
                    newSize = xo.size();
                    VarPointsTo.put(r.left, xo);
                }
                if (r.type == "store") {
                    Set<String> xo = VarPointsTo.get(r.left);
                    Set<String> yo = VarPointsTo.get(r.right);
                    if (xo == null || yo == null)
                        continue;
                    Set<String> os;
                    for (String x : xo) {
                        Map<SootField, Set<String>> fo = FieldPointsTo.get(x);
                        if(fo == null)
                            fo = new HashMap<>();
                        os = fo.get(r.field);
                        if(os == null)
                            os = new HashSet<>();
                        oldSize+=os.size();
                        os.addAll(yo);
                        newSize+=os.size();
                        fo.put(r.field,os);
                        FieldPointsTo.put(x, fo);
                    }
                }
                if(oldSize!=newSize)
                    i=1;
            }
        }
    }

    public static void findFixedPoint(){
        dealInvoke();
        do{
            extRelation();
        }while(dealInvoke());
    }

    public void printRelation() {

        List<String> data2write = new ArrayList<>();
        String writeLine = null;

        for (Relation r : Relations) {
            if (r.type == "v2v") {
                writeLine = r.right + "->" + r.left;
            }
            if (r.type == "load") {
                writeLine = r.right + "--" + r.field.getName()+ "-->" + r.left;
            }
            if (r.type == "store") {
                writeLine = r.right + "---->" + r.left + "." + r.field.getName();
            }
            data2write.add(writeLine);
        }
        if(!data2write.isEmpty()) {
            FileUtil.writeStaticResult(data2write, "result", "Anderson-relation");
        }
    }

    public void printResult(){
        List<String> data2write = new ArrayList<>();
        String writeLine = null;
        Set<String> vars = VarPointsTo.keySet();
        for(String v:vars){
            for(String o:VarPointsTo.get(v)){
                writeLine = v+"::"+o;
                data2write.add(writeLine);
            }
        }
        Set<String> os = FieldPointsTo.keySet();
        for(String o:os){
            Map<SootField,Set<String>> fo =FieldPointsTo.get(o);
            Set<SootField> fs = fo.keySet();
            for(SootField f:fs) {
                Set<String> objects = fo.get(f);
                for(String object:objects){
                    writeLine = o+f+"::"+object;
                    data2write.add(writeLine);
                }
            }
        }
        if(!data2write.isEmpty()){
            FileUtil.writeStaticResult(data2write,"result","Anderson-result");
        }
    }
}
