package org.example.structure;


import soot.SootField;
import soot.Value;

public class Relation {

    public Value left;
    public Value right;
    public SootField field;
    public String type;
    public String o;

    public Relation (Value left,Value right){
        this.type = "v2v";
        this.left = left;
        this.right = right;
    }
    public Relation (Value left,SootField field,Value right){
        this.type = "store";
        this.left = left;
        this.right = right;
        this.field = field;
    }
    public Relation (Value left,Value right,SootField field){
        this.type = "load";
        this.left = left;
        this.right = right;
        this.field = field;
    }
    public Relation (Value param,String o){
        this.type = "new";
        this.o = o;
        this.left = param;
    }
}
