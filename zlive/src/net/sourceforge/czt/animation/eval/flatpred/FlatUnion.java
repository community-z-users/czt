/*
 * FlatUnion.java
 *
 * Created on 05 April 2005, 18:01
 */

package net.sourceforge.czt.animation.eval.flatpred;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.RefName;

/**
 * FlatUnion(a, b, r) implements a \cup b = r
 * @author leo
 */
public class FlatUnion extends FlatPred {
    
    /** Creates a new instance of FlatUnion */
    public FlatUnion(RefName a, RefName b, RefName r) {
    }
    
    public Mode chooseMode(Envir env) {
        Mode m = modeFunction(env); 
        return m;
    }
    
    public boolean nextEvaluation() {
        return false;
    }
    
    ///////////////////////// Pred methods ///////////////////////
    
    public Object accept(Visitor visitor) {
        if (visitor instanceof FlatUnionVisitor) {
            FlatUnionVisitor v = (FlatUnionVisitor) visitor;
            return v.visitFlatUnion(this);
        }
        return super.accept(visitor);
    }
}
