/*
 * FlatBindingVisitor.java
 *
 * Created on 06 April 2005, 16:04
 */

package net.sourceforge.czt.animation.eval.flatpred;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface FlatBindingVisitor extends Visitor {
   
    public Object visitFlatBinding(FlatBinding term);
}
