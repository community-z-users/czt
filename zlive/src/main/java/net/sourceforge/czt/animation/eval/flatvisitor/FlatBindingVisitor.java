/*
 * FlatBindingVisitor.java
 *
 * Created on 06 April 2005, 16:04
 */

package net.sourceforge.czt.animation.eval.flatvisitor;

import net.sourceforge.czt.animation.eval.flatpred.FlatBinding;
import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface FlatBindingVisitor<R> extends Visitor<R> {
   
    public R visitFlatBinding(FlatBinding term);
}
