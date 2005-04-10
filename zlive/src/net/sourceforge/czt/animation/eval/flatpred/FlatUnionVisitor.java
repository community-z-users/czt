/*
 * FlatUnionVisitor.java
 *
 * Created on 05 April 2005, 18:04
 */

package net.sourceforge.czt.animation.eval.flatpred;

import net.sourceforge.czt.util.Visitor;

/**
 *
 * @author leo
 */
public interface FlatUnionVisitor extends Visitor {
  /**
   * Visits a FlatUnion.
   * @param  term the FlatUnion to be visited.
   * @return some kind of <code>Object</code>.
   */
  Object visitFlatUnion(FlatUnion term);
}

