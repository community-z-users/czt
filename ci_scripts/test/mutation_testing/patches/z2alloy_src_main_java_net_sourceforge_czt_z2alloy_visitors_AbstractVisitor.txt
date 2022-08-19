package net.sourceforge.czt.z2alloy.visitors;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z2alloy.Z2Alloy;
import net.sourceforge.czt.z2alloy.ast.AlloyExpr;

public class AbstractVisitor {

  protected AlloyExpr visit(Term t) {
    if (t != null) {
      return t.accept(Z2Alloy.getInstance());
    }
    return null;
  }
  
}
