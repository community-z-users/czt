package net.sourceforge.czt.zpatt.util;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * An implementation of the interface
 * {@link JokerExprBinding}.
 *
 * @author Gnast version 0.1
 */
public class JokerExprBindingImpl
  extends  net.sourceforge.czt.zpatt.impl.JokerExprBindingImpl
{
  protected JokerExprBindingImpl(JokerExpr jokerExpr)
  {
    super.setJokerExpr(jokerExpr);
  }

  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }

  public void setJokerExpr(JokerExpr joker)
  {
    throw new UnsupportedOperationException();
  }
}
