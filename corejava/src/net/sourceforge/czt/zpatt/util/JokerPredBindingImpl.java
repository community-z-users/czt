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
 * {@link JokerPredBinding}.
 *
 * @author Gnast version 0.1
 */
public class JokerPredBindingImpl
  extends  net.sourceforge.czt.zpatt.impl.JokerPredBindingImpl
{
  protected JokerPredBindingImpl(JokerPred jokerPred)
  {
    super.setJokerPred(jokerPred);
  }

  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }

  public void setJokerPred(JokerPred joker)
  {
    throw new UnsupportedOperationException();
  }
}
