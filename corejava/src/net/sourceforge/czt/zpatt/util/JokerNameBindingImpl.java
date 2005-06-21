package net.sourceforge.czt.zpatt.util;

import java.util.*;
import java.util.logging.*;

import net.sourceforge.czt.base.impl.*;
import net.sourceforge.czt.util.TypesafeList;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * An implementation of the interface {@link JokerNameBinding}.
 *
 * @author Petra Malik
 */
public class JokerNameBindingImpl
  extends  net.sourceforge.czt.zpatt.impl.JokerNameBindingImpl
{
  protected JokerNameBindingImpl(JokerName jokerName)
  {
    super.setJokerName(jokerName);
  }

  public net.sourceforge.czt.base.ast.Term create(Object[] args)
  {
    throw new UnsupportedOperationException();
  }

  public void setJokerName(JokerName joker)
  {
    throw new UnsupportedOperationException();
  }
}
