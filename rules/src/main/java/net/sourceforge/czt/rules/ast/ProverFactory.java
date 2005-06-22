/*
  Copyright (C) 2005 Mark Utting
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.rules.ast;

import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.impl.ZpattFactoryImpl;

/**
 * Makes sure that Joker are only created once.
 *
 * @author Petra Malik
 */
public class ProverFactory
  extends ZpattFactoryImpl
{
  private Map<String, ProverJokerExpr> jokerExprs_ =
    new HashMap<String, ProverJokerExpr>();
  private Map<String, ProverJokerName> jokerNames_ =
    new HashMap<String, ProverJokerName>();
  private Map<String, ProverJokerPred> jokerPreds_ =
    new HashMap<String, ProverJokerPred>();
  private int count = 0;

  /**
   * Creates a new JokerExpr having a name that has not
   * been used before.
   */
  public JokerExpr createJokerExpr()
  {
    String name;
    while ( jokerExprs_.get(name = "J" + count) != null ) count++;
    ProverJokerExpr result = new ProverJokerExpr(name);
    jokerExprs_.put(name, result);
    return result;
  }

  public JokerExpr createJokerExpr(String name)
  {
    ProverJokerExpr result = jokerExprs_.get(name);
    if (result == null) {
      result = new ProverJokerExpr(name);
      jokerExprs_.put(name, result);
    }
    return result;
  }

  /**
   * Creates a new JokerName having a name that has not
   * been used before.
   */
  public JokerName createJokerName()
  {
    String name;
    while ( jokerNames_.get(name = "J" + count) != null ) count++;
    ProverJokerName result = new ProverJokerName(name);
    jokerNames_.put(name, result);
    return result;
  }

  public JokerName createJokerName(String name)
  {
    ProverJokerName result = jokerNames_.get(name);
    if (result == null) {
      result = new ProverJokerName(name);
      jokerNames_.put(name, result);
    }
    return result;
  }

  public JokerPred createJokerPred()
  {
    String name;
    while ( jokerPreds_.get(name = "J" + count) != null ) count++;
    ProverJokerPred result = new ProverJokerPred(name);
    jokerPreds_.put(name, result);
    return result;
  }

  public JokerPred createJokerPred(String name)
  {
    ProverJokerPred result = jokerPreds_.get(name);
    if (result == null) {
      result = new ProverJokerPred(name);
      jokerPreds_.put(name, result);
    }
    return result;
  }

  public JokerExprBinding createJokerExprBinding()
  {
    String message =
      "The JokerExpr for the new JokerExprBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerExprBinding createJokerExprBinding(JokerExpr jokerExpr,
                                                 Expr expr)
  {
    ProverJokerExpr joker = jokerExprs_.get(jokerExpr.getName());
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + jokerExpr);
    }
    return joker.getBinding();
  }

  public JokerNameBinding createJokerNameBinding()
  {
    String message =
      "The JokerName for the new JokerNameBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerNameBinding createJokerNameBinding(JokerName jokerName,
                                                 DeclName name)
  {
    ProverJokerName joker = jokerNames_.get(jokerName.getName());
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + jokerName);
    }
    return joker.getBinding();
  }

  public JokerPredBinding createJokerPredBinding()
  {
    String message =
      "The JokerPred for the new JokerPredBinding must be given";
    throw new UnsupportedOperationException(message);
  }

  public JokerPredBinding createJokerPredBinding(JokerPred jokerPred,
                                                 Pred pred)
  {
    ProverJokerPred joker = jokerPreds_.get(jokerPred.getName());
    if (joker == null) {
      throw new IllegalArgumentException("Unknown joker " + jokerPred);
    }
    return joker.getBinding();
  }

  public LookupConstDeclProviso
    createLookupConstDeclProviso(SequentContext sequentContext,
                                 Expr leftExpr,
                                 Expr rightExpr)
    {
      LookupConstDeclProviso proviso = new ProverLookupConstDeclProviso();
      proviso.setSequentContext(sequentContext);
      proviso.setLeftExpr(leftExpr);
      proviso.setRightExpr(rightExpr);
      return proviso;
    }
}
