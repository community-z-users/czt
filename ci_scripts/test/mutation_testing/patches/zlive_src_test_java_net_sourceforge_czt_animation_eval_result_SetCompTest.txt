/**
Copyright (C) 2007 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.animation.eval.result;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.animation.eval.flatpred.Bounds;
import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZName;

/**
 * Unit tests for SetComp.
 *
 * @author Mark Utting
 */
public class SetCompTest extends ZTestCase
{
  /** Set up {x:nat | x<y @ (x,x*2)} */
  public SetComp makeSet(BigInteger big)
  {
    Envir env0 = new Envir().plus(y, factory_.createNumExpr(big));
    Bounds bnds = new Bounds(null);
    SetCompExpr e = (SetCompExpr) parseExpr("\\{x:\\nat | x<y @ (x,x*2)\\}");
    FlatPredList predsAll = new FlatPredList(zlive_);
    predsAll.addExistsSchText(e.getZSchText());
    ZName resultName = predsAll.addExpr(e.getExpr());
    predsAll.inferBoundsFixPoint(bnds);
    return new SetComp(predsAll, resultName, env0, bnds);
  }

  public void testEmpty()
  {
    SetComp set = makeSet(BigInteger.ZERO);
    TupleExpr tuple = factory_.createTupleExpr(i0, i0);
    assertFalse(set.contains(tuple));
    Iterator<Expr> iter = set.iterator();
    assertFalse(iter.hasNext());
    assertTrue(set.isEmpty());
    assertEquals(0.0, set.estSize(), ACCURACY);
    //assertEquals(BigInteger.ZERO, set.maxSize());
    assertEquals(0, set.size());
  }

  public void testTen()
  {
    SetComp set = makeSet(BigInteger.valueOf(10));
    TupleExpr tuple = factory_.createTupleExpr(i2, i4);
    assertTrue(set.contains(tuple));
    Iterator<Expr> iter = set.iterator();
    assertTrue(iter.hasNext());
    assertFalse(set.isEmpty());
    assertEquals(8.0, set.estSize(), ACCURACY);  // very roughly 8.0
    //assertEquals(BigInteger.ZERO, set.maxSize());
    assertEquals(10, set.size());
  }

  /** This tests (?,6) in {x:nat | x<y @ (x,x*2)} can find the ?. */
  public void testMatchIterator()
  {
    SetComp set = makeSet(BigInteger.valueOf(1000000000));
    TupleExpr tuple = factory_.createTupleExpr(i2, i4);
    assertTrue(set.contains(tuple));
    Map<Object, Expr> known = new HashMap<Object, Expr>();
    known.put(Integer.valueOf(2), i6);
    Iterator<Expr> iter = set.matchIterator(known);
    assertTrue(iter.hasNext());
    TupleExpr result = (TupleExpr) iter.next();
    assertEquals(i3, result.getZExprList().get(0));
    assertEquals(i6, result.getZExprList().get(1));
    assertFalse(iter.hasNext());
  }
}
