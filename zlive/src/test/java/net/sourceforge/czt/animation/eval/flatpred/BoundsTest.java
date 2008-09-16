/**
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

package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.animation.eval.ZTestCase;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZChar;

/** Tests the Bounds class. */
public class BoundsTest extends ZTestCase
{
  public void testLower()
  {
    Bounds bnds = new Bounds(null);
    assertNull(bnds.getLower(x));
    assertEquals(0, bnds.getDeductions());
    assertEquals(0, bnds.getLowerKeys().size());
    assertEquals(0, bnds.getUpperKeys().size());
    assertEquals(0, bnds.getEvalSetKeys().size());
    assertFalse(bnds.boundsChanged());

    // add a lower bound
    assertTrue(bnds.addLower(x, new BigInteger("-10")));
    assertEquals(new BigInteger("-10"), bnds.getLower(x));

    // check the change detection
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.boundsChanged(x));
    assertFalse(bnds.boundsChanged(y));
    assertEquals(1, bnds.getDeductions());

    // add a weaker lower bound
    assertFalse(bnds.addLower(x, new BigInteger("-11")));
    assertEquals(new BigInteger("-10"), bnds.getLower(x));

    // add a stronger lower bound
    assertTrue(bnds.addLower(x, new BigInteger("-9")));
    assertEquals(new BigInteger("-9"), bnds.getLower(x));

    // add an even stronger (and positive) lower bound
    assertTrue(bnds.addLower(x, new BigInteger("9")));
    assertEquals(new BigInteger("9"), bnds.getLower(x));

    // recheck the change detection and counting
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.boundsChanged(x));
    assertFalse(bnds.boundsChanged(y));
    assertEquals(3, bnds.getDeductions());
  }

  public void testUpper()
  {
    Bounds bnds = new Bounds(null);
    assertNull(bnds.getUpper(x));
    assertEquals(0, bnds.getDeductions());
    assertEquals(0, bnds.getLowerKeys().size());
    assertEquals(0, bnds.getUpperKeys().size());
    assertEquals(0, bnds.getEvalSetKeys().size());
    assertFalse(bnds.boundsChanged());

    // add an upper bound
    assertTrue(bnds.addUpper(x, new BigInteger("10")));
    assertEquals(new BigInteger("10"), bnds.getUpper(x));

    // check the change detection
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.boundsChanged(x));
    assertFalse(bnds.boundsChanged(y));
    assertEquals(1, bnds.getDeductions());

    // add a weaker upper bound
    assertFalse(bnds.addUpper(x, new BigInteger("11")));
    assertEquals(new BigInteger("10"), bnds.getUpper(x));

    // add a stronger upper bound
    assertTrue(bnds.addUpper(x, new BigInteger("9")));
    assertEquals(new BigInteger("9"), bnds.getUpper(x));

    // add an even stronger (and negative) upper bound
    assertTrue(bnds.addUpper(x, new BigInteger("-9")));
    assertEquals(new BigInteger("-9"), bnds.getUpper(x));

    // recheck the change detection and counting
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.boundsChanged(x));
    assertFalse(bnds.boundsChanged(y));
    assertEquals(3, bnds.getDeductions());
  }

  public void testConst()
  {
    Bounds bnds = new Bounds(null);
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatConst(x,i20));
    assertEquals(1, preds.size());
    preds.inferBoundsFixPoint(bnds);
    assertEquals(new BigInteger("20"), bnds.getLower(x));
    assertEquals(new BigInteger("20"), bnds.getUpper(x));
  }

  /**
   * Checks that bnds already contains all the Bounds deductions
   * that can be made by pred.
   * @param pred
   * @param bnds
   */
  private void checkFixPoint(FlatPred pred, Bounds bnds)
  {
    bnds.startAnalysis();
    assertFalse(bnds.boundsChanged());
    assertEquals(0, bnds.getDeductions());
    pred.inferBounds(bnds);
    bnds.endAnalysis();
    assertFalse(bnds.boundsChanged());
    assertEquals(0, bnds.getDeductions());
  }

  /** Tests FlatLessThan bounds propagation from left to right. */
  public void testLessThanLeft()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThan(x,y));
    preds.add(new FlatLessThan(y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-9"), bnds.getLower(y));
    assertNull(bnds.getUpper(y));
    assertEquals(new BigInteger("-8"), bnds.getLower(z));
    assertNull(bnds.getUpper(z));

    checkFixPoint(preds, bnds);
    // Finally, check that the bounds of x have NOT changed.
    assertEquals(new BigInteger("10"), bnds.getUpper(x));
    assertEquals(new BigInteger("10"), bnds.getUpper(x));
  }

  /** Tests FlatLessThan bounds propagation from right to left. */
  public void testLessThanRight()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(z, new BigInteger("-10"));
    bnds.addUpper(z, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThan(x,y));
    preds.add(new FlatLessThan(y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertNull(bnds.getLower(y));
    assertEquals(new BigInteger("9"), bnds.getUpper(y));
    assertNull(bnds.getLower(x));
    assertEquals(new BigInteger("8"), bnds.getUpper(x));

    checkFixPoint(preds, bnds);
    // Finally, check that the bounds of z have NOT changed.
    assertEquals(new BigInteger("10"), bnds.getUpper(z));
    assertEquals(new BigInteger("10"), bnds.getUpper(z));
  }

  /** Tests FlatLessThanEquals bounds propagation from left to right. */
  public void testLessThanEqualsLeft()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThanEquals(x,y));
    preds.add(new FlatLessThanEquals(y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-10"), bnds.getLower(y));
    assertNull(bnds.getUpper(y));
    assertEquals(new BigInteger("-10"), bnds.getLower(z));
    assertNull(bnds.getUpper(z));

    checkFixPoint(preds, bnds);
    // Finally, check that the bounds of x have NOT changed.
    assertEquals(new BigInteger("10"), bnds.getUpper(x));
    assertEquals(new BigInteger("10"), bnds.getUpper(x));
  }

  /** Tests FlatLessThanEquals bounds propagation from right to left. */
  public void testLessThanEqualsRight()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(z, new BigInteger("-10"));
    bnds.addUpper(z, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThanEquals(x,y));
    preds.add(new FlatLessThanEquals(y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertNull(bnds.getLower(y));
    assertEquals(new BigInteger("10"), bnds.getUpper(y));
    assertNull(bnds.getLower(x));
    assertEquals(new BigInteger("10"), bnds.getUpper(x));

    checkFixPoint(preds, bnds);
    // Finally, check that the bounds of z have NOT changed.
    assertEquals(new BigInteger("10"), bnds.getUpper(z));
    assertEquals(new BigInteger("10"), bnds.getUpper(z));
  }

  /** Tests FlatEquals bounds propagation. */
  public void testEquals()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatEquals(x,y));
    preds.add(new FlatEquals(y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-10"), bnds.getLower(y));
    assertEquals(new BigInteger("10"), bnds.getUpper(y));
    assertEquals(new BigInteger("-10"), bnds.getLower(z));
    assertEquals(new BigInteger("10"), bnds.getUpper(z));

    // Now strengthen the bounds on z to 0..5
    bnds.addLower(z, new BigInteger("0"));
    bnds.addUpper(z, new BigInteger("5"));
    // and check that they propagate to the other variables.
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("0"), bnds.getLower(x));
    assertEquals(new BigInteger("5"), bnds.getUpper(x));
    assertEquals(new BigInteger("0"), bnds.getLower(y));
    assertEquals(new BigInteger("5"), bnds.getUpper(y));
    assertEquals(new BigInteger("0"), bnds.getLower(z));
    assertEquals(new BigInteger("5"), bnds.getUpper(z));

    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from left to right,
   *  with no existing bounds on y.
   */
  public void testNegateRightNone()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("1"));
    bnds.addUpper(x, new BigInteger("5"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("1"), bnds.getLower(x));
    assertEquals(new BigInteger("5"), bnds.getUpper(x));
    assertEquals(new BigInteger("-5"), bnds.getLower(y));
    assertEquals(new BigInteger("-1"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from left to right
   *  with existing looser bounds on y.
   */
  public void testNegateRightLoose()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("1"));
    bnds.addUpper(x, new BigInteger("5"));
    bnds.addLower(y, new BigInteger("-10"));
    bnds.addUpper(y, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("1"), bnds.getLower(x));
    assertEquals(new BigInteger("5"), bnds.getUpper(x));
    assertEquals(new BigInteger("-5"), bnds.getLower(y));
    assertEquals(new BigInteger("-1"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from left to right
   *  with existing tighter bounds on y.
   */
  public void testNegateRightTight()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("1"));
    bnds.addUpper(x, new BigInteger("5"));
    bnds.addLower(y, new BigInteger("-4"));
    bnds.addUpper(y, new BigInteger("-2"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("2"), bnds.getLower(x));
    assertEquals(new BigInteger("4"), bnds.getUpper(x));
    assertEquals(new BigInteger("-4"), bnds.getLower(y));
    assertEquals(new BigInteger("-2"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from right to left,
   *  with no existing bounds on x.
   */
  public void testNegateLeftNone()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-5"));
    bnds.addUpper(x, new BigInteger("-1"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-5"), bnds.getLower(x));
    assertEquals(new BigInteger("-1"), bnds.getUpper(x));
    assertEquals(new BigInteger("1"), bnds.getLower(y));
    assertEquals(new BigInteger("5"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from right to left
   *  with existing looser bounds on x.
   */
  public void testNegateLeftLoose()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-5"));
    bnds.addUpper(x, new BigInteger("-1"));
    bnds.addLower(y, new BigInteger("-10"));
    bnds.addUpper(y, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-5"), bnds.getLower(x));
    assertEquals(new BigInteger("-1"), bnds.getUpper(x));
    assertEquals(new BigInteger("1"), bnds.getLower(y));
    assertEquals(new BigInteger("5"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatNegate(x,y) bounds propagation from right to left
   *  with existing tighter bounds on x.
   */
  public void testNegateLeftTight()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("-4"));
    bnds.addUpper(x, new BigInteger("-2"));
    bnds.addLower(y, new BigInteger("1"));
    bnds.addUpper(y, new BigInteger("5"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatNegate(x,y));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("-4"), bnds.getLower(x));
    assertEquals(new BigInteger("-2"), bnds.getUpper(x));
    assertEquals(new BigInteger("2"), bnds.getLower(y));
    assertEquals(new BigInteger("4"), bnds.getUpper(y));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatPlus bounds propagation on x+y=z */
  public void testPlusRight()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("0"));
    bnds.addUpper(x, new BigInteger("5"));
    bnds.addLower(y, new BigInteger("3"));
    bnds.addUpper(y, new BigInteger("4"));
    bnds.addLower(z, new BigInteger("-10"));
    bnds.addUpper(z, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatPlus(x,y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("0"), bnds.getLower(x));
    assertEquals(new BigInteger("5"), bnds.getUpper(x));
    assertEquals(new BigInteger("3"), bnds.getLower(y));
    assertEquals(new BigInteger("4"), bnds.getUpper(y));
    assertEquals(new BigInteger("3"), bnds.getLower(z));
    assertEquals(new BigInteger("9"), bnds.getUpper(z));
    checkFixPoint(preds, bnds);
  }

  /** Tests FlatPlus bounds propagation on x+y=z */
  public void testPlusLeft()
  {
    Bounds bnds = new Bounds(null);
    bnds.addLower(x, new BigInteger("0"));
    bnds.addUpper(x, new BigInteger("10"));
    bnds.addLower(y, new BigInteger("2"));
    bnds.addUpper(y, new BigInteger("3"));
    bnds.addLower(z, new BigInteger("7"));
    bnds.addUpper(z, new BigInteger("8"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatPlus(x,y,z));
    assertTrue(preds.inferBoundsFixPoint(bnds));
    assertEquals(new BigInteger("4"), bnds.getLower(x));
    assertEquals(new BigInteger("6"), bnds.getUpper(x));
    assertEquals(new BigInteger("2"), bnds.getLower(y));
    assertEquals(new BigInteger("3"), bnds.getUpper(y));
    assertEquals(new BigInteger("7"), bnds.getLower(z));
    assertEquals(new BigInteger("8"), bnds.getUpper(z));
    checkFixPoint(preds, bnds);
  }

  public void testSetCompExpr()
  {
    Bounds bnds = new Bounds(null);
    Expr setexpr
      = parseExpr("\\{x,y,z:\\nat | x < y \\land y < z \\land z < 10 @ x\\}");
    FlatPredList preds = new FlatPredList(zlive_);
    ZName setname = preds.addExpr(setexpr);
    preds.inferBoundsFixPoint(bnds);
    EvalSet est = bnds.getEvalSet(setname);
    assertNotNull(est);
    assertEquals(BigInteger.valueOf(0), est.getLower());
    assertEquals(BigInteger.valueOf(7), est.getUpper());
    // TODO: add these once SetComp does better size estimation
    //assertNotNull(est.maxSize());
    //assertTrue(est.maxSize().intValue() <= 1000);
    checkFixPoint(preds, bnds);
  }

  /** Tests simple aliasing between ZNames within one Bounds object. */
  public void testAlias1()
  {
    Bounds bnds = new Bounds(null);
    assertFalse(bnds.isAliased(x, y));
    assertTrue(bnds.isAliased(x, x));
    assertFalse(bnds.boundsChanged());
    assertEquals(0, bnds.getDeductions());
    bnds.addAlias(x, y);
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.isAliased(x, y));
    assertTrue(bnds.isAliased(y, x));
    assertEquals(2, bnds.getAliasKeys().size());
    Set<ZName> aliases = bnds.getAliases(x);
    assertSame(aliases, bnds.getAliases(y));
    assertTrue(aliases.contains(x));
    assertTrue(aliases.contains(y));

    // add some bounds to an aliased var
    assertTrue(bnds.addLower(x, BigInteger.valueOf(10)));
    assertEquals(BigInteger.valueOf(10), bnds.getLower(x));
    assertEquals(BigInteger.valueOf(10), bnds.getLower(y));

    assertTrue(bnds.addUpper(x, BigInteger.valueOf(20)));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(x));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(y));

    // alias a third variable
    bnds.addAlias(x,z);
    assertTrue(bnds.isAliased(x, y));
    assertTrue(bnds.isAliased(y, z));
    assertTrue(bnds.isAliased(y, x));
    assertTrue(bnds.isAliased(z, y));
    aliases = bnds.getAliases(x);
    assertEquals(3, aliases.size());
    assertSame(aliases, bnds.getAliases(y));
    assertSame(aliases, bnds.getAliases(z));
    assertTrue(aliases.contains(x));
    assertTrue(aliases.contains(y));
    assertTrue(aliases.contains(z));

    // check the above lower bound
    assertEquals(BigInteger.valueOf(10), bnds.getLower(z));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(z));
  }

  /** Tests w=x, then y=z, then x=y aliasing within one Bounds object. */
  public void testAlias2()
  {
    //System.out.println("Starting testAlias2");
    ZName w = factory_.createZName("w");
    Bounds bnds = new Bounds(null);
    // add some bounds:  w : 10..20
    assertTrue(bnds.addLower(w, BigInteger.valueOf(10)));
    assertTrue(bnds.addUpper(w, BigInteger.valueOf(20)));

    //System.out.println("w=x  (where w:10..20)");
    bnds.addAlias(w, x);
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.isAliased(w, x));
    assertTrue(bnds.isAliased(x, w));
    assertEquals(BigInteger.valueOf(10), bnds.getLower(w));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(w));
    assertEquals(BigInteger.valueOf(10), bnds.getLower(x));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(x));

    // add some bounds:  y : 11..21
    assertTrue(bnds.addLower(y, BigInteger.valueOf(11)));
    assertTrue(bnds.addUpper(y, BigInteger.valueOf(21)));

    //System.out.println("y=z  (where y:11..21)");
    bnds.addAlias(y, z);
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.isAliased(y, z));
    assertTrue(bnds.isAliased(z, y));
    assertEquals(BigInteger.valueOf(11), bnds.getLower(y));
    assertEquals(BigInteger.valueOf(21), bnds.getUpper(y));
    assertEquals(BigInteger.valueOf(11), bnds.getLower(z));
    assertEquals(BigInteger.valueOf(21), bnds.getUpper(z));

    //System.out.println("x=y");
    bnds.addAlias(x, y);
    assertTrue(bnds.isAliased(w, x));
    assertTrue(bnds.isAliased(x, y));
    assertTrue(bnds.isAliased(y, z));
    assertTrue(bnds.isAliased(z, w));
    Set<ZName> aliases = bnds.getAliases(x);
    assertEquals(4, aliases.size());
    assertTrue(aliases.contains(w));
    assertTrue(aliases.contains(x));
    assertTrue(aliases.contains(y));
    assertTrue(aliases.contains(z));

    // check the above lower bound
    assertEquals(BigInteger.valueOf(11), bnds.getLower(w));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(w));
    assertEquals(BigInteger.valueOf(11), bnds.getLower(x));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(x));
    assertEquals(BigInteger.valueOf(11), bnds.getLower(y));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(y));
    assertEquals(BigInteger.valueOf(11), bnds.getLower(z));
    assertEquals(BigInteger.valueOf(20), bnds.getUpper(z));
  }

  /** Tests aliasing between ZNames and a Tuple, using parent
   * and child Bounds objects.
   */
  public void testAliasTuple()
  {
    Bounds bnds = new Bounds(null);

    // alias x = (y,z)
    bnds.addStructureArg(x, Integer.valueOf(1), y);
    bnds.addStructureArg(x, Integer.valueOf(2), z);
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.getDeductions() > 0);
    Map<Object, ZName> args = bnds.getStructure(x);
    assertNotNull(args);
    assertEquals(2, args.size());
    assertEquals(y, args.get(Integer.valueOf(1)));
    assertEquals(z, args.get(Integer.valueOf(2)));

    // alias x = w in a sub-bounds.
    bnds.startAnalysis();  // resets deduction count
    assertEquals(0, bnds.getDeductions());
    Bounds bnds2 = new Bounds(bnds);
    bnds2.startAnalysis(bnds);
    assertEquals(args, bnds2.getStructure(x)); // should be copied down
    assertEquals(0, bnds2.getDeductions());
    ZName w = factory_.createZName("w");
    bnds2.addAlias(w, x);
    assertTrue(bnds2.isAliased(x, w));
    assertTrue(bnds2.boundsChanged());
    assertTrue(bnds2.getDeductions() > 0);

    // check that w.1 = y and w.2 = z
    args = bnds2.getStructure(w);
    assertEquals(2, args.size());
    assertEquals(y, args.get(Integer.valueOf(1)));
    assertEquals(z, args.get(Integer.valueOf(2)));

    args = bnds2.getStructure(x);
    assertEquals(2, args.size());
    assertEquals(y, args.get(Integer.valueOf(1)));
    assertEquals(z, args.get(Integer.valueOf(2)));

    bnds2.endAnalysis();
    // parent should have noticed the changes
    assertTrue(bnds.getDeductions() > 0);

    // now alias x = (u,v) in the parent.
    ZName u = factory_.createZName("u");
    ZName v = factory_.createZName("v");
    bnds.addStructureArg(x, Integer.valueOf(1), u);
    bnds.addStructureArg(x, Integer.valueOf(2), v);

    // check that the parent has deduced u=y and v=z
    assertTrue(bnds.getDeductions() > 0);
    assertTrue(bnds.isAliased(y, u));
    assertTrue(bnds.isAliased(v, z));

    // check that the new aliases flow down into the child
    bnds2.startAnalysis(bnds);
    assertTrue(bnds.isAliased(y, u));
    assertTrue(bnds.isAliased(v, z));
    bnds2.endAnalysis();
  }

  /** Aliasing of tuples and bindings is done by the same code,
   *  so we don't need different tests for them.
   *  However, this test adds alias information in a different
   *  order to testAliasTuple.  This test was derived from failure
   *  to execute the Find operation of the BirthdayBook specification.
   */
  public void testAliasBinding()
  {
    Bounds bnds = new Bounds(null);

    // alias x = <| known==known, birthday==birthday |>
    ZName known = factory_.createZName("known");
    ZName birthday = factory_.createZName("birthday");
    bnds.addAlias(z, known);  // one component has an existing alias
    ZName knownBest = bnds.getBestAlias(known);
    bnds.addStructureArg(x, known, known);
    bnds.addStructureArg(x, birthday, birthday);
    assertTrue(bnds.boundsChanged());
    assertTrue(bnds.getDeductions() > 0);
    Map<Object, ZName> args = bnds.getStructure(x);
    assertNotNull(args);
    assertEquals(2, args.size());
    assertEquals(knownBest, args.get(known));
    assertEquals(birthday, args.get(birthday));

    // alias y = <| known==known', birthday==birthday' |>
    ZName knownP = factory_.createZName("known"+ZChar.PRIME);
    assertEquals("known", knownP.getWord());
    ZName birthdayP = factory_.createZName("birthday"+ZChar.PRIME);
    assertEquals(1, knownP.getZStrokeList().size());
    bnds.addStructureArg(y, known, knownP);
    bnds.addStructureArg(y, birthday, birthdayP);

    // now alias x=y in a subbounds
    Bounds bnds2 = new Bounds(bnds);
    bnds2.startAnalysis(bnds);
    assertEquals(args, bnds2.getStructure(x)); // should be copied down
    bnds2.addAlias(y, x);
    bnds2.endAnalysis();
    // parent should have noticed the changes
    assertTrue(bnds.getDeductions() > 0);

    // check that bnds2 has made some deductions
    assertTrue(bnds2.isAliased(x, y));
    assertTrue(bnds2.boundsChanged());
    assertTrue(bnds2.getDeductions() > 0);

    // check that bnds2 has deduced x=y, known=known' and birthday=birthday'
    assertTrue(bnds2.isAliased(x, y));
    assertTrue(bnds2.isAliased(known, knownP));
    assertTrue(bnds2.isAliased(birthdayP, birthday));

    // check that bnds2 has correct structure information for x.
    args = bnds2.getStructure(x);
    assertEquals(2, args.size());
    assertEquals(bnds2.getBestAlias(known), args.get(known));
    assertEquals(bnds2.getBestAlias(birthdayP), args.get(birthday));

    // check that bnds2 has same information for y as for x.
    assertEquals(args, bnds2.getStructure(y));
  }

  public void testIncludesZeroLower()
  {
    Bounds bnds = new Bounds(null);
    assertTrue(bnds.includesZero(x));
    bnds.addLower(x, new BigInteger("0"));
    assertTrue(bnds.includesZero(x));
    bnds.addLower(x, new BigInteger("1"));
    assertFalse(bnds.includesZero(x));
  }

  public void testIncludesZeroUpper()
  {
    Bounds bnds = new Bounds(null);
    assertTrue(bnds.includesZero(x));
    bnds.addUpper(x, new BigInteger("0"));
    assertTrue(bnds.includesZero(x));
    bnds.addUpper(x, new BigInteger("-1"));
    assertFalse(bnds.includesZero(x));
  }
}
