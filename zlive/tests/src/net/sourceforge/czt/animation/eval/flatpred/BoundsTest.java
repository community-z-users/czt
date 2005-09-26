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

import junit.framework.*;
import java.math.BigInteger;

import net.sourceforge.czt.animation.eval.ZLive;
import net.sourceforge.czt.animation.eval.ZTestCase;

/** Tests the Bounds class. */
public class BoundsTest extends ZTestCase
{
  ZLive zlive_ = new ZLive();
  
  public void testLower()
  {
    Bounds bnds = new Bounds();
    Assert.assertNull(bnds.getLower(x));
    
    // add a lower bound
    Assert.assertTrue(bnds.addLower(x, new BigInteger("-10")));
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(x));
    
    // add a weaker lower bound
    Assert.assertFalse(bnds.addLower(x, new BigInteger("-11")));
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(x));
    
    // add a stronger lower bound
    Assert.assertTrue(bnds.addLower(x, new BigInteger("-9")));
    Assert.assertEquals(new BigInteger("-9"), bnds.getLower(x));
    
    // add an even stronger (and positive) lower bound
    Assert.assertTrue(bnds.addLower(x, new BigInteger("9")));
    Assert.assertEquals(new BigInteger("9"), bnds.getLower(x));
  }
  
  public void testUpper()
  {
    Bounds bnds = new Bounds();
    Assert.assertNull(bnds.getUpper(x));
    
    // add an upper bound
    Assert.assertTrue(bnds.addUpper(x, new BigInteger("10")));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
    
    // add a weaker upper bound
    Assert.assertFalse(bnds.addUpper(x, new BigInteger("11")));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
    
    // add a stronger upper bound
    Assert.assertTrue(bnds.addUpper(x, new BigInteger("9")));
    Assert.assertEquals(new BigInteger("9"), bnds.getUpper(x));
    
    // add an even stronger (and negative) upper bound
    Assert.assertTrue(bnds.addUpper(x, new BigInteger("-9")));
    Assert.assertEquals(new BigInteger("-9"), bnds.getUpper(x));
  }
  
  public void testConst()
  {
    Bounds bnds = new Bounds();
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatConst(x,i20));
    Assert.assertEquals(1, preds.size());
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertEquals(new BigInteger("20"), bnds.getLower(x));
    Assert.assertEquals(new BigInteger("20"), bnds.getUpper(x));
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
  }
  

  /** Tests FlatLessThan bounds propogation from left to right. */
  public void testLessThanLeft()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThan(x,y));
    preds.add(new FlatLessThan(y,z));
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertEquals(new BigInteger("-9"), bnds.getLower(y));
    Assert.assertNull(bnds.getUpper(y));
    Assert.assertEquals(new BigInteger("-8"), bnds.getLower(z));
    Assert.assertNull(bnds.getUpper(z));
    // Check that we have reached a fixed point.
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
    // Finally, check that the bounds of x have NOT changed.
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
  }
  
  /** Tests FlatLessThan bounds propogation from right to left. */
  public void testLessThanRight()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(z, new BigInteger("-10"));
    bnds.addUpper(z, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThan(x,y));
    preds.add(new FlatLessThan(y,z));
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertNull(bnds.getLower(y));
    Assert.assertEquals(new BigInteger("9"), bnds.getUpper(y));
    Assert.assertNull(bnds.getLower(x));
    Assert.assertEquals(new BigInteger("8"), bnds.getUpper(x));

    // Check that we have reached a fixed point.
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
    // Finally, check that the bounds of z have NOT changed.
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(z));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(z));
  }
  
  /** Tests FlatLessThanEquals bounds propogation from left to right. */
  public void testLessThanEqualsLeft()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThanEquals(x,y));
    preds.add(new FlatLessThanEquals(y,z));
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(y));
    Assert.assertNull(bnds.getUpper(y));
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(z));
    Assert.assertNull(bnds.getUpper(z));
    // Check that we have reached a fixed point.
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
    // Finally, check that the bounds of x have NOT changed.
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));
  }
  
  /** Tests FlatLessThanEquals bounds propogation from right to left. */
  public void testLessThanEqualsRight()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(z, new BigInteger("-10"));
    bnds.addUpper(z, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatLessThanEquals(x,y));
    preds.add(new FlatLessThanEquals(y,z));
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertNull(bnds.getLower(y));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(y));
    Assert.assertNull(bnds.getLower(x));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(x));

    // Check that we have reached a fixed point.
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
    // Finally, check that the bounds of z have NOT changed.
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(z));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(z));
  }
  
  /** Tests FlatEquals bounds propogation. */
  public void testEquals()
  {
    Bounds bnds = new Bounds();
    bnds.addLower(x, new BigInteger("-10"));
    bnds.addUpper(x, new BigInteger("10"));
    FlatPredList preds = new FlatPredList(zlive_);
    preds.add(new FlatEquals(x,y));
    preds.add(new FlatEquals(y,z));
    boolean changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(y));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(y));
    Assert.assertEquals(new BigInteger("-10"), bnds.getLower(z));
    Assert.assertEquals(new BigInteger("10"), bnds.getUpper(z));

    // Now strengthen the bounds on z to 0..5
    bnds.addLower(z, new BigInteger("0"));
    bnds.addUpper(z, new BigInteger("5"));
    // and check that they propagate to the other variables.
    changed = preds.inferBounds(bnds);
    Assert.assertTrue(changed);
    Assert.assertEquals(new BigInteger("0"), bnds.getLower(x));
    Assert.assertEquals(new BigInteger("5"), bnds.getUpper(x));
    Assert.assertEquals(new BigInteger("0"), bnds.getLower(y));
    Assert.assertEquals(new BigInteger("5"), bnds.getUpper(y));
    Assert.assertEquals(new BigInteger("0"), bnds.getLower(z));
    Assert.assertEquals(new BigInteger("5"), bnds.getUpper(z));
    
    // Check that we have reached a fixed point.
    changed = preds.inferBounds(bnds);
    Assert.assertFalse(changed);
  }
}
