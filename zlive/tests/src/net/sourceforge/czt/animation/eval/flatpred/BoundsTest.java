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
import net.sourceforge.czt.animation.eval.ZTestCase;

/** Tests the Bounds class. */
public class BoundsTest extends ZTestCase
{
  public void testLower()
  {
    Bounds bnds = new Bounds();
    Assert.assertNull(bnds.getLower(x));
    
    // add a lower bound
    bnds.addLower(x, new BigInteger("-10"));
    Assert.assertEquals(bnds.getLower(x), new BigInteger("-10"));
    
    // add a weaker lower bound
    bnds.addLower(x, new BigInteger("-11"));
    Assert.assertEquals(bnds.getLower(x), new BigInteger("-10"));
    
    // add a stronger lower bound
    bnds.addLower(x, new BigInteger("-9"));
    Assert.assertEquals(bnds.getLower(x), new BigInteger("-9"));
    
    // add an even stronger (and positive) lower bound
    bnds.addLower(x, new BigInteger("9"));
    Assert.assertEquals(bnds.getLower(x), new BigInteger("9"));
  }
  
  public void testUpper()
  {
    Bounds bnds = new Bounds();
    Assert.assertNull(bnds.getUpper(x));
    
    // add a upper bound
    bnds.addUpper(x, new BigInteger("10"));
    Assert.assertEquals(bnds.getUpper(x), new BigInteger("10"));
    
    // add a weaker upper bound
    bnds.addUpper(x, new BigInteger("11"));
    Assert.assertEquals(bnds.getUpper(x), new BigInteger("10"));
    
    // add a stronger upper bound
    bnds.addUpper(x, new BigInteger("9"));
    Assert.assertEquals(bnds.getUpper(x), new BigInteger("9"));
    
    // add an even stronger (and negative) upper bound
    bnds.addUpper(x, new BigInteger("-9"));
    Assert.assertEquals(bnds.getUpper(x), new BigInteger("-9"));
  }
}
