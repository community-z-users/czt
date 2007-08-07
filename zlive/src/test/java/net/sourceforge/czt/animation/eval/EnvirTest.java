/**
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.animation.eval;

import java.util.HashSet;
import java.util.Set;

import junit.framework.Assert;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ZName;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class EnvirTest
  extends ZTestCase
{
  private Envir empty = new Envir();
  private Envir empty2 = new Envir();
  private Envir x10 = empty.plus(x,i10);
  private Envir x10b = empty.plus(x,i10);
  private Envir x20 = empty.plus(x,i20);
  private Envir y10 = empty.plus(y,i10);
  private Envir x10x20 = x20.plus(x,i10);
  private Envir x10y20 = x10.plus(y,i20);
  
  public void testIsDefined()
  {
    Assert.assertTrue(x10y20.isDefined(x));
    Assert.assertTrue(x10y20.isDefined(y));
    Assert.assertFalse(x10.isDefined(y));
  }

  public void testIsDefinedSince()
  {
    Assert.assertFalse(x10y20.isDefinedSince(x10,x));
    Assert.assertTrue(x10y20.isDefinedSince(x10,y));
  }
  
  public void testDefinedSince()
  {
    Set<ZName> result = new HashSet<ZName>();
    result.add(y);
    Assert.assertEquals(result, x10y20.definedSince(x10));
  }
  
  public void testEqualsEmptyEmpty()
  {
    Assert.assertTrue(empty.equals(empty2));
  }
  
  public void testEqualsx10x20()
  {
    Assert.assertFalse(x10.equals(x20));
  }
  
  public void testEqualsx10y10()
  {
    Assert.assertFalse(x10.equals(y10));
  }
 
  public void testEqualsx10x10b()
  {
    Assert.assertTrue(x10.equals(x10b));
  }
  
  public void testEqualsEmptyx10()
  {
    Assert.assertFalse(empty.equals(x10));
  }
  
  public void testEqualsx10Empty()
  {
    Assert.assertFalse(x10.equals(empty));
  }
  
  public void testEqualsx10x20x10()
  {
    Assert.assertFalse(x10x20.equals(x10));
  }
  
  public void testLookupxEmpty()
  {
    try {
	Assert.assertFalse(empty.lookup(x)==null);
    }
    catch (EvalException ex) {
    }
  }
  
  public void testLookupxx10()
  {
    Assert.assertEquals(i10, x10.lookup(x));
  }

  public void testLookupxx10x20()
  {
    Assert.assertEquals(i10, x10x20.lookup(x));
  }

  public void testSetValueOldest()
  {
    Envir env = new Envir().plus(x,i10).plus(y,i20);
    env.setValue(x,i5);
    Assert.assertEquals(i5, env.lookup(x));
    Assert.assertEquals(i20, env.lookup(y));
  }

  public void testSetValueNewest()
  {
    Envir env = new Envir().plus(x,i10).plus(y,i20);
    env.setValue(y,i5);
    Assert.assertEquals(i5, env.lookup(y));
    Assert.assertEquals(i10, env.lookup(x));
  }
  
  public void testPlusAll()
  {
    BindExpr args = (BindExpr) parseExpr("\\lblot x==0, y==10 \\rblot");
    Envir env = new Envir().plusAll(args);
    assertEquals(i0, env.lookup(x));
    assertEquals(i10, env.lookup(y));
  }
}

  
    
    
