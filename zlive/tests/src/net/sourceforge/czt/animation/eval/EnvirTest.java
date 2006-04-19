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

import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.ZRefName;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.z.util.Factory;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class EnvirTest
  extends TestCase
{
  private Factory factory_ = new Factory(new ZFactoryImpl());

  private List<Stroke> emptyList = new ArrayList<Stroke>();
  private Envir empty = new Envir();
  private Envir empty2 = new Envir();
  private ZRefName x = factory_.createZRefName("x",emptyList,null);
  private ZRefName y = factory_.createZRefName("y",emptyList,null);
  private Expr i10 = factory_.createNumExpr(factory_.createZNumeral(10));
  private Expr i20 = factory_.createNumExpr(factory_.createZNumeral(20));
  private Envir x10 = empty.plus(x,i10);
  private Envir x10b = empty.plus(x,i10);
  private Envir x20 = empty.plus(x,i20);
  private Envir y10 = empty.plus(y,i10);
  private Envir x10x20 = x20.plus(x,i10);
  
  public void testEqualsEmptyEmpty()
  {
    Assert.assertTrue(empty.equals(empty2));
  }
  
  public void testEqualsx10x20()
  {
    Assert.assertTrue(!x10.equals(x20));
  }
  
  public void testEqualsx10y10()
  {
    Assert.assertTrue(!x10.equals(y10));
  }
 
  public void testEqualsx10x10b()
  {
    Assert.assertTrue(x10.equals(x10b));
  }
  
  public void testEqualsEmptyx10()
  {
    Assert.assertTrue(!empty.equals(x10));
  }
  
  public void testEqualsx10Empty()
  {
    Assert.assertTrue(!x10.equals(empty));
  }
  
  public void testEqualsx10x20x10()
  {
    Assert.assertTrue(!x10x20.equals(x10));
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
    Assert.assertTrue(x10.lookup(x).equals(i10));
  }

  public void testLookupxx10x20()
  {
    Assert.assertTrue(x10x20.lookup(x).equals(i10));
  }

}

  
    
    
