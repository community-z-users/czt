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

import java.io.IOException;
import java.net.URL;
import java.util.*;
import java.math.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;


/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class EnvirTest
  extends TestCase
{
  private ZFactory factory_ = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  private List emptyList = new ArrayList();
  private Envir empty = new Envir();
  private Envir empty2 = new Envir();
  private BigInteger a = new BigInteger("10");
  private BigInteger b = new BigInteger("20");
  private RefName x = factory_.createRefName("x",emptyList,null);
  private RefName y = factory_.createRefName("y",emptyList,null);
  private Term i10 = factory_.createNumExpr(a);
  private Term i20 = factory_.createNumExpr(b);
  private Envir x10 = empty.add(x,i10);
  private Envir x10b = empty.add(x,i10);
  private Envir x20 = empty.add(x,i20);
  private Envir y10 = empty.add(y,i10);
  private Envir x10x20 = x20.add(x,i10);
  
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
    Assert.assertTrue(empty.lookup(x)==null);
  }
  
  public void testLookupxx10()
  {
    Assert.assertTrue(x10.lookup(x).equals(i10));
  }

  public void testLookupxy10()
  {
    Assert.assertTrue(y10.lookup(x)==null);
  }

  public void testLookupxx10x20()
  {
    Assert.assertTrue(x10x20.lookup(x).equals(i10));
  }

}

  
    
    
