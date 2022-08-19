package net.sourceforge.czt.animation.gui.temp;

import net.sourceforge.czt.z.ast.NumExpr;
import junit.framework.TestCase;

public class ZNumberTest extends TestCase
{
  ZNumber n10 = new ZNumber(10);
  ZNumber n10b = new ZNumber(10);

  ZNumber neg10 = new ZNumber(-10);
  
  
  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZNumber.hashCode()'
   */
  public void testHashCode()
  {
    assertEquals(n10.hashCode(), n10b.hashCode());
    assertFalse( n10.hashCode() == neg10.hashCode());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZNumber.ZNumber(NumExpr)'
   */
  public void testZNumberNumExpr()
  {
    NumExpr e = (NumExpr) n10.getExpr();
    ZNumber tmp = new ZNumber(e);
    assertTrue(tmp.getExpr() == e);
    assertEquals(tmp, n10);
    assertEquals(tmp, n10b);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZNumber.toString()'
   */
  public void testToString()
  {
    assertEquals("10", n10.toString());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZNumber.equals(Object)'
   */
  public void testEqualsObject()
  {
    assertEquals(n10, n10b);
    assertFalse(n10.equals(neg10));
  }
}
