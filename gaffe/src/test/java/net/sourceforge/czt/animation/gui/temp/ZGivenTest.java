package net.sourceforge.czt.animation.gui.temp;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.z.ast.Expr;

public class ZGivenTest extends TestCase
{
  private ZGiven ga = new ZGiven("A");
  private ZGiven gb = new ZGiven("A");
  private ZGiven gc = new ZGiven("C");
  
  private String name_ = "Try_019_!@#$%^&*()~|\"\\\"?<>:;''''{}[]-=_,.+";
  private ZGiven gd = new ZGiven(name_);
  
  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.hashCode()'
   */
  public void testHashCode()
  {
    Assert.assertEquals(ga.hashCode(),gb.hashCode());
    Assert.assertNotSame(ga.hashCode(),gc.hashCode());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.ZGiven(String)'
   */
  public void testZGivenString()
  {
    Assert.assertEquals("A",ga.toString());
    Assert.assertEquals(gb,ga);
    Assert.assertEquals(gc,new ZGiven("C"));
    Assert.assertFalse(ga.equals(gc));
    Assert.assertEquals(gd,new ZGiven(name_));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.ZGiven(GivenValue)'
   */
  public void testZGivenGivenValue()
  {
    GivenValue e = ga.getExpr();
    ZGiven tmp = new ZGiven(e);
    Assert.assertSame(tmp.getExpr(),e);
    Assert.assertEquals(tmp,ga);
    Assert.assertEquals(tmp,gb);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.getValue()'
   */
  public void testGetValue()
  {
    Assert.assertEquals(ga.getValue(),"A");
    Assert.assertEquals(gb.getValue(),"A");
    Assert.assertEquals(gc.getValue(),"C");
    Assert.assertEquals(gd.getValue(),"Try_019_!@#$%^&*()~|\"\\\"?<>:;''''{}[]-=_,.+");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.toString()'
   */
  public void testToString()
  {
    Assert.assertEquals(ga.toString(),"A");
    Assert.assertEquals(gb.toString(),"A");
    Assert.assertEquals(gc.toString(),"C");
    Assert.assertEquals(gd.getValue(),"Try_019_!@#$%^&*()~|\"\\\"?<>:;''''{}[]-=_,.+");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.equals(Object)'
   */
  public void testEqualsObject()
  {
    Assert.assertTrue(ga.equals(gb));
    Assert.assertTrue(gb.equals(ga));
    Assert.assertFalse(ga.equals(gc));
    Assert.assertFalse(gb.equals(gd));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZGiven.getExpr()'
   */
  public void testGetExpr()
  {
    Expr expr_a = ga.getExpr();
    Expr expr_b = gb.getExpr();
    Expr expr_c = gc.getExpr();
    Expr expr_d = gd.getExpr();
    Assert.assertTrue(expr_d instanceof GivenValue);
    Assert.assertNotNull(expr_a);
    Assert.assertNotNull(expr_d);
    Assert.assertEquals(expr_a,expr_b);
    Assert.assertFalse(expr_c.equals(expr_d));
  }

}
