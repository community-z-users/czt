package net.sourceforge.czt.animation.gui.temp;

import java.util.HashMap;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;

public class ZBindingTest extends TestCase
{
  private ZBinding ba;
  private ZBinding ba0;
  private ZBinding bb;
  private ZBinding bc;
  
  protected void setUp() throws Exception
  {
    super.setUp();
    HashMap<String, ZValue> tempa = new HashMap<String,ZValue>(); 
    tempa.put("1",new ZNumber(1));
    tempa.put("2",new ZNumber(2));
    tempa.put("3",new ZNumber(3));
    tempa.put("4",new ZNumber(4));
    tempa.put("5",new ZNumber(5));
    tempa.put("6",new ZNumber(6));
    ba = new ZBinding(tempa);
    ba0= new ZBinding(tempa);
    tempa.put("7",new ZNumber(7));
    bb = new ZBinding(tempa);
    tempa.put("ba",ba);
    tempa.put("bb",bb);
    bc = new ZBinding(tempa);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.hashCode()'
   */
  public void testHashCode()
  {
    Assert.assertEquals(ba.hashCode(),ba0.hashCode());
    Assert.assertNotSame(ba.hashCode(),bb.hashCode());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.ZBinding()'
   */
  public void testZBinding()
  {
    Assert.assertNotNull(new ZBinding().getExpr());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.ZBinding(Map<String, ZValue>)'
   */
  public void testZBindingMapOfStringZValue()
  {
    Assert.assertEquals(bc.get("ba"),ba);
    Assert.assertEquals(bc.get("bb"),bb);
    Assert.assertEquals(ba.get("1").toString(),"1");
    Assert.assertEquals(ba.get("6").toString(),"6");
    Assert.assertEquals(bb.get("1").toString(),"1");
    Assert.assertEquals(bb.get("7").toString(),"7");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.ZBinding(BindExpr)'
   */
  public void testZBindingBindExpr()
  {
    BindExpr be = ba.getExpr();
    ZBinding ba1 = new ZBinding(be);
    Assert.assertSame(ba1.getExpr(),be);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.keySet()'
   */
  public void testKeySet()
  {
    Assert.assertEquals(ba.keySet().size(),6);
    Assert.assertEquals(bb.keySet().size(),7);
    Assert.assertEquals(bc.keySet().size(),9);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.get(String)'
   */
  public void testGet()
  {
    Assert.assertEquals(ba.get("1").toString(),"1");
    Assert.assertEquals(ba.get("6").toString(),"6");
    Assert.assertEquals(bb.get("1").toString(),"1");
    Assert.assertEquals(bb.get("7").toString(),"7");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.equals(Object)'
   */
  public void testEqualsObject()
  {
    Assert.assertTrue(ba.equals(ba0));
    Assert.assertFalse(ba.equals(bb));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.toString()'
   */
  public void testToString()
  {
    Assert.assertEquals(ba.toString(),ba0.toString());
    Assert.assertNotSame(ba.toString(),bb.toString());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZBinding.getExpr()'
   */
  public void testGetExpr()
  {
    Expr expr_a = ba.getExpr();
    Expr expr_b = ba0.getExpr();
    Expr expr_c = bb.getExpr();
    Expr expr_d = bc.getExpr();
    Assert.assertTrue(expr_d instanceof BindExpr);
    Assert.assertNotNull(expr_a);
    Assert.assertNotNull(expr_d);
    Assert.assertEquals(expr_a,expr_b);
    Assert.assertFalse(expr_c.equals(expr_d));
  }

}
