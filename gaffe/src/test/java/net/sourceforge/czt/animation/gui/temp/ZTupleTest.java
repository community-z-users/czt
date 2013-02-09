package net.sourceforge.czt.animation.gui.temp;

import java.util.ArrayList;
import java.util.ListIterator;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.TupleExpr;

public class ZTupleTest extends TestCase
{

  private ZTuple ta = new ZTuple(new ZGiven("One"),new ZNumber(1));  //("One", 1)
  private ZTuple ta0 = new ZTuple(new ZGiven("One"),new ZNumber(1)); //("One", 1)
  private ZTuple tb = new ZTuple(new ZGiven("Two"),new ZNumber(2));  //("Two", 2)
  private ZTuple tc = new ZTuple(new ZTuple((TupleExpr)ta.getExpr()) //(("One",1),("Two",2))
                                ,new ZTuple((TupleExpr)tb.getExpr())); 
  
  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.hashCode()'
   */
  public void testHashCode()
  {
    Assert.assertEquals(ta.hashCode(),ta0.hashCode());
    Assert.assertNotSame(ta.hashCode(),tb.hashCode());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.ZTuple()'
   */
  public void testZTuple()
  {
    Assert.assertNotNull(new ZTuple().getExpr());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.ZTuple(ZValue, ZValue)'
   */
  public void testZTupleZValueZValue()
  {
    Assert.assertEquals(tc, new ZTuple(new ZTuple(new ZGiven("One"),new ZNumber(1))
                                      ,new ZTuple(new ZGiven("Two"),new ZNumber(2))));
    Assert.assertEquals(tc.get(0),ta);
    Assert.assertEquals(tc.get(1),tb);
    Assert.assertEquals(ta.get(0).toString(),"One");
    Assert.assertEquals(ta.get(1).toString(),"1");
    Assert.assertEquals(tb.get(0).toString(),"Two");
    Assert.assertEquals(tb.get(1).toString(),"2");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.ZTuple(List<ZValue>)'
   */
  public void testZTupleListOfZValue()
  {
    ArrayList<ZValue> valueList = new ArrayList<ZValue>();
    valueList.add(ta);
    valueList.add(ta0);
    valueList.add(tb);
    valueList.add(tc);
    ZTuple listTuple = new ZTuple(valueList);
    Assert.assertEquals(listTuple.get(0),ta);
    Assert.assertEquals(listTuple.get(1),ta0);
    Assert.assertEquals(listTuple.get(2),tb);
    Assert.assertEquals(listTuple.get(3),tc);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.ZTuple(TupleExpr)'
   */
  public void testZTupleTupleExpr()
  {
    TupleExpr te = ta.getExpr();
    ZTuple ta1 = new ZTuple(te);
    Assert.assertSame(ta1.getExpr(),te);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.iterator()'
   */
  public void testIterator()
  {
    ListIterator<ZValue> it = tc.iterator();
    Assert.assertTrue(it.hasNext());
    Assert.assertFalse(it.hasPrevious());
    Assert.assertEquals(it.next(),ta);
    Assert.assertEquals(it.previousIndex(),0);
    Assert.assertEquals(it.next(),tb);
    Assert.assertEquals(it.previousIndex(),1);
    Assert.assertFalse(it.hasNext());
    Assert.assertTrue(it.hasPrevious());
    Assert.assertEquals(it.previous(),tb);
    Assert.assertEquals(it.nextIndex(),1);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.size()'
   */
  public void testSize()
  {
    Assert.assertEquals(ta.size(),2);
    Assert.assertEquals(tb.size(),2);
    Assert.assertEquals(tc.size(),2);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.get(int)'
   */
  public void testGet()
  {
    Assert.assertEquals(ta.get(0).toString(),"One");
    Assert.assertEquals(ta.get(1).toString(),"1");
    Assert.assertEquals(tb.get(0).toString(),"Two");
    Assert.assertEquals(tb.get(1).toString(),"2");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.toString()'
   */
  public void testToString()
  {
    Assert.assertEquals(ta.toString(),ta0.toString());
    Assert.assertNotSame(ta.toString(),tb.toString());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.equals(Object)'
   */
  public void testEqualsObject()
  {
    Assert.assertTrue(ta.equals(ta0));
    Assert.assertFalse(ta.equals(tb));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZTuple.getExpr()'
   */
  public void testGetExpr()
  {
    Expr expr_a = ta.getExpr();
    Expr expr_b = ta0.getExpr();
    Expr expr_c = tb.getExpr();
    Expr expr_d = tc.getExpr();
    Assert.assertTrue(expr_d instanceof TupleExpr);
    Assert.assertNotNull(expr_a);
    Assert.assertNotNull(expr_d);
    Assert.assertEquals(expr_a,expr_b);
    Assert.assertFalse(expr_c.equals(expr_d));
  }

}
