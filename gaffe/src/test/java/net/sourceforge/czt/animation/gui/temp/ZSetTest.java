package net.sourceforge.czt.animation.gui.temp;

import java.util.HashSet;
import java.util.ListIterator;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.z.ast.Expr;

public class ZSetTest extends TestCase
{
  private ZSet sa;                //1...99
  private ZSet sa0;               //1...99
  private ZSet sb;                //1...100
  private ZSet sc;                //{1...99},{1...100}
  
  protected void setUp() throws Exception
  {
    super.setUp();
    HashSet<ZValue> tempa = new HashSet<ZValue>();
    for (int i = 0; i<100; i++){
      tempa.add(new ZNumber(i));
    }
    this.sa = new ZSet(tempa);
    this.sa0= new ZSet(tempa); 
    HashSet<ZValue> tempb = new HashSet<ZValue>(tempa);
    tempb.add(new ZNumber(100));
    this.sb = new ZSet(tempb);
    HashSet<ZValue> tempc = new HashSet<ZValue>();
    tempc.add(sa);
    tempc.add(sb);
    this.sc = new ZSet(tempc);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.ZSet()'
   */
  public void testZSet()
  {
    Assert.assertNotNull(new ZSet().getExpr());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.ZSet(Set<? extends ZValue>)'
   */
  public void testZSetSetOfQextendsZValue()
  {
    Assert.assertTrue(sc.contains(sa));
    Assert.assertTrue(sc.contains(sb));
    Assert.assertTrue(sa.contains(new ZNumber(0)));
    Assert.assertTrue(sa.contains(new ZNumber(99)));
    Assert.assertTrue(sb.contains(new ZNumber(0)));
    Assert.assertTrue(sb.contains(new ZNumber(100)));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.ZSet(EvalSet)'
   */
  public void testZSetEvalSet()
  {
    EvalSet es = sa.getExpr();
    ZSet sa1 = new ZSet(es);
    Assert.assertSame(sa1.getExpr(),es);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.iterator()'
   */
  public void testIterator()
  {
    ListIterator<ZValue> it = sc.iterator();
    Assert.assertTrue(it.hasNext());
    Assert.assertFalse(it.hasPrevious());
    Assert.assertEquals(it.next(),sa);
    Assert.assertEquals(it.previousIndex(),0);
    Assert.assertEquals(it.next(),sb);
    Assert.assertEquals(it.previousIndex(),1);
    Assert.assertFalse(it.hasNext());
    Assert.assertTrue(it.hasPrevious());
    Assert.assertEquals(it.previous(),sb);
    Assert.assertEquals(it.nextIndex(),1);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.size()'
   */
  public void testSize()
  {
    Assert.assertEquals(sa.size(),100);
    Assert.assertEquals(sb.size(),101);
    Assert.assertEquals(sc.size(),2);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.contains(ZValue)'
   */
  public void testContains()
  {
    Assert.assertTrue(sa.contains(new ZNumber(0)));
    Assert.assertTrue(sa.contains(new ZNumber(99)));
    Assert.assertFalse(sa.contains(new ZNumber(100)));
    
    Assert.assertTrue(sb.contains(new ZNumber(0)));
    Assert.assertTrue(sb.contains(new ZNumber(100)));
    Assert.assertFalse(sb.contains(new ZNumber(101)));
    
    Assert.assertTrue(sc.contains(sa));
    Assert.assertTrue(sc.contains(sb));
    Assert.assertFalse(sc.contains(sc));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.get(int)'
   */
  public void testGet()
  {
    // Not working. Since HashSet does not hold the sequence
    
    //Assert.assertEquals(sc.get(0),sa);
    //Assert.assertEquals(sc.get(1),sb);
    //Assert.assertEquals(sa.get(0).toString(),"0");
    //Assert.assertEquals(sa.get(99).toString(),"99");
    //Assert.assertEquals(sb.get(0).toString(),"0");
    //Assert.assertEquals(sb.get(100).toString(),"100");
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.getSet()'
   */
  public void testGetSet()
  {
    HashSet<ZValue> tempa = new HashSet<ZValue>();
    for (int i = 0; i<100; i++){
      tempa.add(new ZNumber(i));
    }
    Assert.assertEquals(sa.getSet(),tempa);
    Assert.assertNotSame(sb.getSet(),tempa);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.toString()'
   */
  public void testToString()
  {
    Assert.assertEquals(sa.toString(),sa0.toString());
    Assert.assertNotSame(sa.toString(),sb.toString());
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.equals(Object)'
   */
  public void testEqualsObject()
  {
    Assert.assertTrue(sa.equals(sa0));
    Assert.assertFalse(sa.equals(sb));
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.gui.temp.ZSet.getExpr()'
   */
  public void testGetExpr()
  {
    Expr expr_a = sa.getExpr();
    Expr expr_b = sa0.getExpr();
    Expr expr_c = sb.getExpr();
    Expr expr_d = sc.getExpr();
    Assert.assertTrue(expr_d instanceof EvalSet);
    Assert.assertNotNull(expr_a);
    Assert.assertNotNull(expr_d);
    Assert.assertEquals(expr_a,expr_b);
    Assert.assertFalse(expr_c.equals(expr_d));
  }

}
