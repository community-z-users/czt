package net.sourceforge.czt.animation.test.model;

import java.util.ArrayList;
import java.util.List;

import junit.framework.TestCase;
import net.sourceforge.czt.animation.model.EvalSetResult;
import net.sourceforge.czt.animation.model.Step;
import net.sourceforge.czt.animation.model.StepTree;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.Factory;

public class StepTreeTest extends TestCase
{
  private StepTree tree;
  private Factory factory;
  
  private Step root;
  private Step step1;
  private Step step2;
  
  private BindExpr root_result1;
  private BindExpr step1_result1;
  private BindExpr step1_result2;
  
  /* (non-Javadoc)
   * @see junit.framework.TestCase#setUp()
   */
  public void setUp(){
    factory = new Factory();
    root_result1 = factory.createBindExpr(factory.createZDeclList());
    step1_result1 = factory.createBindExpr(factory.createZDeclList());
    step1_result2 = factory.createBindExpr(factory.createZDeclList());
    
    List<Expr> rootList = new ArrayList<Expr>();
    rootList.add(root_result1);
    root = new Step("initial", new EvalSetResult(rootList));

    List<Expr> step1List = new ArrayList<Expr>();
    step1List.add(step1_result1);
    step1List.add(step1_result2);
    step1 = new Step("add_step_1", new EvalSetResult(step1List));
    
    BindExpr step2_result1 = factory.createBindExpr(factory.createZDeclList());
    BindExpr step2_result2 = factory.createBindExpr(factory.createZDeclList());
    List<Expr> step2List = new ArrayList<Expr>();
    step2List.add(step2_result1);
    step2List.add(step2_result2);
    step2 = new Step("add_step_2", new EvalSetResult(step2List));
    
    tree = new StepTree(root);
    tree.add(step1);
    tree.add(step2);
  }
  
  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.add(Step)'
   */
  public void testAdd()
  {
    assertEquals(tree.getStep(),step2);
    assertEquals(step2.getParent(),step1);
    assertEquals(step1.getParent(),root);
    assertEquals(tree.getRoot(),root);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.moveTo(String)'
   */
  public void testMoveTo()
  {
    tree.setStep(root);
    tree.moveTo("add_step_1");
    assertEquals(tree.getStep(),step1);
    tree.moveTo("add_step_2");
    assertEquals(tree.getStep(),step2);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.changeIndex(int)'
   */
  public void testChangeIndex()
  {
    tree.setStep(step1);
    tree.changeIndex(1);
    assertEquals(step1.getIndex(),1);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.hasPrevious()'
   */
  public void testHasPrevious()
  {
    tree.setStep(step1);
    assertEquals(tree.hasPrevious(),true);
    tree.setStep(root);
    assertEquals(tree.hasPrevious(),false);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.hasNext()'
   */
  public void testHasNext()
  {
    tree.setStep(step1);
    assertEquals(tree.hasNext(),true);
    tree.setStep(step2);
    assertEquals(tree.hasNext(),false);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.size()'
   */
  public void testSize()
  {
    tree.setStep(step1);
    tree.changeIndex(1);
    assertEquals(tree.size(),2);
    tree.setStep(step2);
    assertEquals(tree.size(),1);
  }

  /*
   * Test method for 'net.sourceforge.czt.animation.model.StepTree.isComplete()'
   */
  public void testIsComplete()
  {
    tree.setStep(step1);
    tree.changeIndex(1);
    assertEquals(tree.isComplete(),true);
    tree.setStep(step2);
    assertEquals(tree.isComplete(),false);
  }

}
