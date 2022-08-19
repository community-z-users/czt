package net.sourceforge.czt.z2alloy.test;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.Scanner;

import net.sourceforge.czt.z2alloy.Main;

import org.junit.Test;

public class Z2AlloyTest {
  /** tests a single given type */
  @Test
  public void testGiven1() {
    test("given1", true);
  }

  /** tests more than one given type */
  @Test
  public void testGiven2() {
    test("given2", true);
  }

  /** tests a free type */
  @Test
  public void testFree1() {
    test("free1", true);
  }

  /** tests a schema which which declares a variable of a free type */
  @Test
  public void testSchema1() {
    test("schema1", true);
  }

  /**
   * tests a schema which declares a variable of a schema. This doesn't work
   * with unfolding
   */
  @Test
  public void testSchema2() {
    test("schema2", false);
  }

  /** tests a schema which includes a schema */
  @Test
  public void testSchema3() {
    test("schema3", true);
  }
  
  /** tests schema conjunction, disjunction, implication and equivalence */
  @Test
  public void testSchema4() {
    test("schema4", false);
  }

  /** tests a schema with an equality constraint */
  @Test
  public void testEquality1() {
    test("equality1", true);
  }

  /** tests logical and, or, not, implication, iff */
  @Test
  public void testBooleanOperators1() {
    test("booleanoperators1", true);
  }

  /** tests simple the use of delta/xi in a schema */
  @Test
  public void testDelta1() {
    test("delta1", true);
  }
  
  /** tests numerical operators */
  @Test
  public void testNumbers1() {
    test("numbers1", true);
  }
  
  /** tests simple quantification predicates */
  @Test
  public void testQuantifiers1() {
    test("quantifiers1", true);
  }

  /**
   * tests quantifier predicates which include schemas in various places
   */
  @Test
  public void testQuantifier2() {
    test("quantifiers2", false);
  }
 
  /**
   * tests quantifier expressions
   */
  @Test
  public void testQuantifiers3() {
    test("quantifiers3", false);
  }
  
  /** tests simple theta expressions
   * this is actually a really bad test because it shows up that alloy uses atoms
   */
  @Test
  public void testTheta1() {
    test("theta1", false);
  }

  /*
   * These are old tests - they don't work because of changes to the printer
   * they should be cleaned up, fixed up and included above ASAP
   * 
   * @Test public void testOld1() { test("AB", false); }
   * 
   * @Test public void testOld2() { test("st", false); }
   * 
   * @Test public void testOld3() { test("quant", false); }
   * 
   * @Test public void testOld4() { test("box_office", false); }
   * 
   * @Test public void testOld5() { test("seq", false); }
   * 
   * @Test public void testOld6() { test("front_last", false); }
   * 
   * @Test public void testOld7() { test("bst", false); }
   * 
   * @Test public void testOld8() { test("Unix", false); }
   * 
   * @Test public void testOld9() { test("substitution", false); }
   * 
   * @Test public void testOld10() { test("hidig", false); }
   * 
   * @Test public void testOld11() { test("theta", false); }
   * 
   * @Test public void testOld12() { test("comprehension", false); }
   * 
   * @Test public void testOld13() { test("schemaquant", false); }
   * 
   * @Test public void testOld14() { test("composition", false); }
   */

  public void test(String fileName, boolean testUnfolding) {
    assertTrue(equal(fileName, false));
    if (testUnfolding) {
      assertTrue(equal(fileName, true));
    }
  }

  public boolean equal(String fileName, boolean unfolding) {
    try {
        Scanner translate = new Scanner(Main.print(Main.translate(new File(
                getClass().getResource("/" + fileName + ".tex").toURI()), unfolding)));
            Scanner read = new Scanner(new File(getClass().getResource(
                "/" + fileName + (unfolding ? "_unfold" : "_fold") + ".als").toURI()));
    	try{
      while (translate.hasNext() && read.hasNext()) {
        String t1 = translate.nextLine();
        String t2 = read.nextLine();
        if (!t1.equals(t2)) {
          throw new RuntimeException(t1 + " vs " + t2);
        }
      }
      if (translate.hasNext())
        throw new RuntimeException("error translate: " + translate.next());
      if (read.hasNext())
        throw new RuntimeException("error read: " + read.next());
      return (translate.hasNext() == read.hasNext());
    	}
    	finally{
      translate.close();
      read.close();}
    	
    } catch (URISyntaxException e) {
      throw new RuntimeException(e);
    } catch (Exception e) {
      System.err.println(fileName);
      throw new RuntimeException(e);
    }
  }

}
