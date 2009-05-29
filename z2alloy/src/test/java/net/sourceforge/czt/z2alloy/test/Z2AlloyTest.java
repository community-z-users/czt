package net.sourceforge.czt.z2alloy.test;


import static org.junit.Assert.assertTrue;

import java.io.File;
import java.net.URISyntaxException;
import java.util.Scanner;

import net.sourceforge.czt.z2alloy.Main;

import org.junit.Test;

public class Z2AlloyTest
{
  
  @Test
  public void testAB() {
    test("AB");
  }
  
  @Test
  public void testST() {
    test("st");
  }

  @Test
  public void testQuant() {
    test("quant");
  }

  @Test
  public void testBoxOffice() {
    test("box_office");
  }
  
  @Test
  public void testSeq() {
    test("seq");
  }
  
  @Test
  public void testFrontLast() {
    test("front_last");
  }
  
  @Test
  public void bst() {
    assertTrue(equal("bst", false));
  }
  
  @Test
  public void unix() {
	  assertTrue(equal("Unix", false));
  }

  public void test(String fileName) {
    assertTrue(equal(fileName, true));
    assertTrue(equal(fileName, false));
  }

  public boolean equal(String fileName, boolean unfolding) {
	  try {
		Scanner translate = new Scanner(Main.print(Main.translate(new File(getClass().getResource("/" + fileName + ".tex").toURI()), unfolding)));
		Scanner read = new Scanner(new File(getClass().getResource("/" + fileName + (unfolding ? "_unfold" : "_fold") + ".als").toURI()));
				
		while(translate.hasNext() && read.hasNext()) {
			String t1 = translate.nextLine();
			String t2 = read.nextLine();
			if (! t1.equals(t2)) {
				throw new RuntimeException(t1 + " vs " + t2);
			}
		}
		if (translate.hasNext()) throw new RuntimeException("error translate: " + translate.next());
		if (read.hasNext()) throw new RuntimeException("error read: " + read.next());
		return (translate.hasNext() == read.hasNext());
	} catch (URISyntaxException e) {
		throw new RuntimeException(e);
	} catch (Exception e) {
		throw new RuntimeException(e);
	}
  }

}
