package net.sourceforge.czt.z2alloy.test;


import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.PrintStream;
import java.util.Scanner;

import net.sourceforge.czt.z2alloy.Main;
import net.sourceforge.czt.z2alloy.Z2Alloy;

import org.junit.Test;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.parser.Module;

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
    assertTrue(equalOutput("bst", false));
  }

  public void test(String fileName) {
    assertTrue(equal(fileName, true));
    assertTrue(equal(fileName, false));
    assertTrue(equalOutput(fileName, true));
    assertTrue(equalOutput(fileName, false));
  }

  public boolean equal(String fileName, boolean unfolding) {
    try {
      Z2Alloy z2alloy = createZ2Alloy(fileName + ".tex", unfolding);
      
      // CompUtil.parseEverything_FromFile needs a string, but it comes from inside jar, so has a url
      // write the file, then pass the fileName
      // delete at the end
      File f = new File(getClass().getResource("/" + fileName + (unfolding ? "_unfold" : "_fold")  + ".als").toURI());

      // CompUtil.parseEverything_FromFile needs a string, but it comes from inside jar, so has a url
      // write the file, then pass the fileName
      // delete at the end

      File temp = new File(fileName + ".als");
      
      PrintStream out = new PrintStream(temp);
      Scanner s = new Scanner(f);
      
      while (s.hasNext()) out.println(s.nextLine());
      out.close();
      
      Module module = createModule(fileName + ".als");
      temp.delete();
      
      return AlloyEquality.equals(z2alloy, module);
    }
    catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  public boolean equalOutput(String fileName, boolean unfolding) {
    try {
      Z2Alloy z2alloy = createZ2Alloy(fileName + ".tex", unfolding);

      File f = new File(fileName + ".als");

      PrintStream out = new PrintStream(f);
      out.println(Main.print(z2alloy));
      out.close();

      Module module = createModule(fileName + ".als");

      f.delete();
      return AlloyEquality.equals(z2alloy, module);
    }
    catch (Exception e) {
      throw new RuntimeException(e);
    }
  }

  private Z2Alloy createZ2Alloy(String fileName, boolean unfolding) throws Exception {
    return Main.translate(new File(getClass().getResource("/" + fileName).toURI()), unfolding);
  }

  private Module createModule(String fileName) throws Exception {
    A4Reporter rep = new A4Reporter();

    // Parse+typecheck the model
    Module m = CompUtil.parseEverything_fromFile(rep, null, fileName);
    return m;
  }

}
