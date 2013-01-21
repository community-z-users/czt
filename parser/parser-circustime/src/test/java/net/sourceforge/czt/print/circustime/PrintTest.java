/*
 * PrintTest.java
 *
 * Created on 01 May 2007, 13:22
 *
 * To change this template, choose Tools | Template Manager
 * and open the template in the editor.
 */

package net.sourceforge.czt.print.circustime;

import java.io.File;
import java.io.FileWriter;
import java.util.logging.Level;
import junit.framework.Test;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.circus.ParserTest;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;

/**
 *
 * @author leo
 */
public class PrintTest  extends ParserTest
{
  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    PrintTest printTests = new PrintTest();
    printTests.collectTests(suite, TESTS_SOURCEDIR);        
    if (VERBOSE) { System.out.println("Number of successful tests to run: " + suite.countTestCases()); }
    //if (VERBOSE) {
    System.out.println("\t\tCircus printing testing skipped - AST2PrintTree not yet complete");
            //}
    return suite;
  }
  
  @Override
  protected void collectTest(TestSuite suite, File file)
  {       
     
    //super.collectTest(suite, file);
  }
  
  protected FileWriter print(Term term, String file) throws Exception
  {      
    assert term != null && file != null;
    FileWriter writer = new FileWriter(file);    
    System.out.println("Printing " + file);        
    PrintUtils.printLatex(term, writer, getSectionManager());
    if (DEBUG_TESTING && DEBUG_LEVEL.intValue() <= Level.INFO.intValue()) {
        System.out.flush();
        System.out.println("DEBUG: AFTER PRINTING, saved to " + file);                
        System.out.flush();
    }    
    return writer;
  }
  
  @Override
  protected TestNormal createTestCase(String name) {
      return new TestNormal(name);
  }
  
  public static final String PRINT_LATEX_EXT = ".print";
  
  protected class TestNormal extends ParserTest.TestNormal
  {
    protected TestNormal(String file)
    {
      super(file);
    }
  
    @Override
    protected String getFile() {
        return super.getFile() + PRINT_LATEX_EXT;
    }
    
    @Override
    public void runTest()
    { 
      // parse the file
      if (VERBOSE) { System.out.println("PARSING FOR PRINTING"); }
      innerTest();
      assertTrue("Could not parse file " + super.getFile() + " for printing", getTerm() != null);
      
      try
      {
        if (VERBOSE) { System.out.println("PREPARING FOR PRINTING"); }
        FileWriter writer = print(getTerm(), getFile());
        if (writer == null)
        {
          fail("Printer returned null writer (i.e., printing error)");
        }
        writer.close();
      }            
      catch (net.sourceforge.czt.util.CztException f)
      {
        printCauses(f);
        fail(lineSeparator_ + "Unexpected print exception" +
            lineSeparator_ + "\tFile: " + getFile() +
            lineSeparator_ + "\tException: " + f.toString());               
      }
      catch (RuntimeException e)
      {
        printCauses(e);
        fail(lineSeparator_ + "Unexpected runtime exception" +
            lineSeparator_ + "\tFile: " + getFile() +
            lineSeparator_ + "\tException: " + e.toString());                
      }
      catch (Throwable e)
      {        
        printCauses(e);
        fail(lineSeparator_ + "Unexpected exception" +
            lineSeparator_ + "\tFile: " + getFile() +
            lineSeparator_ + "\tException: " + e.toString());        
      }
    }
  }
}
