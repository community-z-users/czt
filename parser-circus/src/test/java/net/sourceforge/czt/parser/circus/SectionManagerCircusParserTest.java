/*
 * SectionManagerCircusParserTest.java
 * JUnit based test
 *
 * Created on 14 May 2007, 14:59
 */

package net.sourceforge.czt.parser.circus;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import junit.framework.*;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author leo
 */
public class SectionManagerCircusParserTest extends TestCase
{
  
 // true => looks into tests/circus/debug/*.tex;
  // false=> looks into tests/circus/*.tex
  protected static boolean DEBUG_TESTING = true;
  
  // true => executes the printing tests, which will reparse and print files.
  protected static boolean TESTING_PRINTING = false;
  
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : Level.OFF;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();
  protected static ParseErrorLogging pel_;
  protected static ParseErrorLogging pelsm_;
  
  static {      
      if (DEBUG_TESTING) {
        //pel_ = new ParseErrorLogging(Parser.class, DEBUG_LEVEL);
        //pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
        TESTS_SOURCEDIR.add("tests/circus/debug");        
      } else {
        TESTS_SOURCEDIR.add("tests/circus");
        // If not debugging testing, then do not do logging.
        pel_ = null;
        pelsm_ = null;
      }
  }
  
  public SectionManagerCircusParserTest(String testName)
  {
    super(testName);
  }
  
  private List<File> files_;
  private SectionManager manager_;
  
  protected void collectTestFiles(List<String> directoryNames) 
  {
    for(String dirName : directoryNames) {
      collectTestFiles(dirName);
    }
  }
  
  private void collectTestFiles(String directoryName)
  {
    String cztHome = System.getProperty("czt.home");
    //System.out.println("CZT-HOME = " + cztHome);
    if (cztHome == null || cztHome.length() == 0)
    {
      cztHome = manager_.getProperty("czt.path");
      //System.out.println("CZT-PATH = " + cztHome);
      if (cztHome == null)
      { cztHome = ""; }
    }
    String fullDirectoryName = cztHome + directoryName;
    System.out.println("Full directory name = " + fullDirectoryName);
    File directory = new File(fullDirectoryName);
    File[] files = null;
    if (! directory.isDirectory())
    {
      URL url = getClass().getResource("/");
      if (url != null)
      {
        System.out.println("Looking for tests under: " + url.getFile() + fullDirectoryName);
        directory = new File(url.getFile() + fullDirectoryName);
        if (! directory.isDirectory())
        {
          System.out.println("No tests to perform on " + directory.getAbsolutePath());
        }
        else
        {
          files = directory.listFiles();
        }
      }
      else
      {
        fail("Could not retrieve a valid testing set under " + directory.getAbsolutePath());
      }
    }
    else
    {
      files = directory.listFiles();
    }
    if (files != null)
    {
      for (File file : files)
      {
        files_.add(file);
      }
    }
  }
  
  protected void setUp() throws Exception
  {
    files_ = new ArrayList<File>();
    manager_ = new SectionManager("circus");
    //collectTestFiles(TESTS_SOURCEDIR);
  }
  
  // TODO add test methods here. The name must begin with 'test'. For example:
  // public void testHello() {}
  
  public void testSectionManagerParse()
  {
    if (!files_.isEmpty())
    {
      for(File file : files_)
      {
        System.out.println("Results for "+file.getAbsolutePath());
        Key k = new Key(file.getAbsolutePath(), LatexString.class);
        Key k2 = new Key(file.getAbsolutePath(), UnicodeString.class);
        System.out.println("HERE:================================================================");
        try
        {
          LatexString ls = (LatexString)manager_.get(k);
          //UnicodeString ls = (UnicodeString)manager_.get(k2);
          System.out.println(ls.toString());
          System.out.println("HERE:================================================================");
          // For now do it only once.
          return ;
        }
        catch(CommandException c)
        {
          printCauses(c);
        }
      }
      fail("Could not use the section manager to parse/print/parse.");
    }
  }
  
  protected void printCauses(Throwable e)
  {
    e.printStackTrace();
    if (e.getCause() != null) printCauses(e.getCause());
  }
}
