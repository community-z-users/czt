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
  
  protected static boolean DEBUG_TESTING = true;
  protected static final Level DEBUG_LEVEL = Level.OFF;
  protected static String TESTS_SOURCEDIR = (DEBUG_TESTING ? "tests/circus/debug" : "tests/circus");
  protected static final ParseErrorLogging pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
  
  public SectionManagerCircusParserTest(String testName)
  {
    super(testName);
  }
  
  private List<File> files_;
  private SectionManager manager_;
  
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
