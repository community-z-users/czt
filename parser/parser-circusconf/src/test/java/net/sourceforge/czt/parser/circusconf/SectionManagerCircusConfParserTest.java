/*
 * SectionManagerCircusParserTest.java
 * JUnit based test
 *
 * Created on 14 May 2007, 14:59
 */

package net.sourceforge.czt.parser.circusconf;

import java.io.File;
import java.io.UnsupportedEncodingException;
import java.net.URL;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import junit.framework.TestCase;
import net.sourceforge.czt.parser.circus.ParseErrorLogging;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;

/**
 *
 * @author leo
 */
public class SectionManagerCircusConfParserTest extends TestCase
{
  
 // true => looks into tests/circusconf/debug/*.tex;
  // false=> looks into tests/circusconf/*.tex
  protected static boolean DEBUG_TESTING = true;
  
  // true => executes the printing tests, which will reparse and print files.
  protected final static boolean VERBOSE = false;
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : VERBOSE ? Level.WARNING : Level.SEVERE;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();
  protected static ParseErrorLogging pel_;
  protected static ParseErrorLogging pelsm_;
  
  static {      
      if (DEBUG_TESTING) {
        //pel_ = new ParseErrorLogging(Parser.class, DEBUG_LEVEL);
        //pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
        TESTS_SOURCEDIR.add("tests/circusconf/debug");        
      } else {
        TESTS_SOURCEDIR.add("tests/circusconf");
        // If not debugging testing, then do not do logging.
        pel_ = null;
        pelsm_ = null;
      }
  }
  
  public SectionManagerCircusConfParserTest(String testName)
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
    if (VERBOSE) { System.out.println("Full directory name = " + fullDirectoryName); }
    File directory = new File(fullDirectoryName);
    File[] files = null;
    if (! directory.isDirectory())
    {
      URL url = getClass().getResource("/");
      if (url != null)
      {
        try {
          String urlPath = URLDecoder.decode(url.getFile(), "UTF-8");
          if (VERBOSE) { System.out.println("Looking for tests under: " + urlPath + fullDirectoryName); }
          directory = new File(urlPath + fullDirectoryName);
        } catch (UnsupportedEncodingException e) {
          throw new RuntimeException(e);
        }
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
  
  @Override
  protected void setUp() throws Exception
  {
    files_ = new ArrayList<File>();
    manager_ = new SectionManager(Dialect.CIRCUSCONF);
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
        if (VERBOSE) { System.out.println("Results for "+file.getAbsolutePath()); }
        Key<LatexString> k = new Key<LatexString>(file.getAbsolutePath(), LatexString.class);
        //Key<UnicodeString> k2 = new Key<UnicodeString>(file.getAbsolutePath(), UnicodeString.class);
        if (VERBOSE) { System.out.println("HERE:================================================================"); }
        try
        {
          LatexString ls = manager_.get(k);
          //UnicodeString ls = manager_.get(k2);
          if (VERBOSE) { System.out.println(ls.toString());
           System.out.println("HERE:================================================================"); }
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
