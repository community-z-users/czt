/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z.dc;

import java.io.File;
import java.io.FileWriter;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.logging.Level;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.print.util.CztPrintString;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Spec;

/**
 * A JUnit test class for testing the domainchecker. This reads any
 * files not ending with a "_" from the directory tests/circus.
 *
 * If the file ends with ".error", then the test reads everything up
 * to the first "-" and that is the name of the error constant.
 *
 * If the file does not end in ".error" or "_", then no error is
 * expected.
 *
 * @author Leo Freitas
 */
public class DomainCheckerTest
  extends TestCase
  implements DomainCheckPropertyKeys
{
  // true => looks into tests/circus/debug/*.tex;
  // false=> looks into tests/circus/*.tex
  protected static boolean DEBUG_TESTING = false; // true;
  // true => executes the printing tests, which will reparse and print files.
  protected static boolean TESTING_PRINTING = false;
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : Level.WARNING;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();

  static
  {
    File shouldDebug = new File("src/test/resources/tests/z/debug-please");
    try
    {
      System.out.println("shouldDebug? \n path = " + shouldDebug.getPath() + "\n abs path = " + shouldDebug.getAbsolutePath() + "\n can path = " + shouldDebug.getCanonicalPath() + " \n exists? = " + shouldDebug.exists());
    }
    catch (java.io.IOException e)
    {
    }
    DEBUG_TESTING = shouldDebug.exists();
    if (DEBUG_TESTING)
    {
      System.out.println("Debug mode is on");
      TESTS_SOURCEDIR.add("tests/z/debug");
      DEBUG_LEVEL = Level.FINEST;
    }
    else
    {
      System.out.println("Debug mode is off");
      TESTS_SOURCEDIR.add("tests/z");
      DEBUG_LEVEL = Level.WARNING;
    }
  }

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();

    DomainCheckerTest checkerTest = new DomainCheckerTest();
    checkerTest.collectTests(suite, TESTS_SOURCEDIR);
    return suite;
  }
  
  protected final DomainChecker domainChecker_;
  private final SectionManager manager_;
  
  /** Creates a new instance of DomainCheckerTest */
  public DomainCheckerTest()
  {
    manager_ = new SectionManager();
    domainChecker_ = new DomainChecker(manager_);
    domainChecker_.setAddingTrivialDC(manager_.getBooleanProperty(PROP_DOMAINCHECK_ADD_TRIVIAL_DC));
    domainChecker_.setProcessingParents(manager_.getBooleanProperty(PROP_DOMAINCHECK_PROCESS_PARENTS));
    domainChecker_.setInfixAppliesTo(manager_.getBooleanProperty(PROP_DOMAINCHECK_USE_INFIX_APPLIESTO));    
    for(String section : manager_.getListProperty(PROP_DOMAINCHECK_PARENTS_TO_IGNORE))
    {
      domainChecker_.addParentSectionToIgnore(section);
    }    
  }
  
  protected SectionManager getSectionManager() {
      return manager_;
  }
  
  // Tim's directory search structe testing strategy :)
  
  protected void collectTest(TestSuite suite, File file) 
  {
    String fileName = file.getName();
    if (fileName.indexOf("-errors") == -1 && fileName.endsWith(".tex"))
    {
      suite.addTest(createTestCase(file.getAbsolutePath()));
    }
  }
  
  protected void collectTests(TestSuite suite, List<String> directoryNames) 
  {
    for(String dirName : directoryNames) {
      collectTests(suite, dirName);
    }
  }
  
  //test all the files from a directory
  private void collectTests(TestSuite suite, String directoryName)
  {
    String cztHome = System.getProperty("czt.home");
    //System.out.println("CZT-HOME = " + cztHome);
    if (cztHome == null || cztHome.length() == 0)
    {
      cztHome = manager_.getProperty("czt.path");
      //System.out.println("CZT-PATH = " + cztHome);
      if (cztHome == null) { cztHome = ""; }
    }
    // if it is a list of directories...
    List<String> paths = Arrays.asList(cztHome);
    if (cztHome != null && cztHome.indexOf(';') != -1)
    {
      paths = Arrays.asList(cztHome.split(";"));
    }        
    File[] files = null;
    for(String path : paths)
    {
      String fullDirectoryName = path.trim() + (!path.isEmpty() ? "\\" : "") + directoryName;
      System.out.println("Full directory name = " + fullDirectoryName);
      File directory = new File(fullDirectoryName);      
      if (!directory.isDirectory())
      {
        URL url = getClass().getResource("/");
        if (url != null) {
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
          break;
        } 
        else 
        {
          fail("Could not retrieve a valid testing set under " + directory.getAbsolutePath());
        }
      } 
      else {
        files = directory.listFiles();
        break;
      }
    }
    if (files != null) {
        for (File file : files)
        {
          collectTest(suite, file);
        }    
    }
  }
  
  protected void printCauses(Throwable e) {
      e.printStackTrace();
      if (e.getCause() != null) printCauses(e.getCause());
  }

  protected TestNormal createTestCase(String name) {
      return new TestNormal(name);
  }
  
  protected class TestNormal extends TestCase
  {
    private final String file_;
    
    protected TestNormal(String fileme)
    {
      file_ = fileme;
    }
    
    protected String getFileName() {
        return file_;
    }    
    
    protected void innerTest() {
      try
      {                
        System.out.println("Retrieving Spec for " + file_);        
        Spec spec = manager_.get(new Key<Spec>(file_, Spec.class));
        if (spec == null)
        {
          fail("Parser returned null (i.e., parsing error) for " + file_);
        }
        else 
        { 
          System.out.println("Collecting DCs for Spec");          
          Spec dcSpec = domainChecker_.createDCSpec(spec);
          
          Markup markup = Markup.getMarkup(file_);
          CztPrintString output;
          switch (markup)
          {
            case LATEX:
              output = manager_.get(new Key<LatexString>(file_, LatexString.class));
              break;
            case UNICODE:
              output = manager_.get(new Key<UnicodeString>(file_, UnicodeString.class));
              break;
            case ZML:
              output = manager_.get(new Key<XmlString>(file_, XmlString.class));
              break;
            default: 
              fail("Invalid file name extension. Could not retrieve its markup format to produce DC section.");
              return ;
          }          
          int dotIdx = file_.lastIndexOf(".");
          assert dotIdx != -1; // true since getMarkup would fail/return otherwise
          String fileName = file_.substring(0, dotIdx) + "_dc" + file_.substring(dotIdx);          
          FileWriter writer = new FileWriter(fileName);
          System.out.println("Printing DC sections for Spec as " + fileName);
          writer.write(output.toString());
          writer.close();          
          return ;        
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException f)
      {
        printCauses(f);
        fail("\nUnexpected parser exception" +
            "\n\tFile: " + file_ +
            "\n\tException: " + f.toString());
        f.printErrorList();        
      }
      catch (CommandException g)
      {
        printCauses(g);
        fail("\nUnexpected command exception" +
            "\n\tFile: " + file_ +
            "\n\tException: " + g.toString());                
      }
      catch (RuntimeException e)
      {
        printCauses(e);
        fail("\nUnexpected runtime exception" +
            "\n\tFile: " + file_ +
            "\n\tException: " + e.toString());                
      }
      catch (Throwable e)
      {        
        printCauses(e);
        fail("\nUnexpected exception" +
            "\n\tFile: " + file_ +
            "\n\tException: " + e.toString());        
      }
      fail("Test terminated without a result and without failing!");
    }
    
    public void runTest()
    {      
      innerTest();
    }
  }
} 


