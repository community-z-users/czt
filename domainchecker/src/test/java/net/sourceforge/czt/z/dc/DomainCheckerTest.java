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
import java.io.StringWriter;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/**
 *
 * @author leo
 */
public class DomainCheckerTest extends TestCase
{
  // true => looks into tests/circus/debug/*.tex;
  // false=> looks into tests/circus/*.tex
  protected static boolean DEBUG_TESTING = false;
  
  // true => executes the printing tests, which will reparse and print files.
  protected static boolean TESTING_PRINTING = false;
  
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : Level.OFF;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();
  //protected static final ParseErrorLogging pel_;
  //protected static final ParseErrorLogging pelsm_;
  
  static {      
      if (DEBUG_TESTING) {
        //pel_ = new ParseErrorLogging(Parser.class, DEBUG_LEVEL);
        //pelsm_ = new ParseErrorLogging(SectionManager.class, DEBUG_LEVEL);
        TESTS_SOURCEDIR.add("tests/debug");
      } else {
        TESTS_SOURCEDIR.add("tests/");
        // If not debugging testing, then do not do logging.
        //pel_ = null;
        //pelsm_ = null;
      }
  }

  protected static final SectionManager manager_ = new SectionManager();
  protected static final String lineSeparator_ = System.getProperty("line.separator", "\r\n");

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    DomainCheckerTest dcTest = new DomainCheckerTest();
    dcTest.collectTests(suite, TESTS_SOURCEDIR);        
    System.out.println("Number of (hoppefully) successful tests to run: " + suite.countTestCases());
    return suite;
  }
  
  protected final DomainChecker domainChecker_;
  
  /** Creates a new instance of DomainCheckerTest */
  public DomainCheckerTest()
  {
    domainChecker_ = new DomainChecker();
  }
  
  protected static SectionManager getSectionManager() {
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
    String fullDirectoryName = cztHome + directoryName;
    System.out.println("Full directory name = " + fullDirectoryName);
    File directory = new File(fullDirectoryName);
    File[] files = null;
    if (! directory.isDirectory())
    {
      URL url = getClass().getResource("/");
      if (url != null) {
        System.out.println("Looking for tests under: " + url.getFile() + fullDirectoryName);
        directory = new File(url.getFile() + fullDirectoryName);        
        if (! directory.isDirectory()) {
          System.out.println("No tests to perform on " + directory.getAbsolutePath());            
        } else {
            files = directory.listFiles();
        }       
      } else {
        fail("Could not retrieve a valid testing set under " + directory.getAbsolutePath());
      }
    } else {
        files = directory.listFiles();
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
    private String file_;
    private List<Pair<Para, Pred>> dc_;
    
    protected TestNormal(String file)
    {
      file_ = file;
      dc_ = null;
    }
    
    protected String getFile() {
        return file_;
    }
    
    protected List<Pair<Para, Pred>> getDC() {
        return dc_;
    }
    
    private final boolean PROCESS_PARENTS = false;
    private final boolean ADD_TRIVIAL_DC = false;
    
    protected void innerTest() {
      try
      {
        System.out.println("Retrieving Spec for " + file_);        
        Spec spec = (Spec)manager_.get(new Key(file_, Spec.class));
        if (spec == null)
        {
          fail("Parser returned null (i.e., parsing error)");
        }
        else 
        { 
          System.out.println("Collecting DCs for Spec");    
          domainChecker_.setSectInfo(manager_);
          Spec dcSpec = domainChecker_.createDCSpec(spec, PROCESS_PARENTS, ADD_TRIVIAL_DC);

          StringWriter writer = new StringWriter();
          System.out.println("Printing DC sections for Spec");          
          for(Sect sect : dcSpec.getSect())
          {
            if (sect instanceof ZSect) 
            {
              ZSect zsect = (ZSect)sect;
              domainChecker_.printDCZSect(zsect, writer, Markup.LATEX);
              writer.write("\n\n");
            }
          }          
          
//          for(Pair<Para, Pred> pair : dc_)
//          {            
//            writer.write(i + ") ");  
//            
//            if (ZUtils.isZPara(pair.FIRST))
//            {
//              PrintUtils.printLatex(pair.FIRST, writer, manager_, "standard_toolkit");
//            }   
//            else 
//            {
//              // printLatex does not work for LatexMarkupPara, NarrPara, etc...
//              writer.write(pair.FIRST.toString());
//            }
//            writer.write("\n\tDC= ");
//            PrintUtils.printLatex(pair.SECOND, writer, manager_, "standard_toolkit");
//            writer.write("\n\n\n");
//            i++;
//          }          
//          writer.write("================================================================\n");
          writer.close();
          System.out.println(writer.toString());
          System.out.flush();
          return ;        
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException f)
      {
        printCauses(f);
        fail(lineSeparator_ + "Unexpected parser exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + f.toString());
        f.printErrorList();        
      }
      catch (CommandException g)
      {
        printCauses(g);
        fail(lineSeparator_ + "Unexpected command exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + g.toString());                
      }
      catch (RuntimeException e)
      {
        printCauses(e);
        fail(lineSeparator_ + "Unexpected runtime exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());                
      }
      catch (Throwable e)
      {        
        printCauses(e);
        fail(lineSeparator_ + "Unexpected exception" +
            lineSeparator_ + "\tFile: " + file_ +
            lineSeparator_ + "\tException: " + e.toString());        
      }
      fail("Test terminated without a result and without failing!");
    }
    
    public void runTest()
    {      
      innerTest();
    }
  }
} 


