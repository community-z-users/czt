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
package net.sourceforge.czt.dc.z;

import java.io.File;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.logging.Level;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

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
  // true => executes the printing tests, which will reparse and printToFile files.
  protected static boolean TESTING_PRINTING = false;
  protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : Level.WARNING;
  protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();

  static
  {
    File shouldDebug = new File("src/test/resources/tests/z/debug-please");
    try
    {
      System.out.println("shouldDebug? \n\t path = " + shouldDebug.getPath() +
              "\n\t abs path = " + shouldDebug.getAbsolutePath() +
              "\n\t can path = " + shouldDebug.getCanonicalPath() +
              "\n\t exists? = " + shouldDebug.exists());
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
    TestSuite suite = new TestSuite();

    DomainCheckerTest checkerTest = new DomainCheckerTest();
    checkerTest.manager_.setTracing(DEBUG_TESTING);
    checkerTest.collectTests(suite, TESTS_SOURCEDIR);
    return suite;
  }  
  
  private final SectionManager manager_;
  
  /** Creates a new instance of DomainCheckerTest */
  public DomainCheckerTest()
  {
    manager_ = DomainCheckUtils.getDCUtils().getSectionManager(DomainCheckUtils.getDCUtils().getExtension());
  }
  
  protected SectionManager getSectionManager() {
      return manager_;
  }
  
  // Tim's directory search structe testing strategy :)
  
  protected void collectTest(TestSuite suite, File file) 
  {
    String fileName = file.getName();
    if (fileName.indexOf("-errors") == -1 && // don't process -errors file
        fileName.indexOf(DOMAIN_CHECK_CONJECTURE_NAME_SUFFIX) == - 1 && // don't process _dc files for testing
        fileName.endsWith(".tex")) // only process LaTeX files
    {
      suite.addTest(createTestCase(file));
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
    if (cztHome != null && cztHome.indexOf(File.pathSeparatorChar) != -1)
    {
      paths = Arrays.asList(cztHome.split(File.pathSeparator));
    }        
    File[] files = null;
    for(String path : paths)
    {
      String fullDirectoryName = path.trim() + (!path.isEmpty() ? "\\" : "") + directoryName;
      System.out.println("Full directory name = \n\t" + fullDirectoryName);
      File directory = new File(fullDirectoryName);      
      if (!directory.isDirectory())
      {
        URL url = getClass().getResource("/");
        if (url != null) {          
          System.out.println("Looking for tests under: \n\t" + url.getFile() + fullDirectoryName);
          directory = new File(url.getFile() + fullDirectoryName);        
          if (! directory.isDirectory()) 
          {
            System.out.println("No tests to perform on: \n\t" + directory.getAbsolutePath());
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

  protected TestNormal createTestCase(File file) {
      return new TestNormal(file);
  }
  
  protected class TestNormal extends TestCase
  {
    private final String fileName_;
    private final File file_;
    
    protected TestNormal(File file)
    {
      assert file != null;
      file_ = file;
      fileName_ = file.getAbsolutePath();
    }
    
    protected String getFileName() {
        return fileName_;
    }    
    
    protected void innerTest() {
      try
      {             
        String localcztpath = manager_.getProperty("czt.path");        
        if (localcztpath == null || localcztpath.isEmpty())
        {
          localcztpath = file_.getParent();
        }
        else
        {
          localcztpath += File.pathSeparator + file_.getParent();
        }    
        System.out.println("Setting czt.path = " + localcztpath);
        manager_.setProperty("czt.path", localcztpath); 
        // transforms (c:\temp\myfile.tex or tmp/myfile.tex) into myfile
        String resource = DomainCheckUtils.getSourceName(fileName_);
        System.out.println("Retrieving Spec " +  resource + " for \n\t" + fileName_);
        // for parsing, we better fix the source as well for the section manager.
        manager_.put(new Key<Source>(resource, Source.class), new FileSource(file_));
        Spec spec = manager_.get(new Key<Spec>(resource, Spec.class));
        if (spec == null)
        {
          fail("Parser returned null (i.e., parsing error) for " + fileName_);
        }
        else 
        {           
          System.out.println("Setting up section manager to domain check " + resource);
          DomainCheckUtils.getDCUtils().config();
          System.out.println("Collecting DCs for Spec in file \n\t" + fileName_);
          String path = file_.getParent() != null ? file_.getParent() : ".";
          for (Sect sect : spec.getSect())
          {
            if (sect instanceof ZSect)
            {
              ZSect zSect = (ZSect)sect;
              ZSectDCEnvAnn zSectDCEnvAnn = DomainCheckUtils.getDCUtils().calculateZSectDCEnv(zSect);
              DomainCheckUtils.getDCUtils().printToFile(zSectDCEnvAnn, path, Markup.LATEX);
            }
          }
          return ;
        }
      }
      catch (net.sourceforge.czt.parser.util.ParseException f)
      {
        printCauses(f);
        f.printErrorList();
        fail("\nUnexpected parser exception" +
            "\n\tFile: " + fileName_ +
            "\n\tException: " + f.toString());     
      }
      catch (DomainCheckException f)
      {
        printCauses(f);
        fail("\nUnexpected domain check exception" +
            "\n\tFile: " + fileName_ +
            "\n\tException: " + f.toString());
      }
      catch (CommandException g)
      {
        printCauses(g);
        fail("\nUnexpected command exception" +
            "\n\tFile: " + fileName_ +
            "\n\tException: " + g.toString());                
      }
      catch (RuntimeException e)
      {
        printCauses(e);
        fail("\nUnexpected runtime exception" +
            "\n\tFile: " + fileName_ +
            "\n\tException: " + e.toString());                
      }
      catch (Throwable e)
      {        
        printCauses(e);
        fail("\nUnexpected exception" +
            "\n\tFile: " + fileName_ +
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


