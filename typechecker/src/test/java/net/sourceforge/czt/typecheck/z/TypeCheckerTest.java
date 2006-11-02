/**
Copyright (C) 2004, 2005 Tim Miller
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.typecheck.z;

import java.io.*;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.ParseUtils;

import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.util.SectTypeEnv;

import net.sourceforge.czt.typecheck.testutil.TypeParser;

/**
 * A JUnit test class for testing the typechecker. This reads any
 * files not ending with a "_" from the directory tests/z.
 *
 * If the file ends with ".error", then the test reads everything up
 * to the first "-" and that is the name of the error constant.
 *
 * If the file does not end in ".error" or "_", then no error is
 * expected.
 *
 * @author Tim Miller
 */
public class TypeCheckerTest
  extends TestCase
{
  //the section manager
  protected SectionManager manager_ = getManager();

  //allow use before declaration
  protected boolean useBeforeDecl_ = false;

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(TypeCheckerTest.class);
    return suite;
  }

  protected SectionManager getManager()
  {
    return new SectionManager();
  }

  protected void setUp()
  {
    CztLogger.getLogger(manager_.getClass()).setLevel(Level.OFF);
  }

  public void testZ()
  {
    useBeforeDecl_ = false;
    testDirectory("z/");
  }

  public void testZUseBeforeDecl()
  {
    useBeforeDecl_ = true;
    testDirectory("z/useBeforeDecl/");
  }

  //test all the files from a directory
  protected void testDirectory(String directoryName)
  {
    String cztHome = System.getProperty("czt.home");
    String fullDirectoryName =
      cztHome + "/typechecker/tests/" + directoryName;
    File directory = new File(fullDirectoryName);
    if (! directory.isDirectory()) {
      directory =
        new File(getClass().getResource("/" + directoryName).getFile());
    }
    File[] files = directory.listFiles();
    for (int i = 0; i < files.length; i++) {
      manager_.reset();
      String fileName = files[i].getName();
      String fullPath = files[i].getAbsolutePath();
      //if the file name ends with error, then we have a case with
      //the typechecker should throw the exception specified at the
      //start of the filename
      if (fileName.endsWith(".error")) {
        int index = fileName.indexOf("-");
        if (index < 1) {
          fail(fileName + " does not specify an exception name");
        }
        String exception = fileName.substring(0, index);
        handleException(fullPath, exception);
      }
      //if the file name does not end with error, then we have a
      //normal case
      else if (fileName.endsWith(".tex")) {
        handleNormal(fullPath);
      }
    }
  }

  protected Term parse(String file, SectionManager manager)
    throws Exception
  {
    Source source = new FileSource(file);
    source.setMarkup(Markup.LATEX);
    manager.put(new Key(file, Source.class), source);
    return (Term) manager.get(new Key(file, Spec.class));
  }

  protected List typecheck(Term term, SectionManager manager)
    throws Exception
  {
    return TypeCheckUtils.typecheck(term, manager, useBeforeDecl_);
  }

  protected void handleNormal(String file)
  {
    List<ErrorAnn> errors = new java.util.ArrayList<ErrorAnn>();
    try {
      Term term = parse(file, manager_);
      errors = typecheck(term, manager_);
    }
    catch (RuntimeException e) {
      e.printStackTrace();
      fail("\nUnexpected runtime exception" +
           "\n\tFile: " + file +
           "\n\tException: " + e.toString());
    }
    catch (Throwable e) {
      fail("\nUnexpected exception" +
           "\n\tFile: " + file +
           "\n\tException: " + e.toString());
    }

    if (errors.size() > 0) {
      ErrorAnn errorAnn = errors.get(0);
      fail("\nUnexpected type error" +
           "\n\tFile: " + file +
           "\n\tException: " + errorAnn.getErrorMessage().toString());
    }
  }

  protected void handleException(String file,
                                 String exception)
  {
    Throwable throwable = null;
    List<ErrorAnn> errors = new java.util.ArrayList();
    try {
      Term term = parse(file, manager_);
      if (term == null) {
        fail("Parser returned null");
      }
      else {
        errors = typecheck(term, manager_);
      }
    }
    catch (RuntimeException e) {
      e.printStackTrace();
      fail("\nUnexpected runtime exception" +
           "\n\tFile: " + file +
           "\n\tException: " + e.toString());
    }
    catch (Throwable e) {
      fail("\nUnexpected exception" +
           "\n\tFile: " + file +
           "\n\tException: " + e.toString());
    }

    if (errors.size() == 0) {
      fail("\nNo type error found" +
           "\n\tFile: " + file +
           "\n\tExpected: " + exception);
    }
    else {
      ErrorAnn errorAnn = errors.get(0);
      String actual = removeUnderscore(errorAnn.getErrorMessage().toString());
      if (exception.compareToIgnoreCase(actual) != 0) {
        incorrectError(file, exception, actual);
      }
    }
  }

  private String removeUnderscore(String string)
  {
    String result = new String();
    for (int i = 0; i < string.length(); i++) {
      char c = string.charAt(i);
      if (c != '_') {
        result += c;
      }
    }
    return result;
  }

  private void incorrectError(String file, String expected, String actual)
  {
    fail("\nIncorrect type error" +
         "\n\tFile: " + file +
         "\n\tError: " + expected +
         "\n\tActual: " + actual);
  }
}
