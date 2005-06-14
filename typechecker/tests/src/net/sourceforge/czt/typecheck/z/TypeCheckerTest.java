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

import java.io.IOException;
import java.util.Iterator;
import java.util.List;
import java.io.*;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

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
  protected SectionManager manager_;

  public static Test suite()
  {
    TestSuite suite = new TestSuite();
    suite.addTestSuite(TypeCheckerTest.class);
    return suite;
  }

  protected void setUp()
  {
    manager_ = new SectionManager();
  }

  protected void tearDown()
  {
    //do nothing?
  }

  public void testAll()
  {
    testDirectory("/typechecker/tests/z/");
  }

  //test all the files from a directory
  protected void testDirectory(String directoryName)
  {
    String cztHome = System.getProperty("czt.home");
    String fullDirectoryName = cztHome + directoryName;
    File directory = new File(fullDirectoryName);

    String [] files = directory.list();
    for (int i = 0; i < files.length; i++) {
      String file = files[i];

      //don't check files that end with "_"
      if (file.endsWith(".tex") || file.endsWith(".error")) {
        String fullPath = fullDirectoryName + file;
        //if the file name ends with error, then we have a case with
        //the typechecker should throw the exception specified at the
        //start of the filename
        if (file.endsWith(".error")) {
          int index = file.indexOf("-");
          if (index < 1) {
            fail(file + " does not specify an exception name");
          }
          String exception = file.substring(0, index);
          handleException(fullPath, exception);
        }
        //if the file name does not end with error, then we have a
        //normal case
        else {
          handleNormal(fullPath);
        }
      }
    }
  }

  protected Term parse(String file)
    throws Exception
  {
    return ParseUtils.parseLatexFile(file, manager_);
  }

  protected List typecheck(Term term, Markup markup)
    throws Exception
  {
    return TypeCheckUtils.typecheck(term, manager_, markup);
  }

  protected void handleNormal(String file)
  {
    List<ErrorAnn> errors = new java.util.ArrayList();
    try {
      Term term = parse(file);
      Markup markup = ParseUtils.getMarkup(file);
      errors = typecheck(term, markup);
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
      Term term = parse(file);
      if (term == null) {
        fail("Parser returned null");
      }
      else {
	Markup markup = ParseUtils.getMarkup(file);
        errors = typecheck(term, markup);
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
