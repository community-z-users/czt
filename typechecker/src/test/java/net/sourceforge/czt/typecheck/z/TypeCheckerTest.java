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
import java.util.ArrayList;
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
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;

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
  implements TypecheckPropertiesKeys
{
  //allow use before declaration
  protected boolean useBeforeDecl_ = false;

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    TypeCheckerTest checkerTest = new TypeCheckerTest(false);
    checkerTest.collectTests(suite, "z/");
    checkerTest = new TypeCheckerTest(true);
    checkerTest.collectTests(suite, "z/useBeforeDecl/");
    return suite;
  }

  public TypeCheckerTest(boolean useBeforeDecl)
  {
    useBeforeDecl_ = useBeforeDecl;
  }

  //test all the files from a directory
  protected void collectTests(TestSuite suite, String directoryName)
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
        suite.addTest(new TestError(fullPath, exception));
      }
      //if the file name does not end with error, then we have a
      //normal case
      else if (fileName.endsWith(".tex")) {
        suite.addTest(new TestNormal(fullPath));
      }
    }
  }

  protected SectionManager getManager()
  {
    return new SectionManager();
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
    /*
    Spec spec = (Spec) term;
    String value = useBeforeDecl_ ? "true" : "false";
    manager.setProperty(PROP_TYPECHECK_USE_BEFORE_DECL, value);
    try {
      for (Sect sect : spec.getSect()) {
        if (sect instanceof ZSect) {
          String sectName = ((ZSect) sect).getName();
          Key typekey = new Key(sectName, SectTypeEnvAnn.class);
          manager_.get(typekey);
        }
      }
    }
    catch (CommandException e) {
      if (e.getCause() instanceof TypeErrorException) {
        return ((TypeErrorException) e.getCause()).errors();
      }
      else {
        fail("\nUnexpected CommandException" + e.toString());
      }
    }
    return new ArrayList();
    */
  }

  class TestNormal
    extends TestCase
  {
    private String file_;

    TestNormal(String file)
    {
      file_ = file;
    }

    public void runTest()
    {
      SectionManager manager = getManager();
      List<ErrorAnn> errors = new java.util.ArrayList<ErrorAnn>();
      try {
        Term term = parse(file_, manager);
        errors = typecheck(term, manager);
      }
      catch (RuntimeException e) {
        e.printStackTrace();
        fail("\nUnexpected runtime exception" +
             "\n\tFile: " + file_ +
             "\n\tException: " + e.toString());
      }
      catch (Throwable e) {
	e.printStackTrace();
        fail("\nUnexpected exception" +
             "\n\tFile: " + file_ +
             "\n\tException: " + e.toString());
      }
      if (errors.size() > 0) {
        ErrorAnn errorAnn = errors.get(0);
        fail("\nUnexpected type error" +
             "\n\tFile: " + file_ +
             "\n\tException: " + errorAnn.getErrorMessage().toString() +
	     "\nError: " + errorAnn.toString());
      }
    }
  }

  class TestError
    extends TestCase
  {
    private String file_;
    private String exception_;

    TestError(String file, String exception)
    {
      file_ = file;
      exception_ = exception;
    }

    public void runTest()
    {
      SectionManager manager = getManager();
      Throwable throwable = null;
      List<ErrorAnn> errors = new java.util.ArrayList();
      try {
        Term term = parse(file_, manager);
        if (term == null) {
          fail("Parser returned null");
        }
        else {
          errors = typecheck(term, manager);
        }
      }
      catch (RuntimeException e) {
        e.printStackTrace();
        fail("\nUnexpected runtime exception" +
             "\n\tFile: " + file_ +
             "\n\tException: " + e.toString());
      }
      catch (Throwable e) {
        fail("\nUnexpected exception" +
             "\n\tFile: " + file_ +
             "\n\tException: " + e.toString());
      }
      if (errors.size() == 0) {
        fail("\nNo type error found" +
             "\n\tFile: " + file_ +
             "\n\tExpected: " + exception_);
      }
      else {
        ErrorAnn errorAnn = errors.get(0);
        String actual =
          removeUnderscore(errorAnn.getErrorMessage().toString());
        if (exception_.compareToIgnoreCase(actual) != 0) {
          incorrectError(actual);
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

    private void incorrectError(String error)
    {
      fail("\nIncorrect type error" +
           "\n\tFile: " + file_ +
           "\n\tError: " + exception_ +
           "\n\tActual: " + error);
    }
  }
}
