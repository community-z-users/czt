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
import java.net.URL;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.session.*;

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

  //allow recursive types
  protected boolean recursiveTypes_ = false;

  protected final static String TEST_DIR =
    "/net/sourceforge/czt/typecheck/tests/";

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    TypeCheckerTest checkerTest = new TypeCheckerTest(false, false);
    checkerTest.collectTests(suite,
           TypeCheckerTest.class.getResource(TEST_DIR + "z/"));

    checkerTest = new TypeCheckerTest(true, false);
    checkerTest.collectTests(suite,
           TypeCheckerTest.class.getResource(TEST_DIR + "z/"));

    checkerTest = new TypeCheckerTest(false, true);
    checkerTest.collectTests(suite,
			     TypeCheckerTest.class.getResource(TEST_DIR + "z/recursiveTypes/"));

    checkerTest = new TypeCheckerTest(true, false);
    checkerTest.collectTests(suite,
			     TypeCheckerTest.class.getResource(TEST_DIR + "z/useBeforeDecl/"));

    return suite;
  }

  public TypeCheckerTest(boolean useBeforeDecl, boolean recursiveTypes)
  {
    useBeforeDecl_ = useBeforeDecl;
    recursiveTypes_ = recursiveTypes;
  }

  /**
   * Tests all the files from a directory.
   */
  protected void collectTests(TestSuite suite, URL url)
  {
    try {
      String protocol = url.getProtocol();
      if (! "file".equals(protocol)) {
	throw new IllegalArgumentException("Unsupported Protocol");
      }
      final File dir = new File(url.getFile());
      String[] content = dir.list();
      for (String name : content) {
	//if the file name ends with error, then we have a case with
	//the typechecker should throw the exception specified at the
	//start of the filename
	if (name.endsWith(".error")) {
	  int index = name.indexOf("-");
	  if (index < 1) {
	    fail(name + " does not specify an exception name");
	  }
	  String exception = name.substring(0, index);
	  suite.addTest(new TestError(new URL(url, name), exception));
	}
	//if the file name does not end with error, then we have a
	//normal case
	else if (name.endsWith(".tex")) {
	  suite.addTest(new TestNormal(new URL(url, name)));
	}
      }
    }
    catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  protected SectionManager getManager()
  {
    return new SectionManager();
  }

  protected Term parse(URL url, SectionManager manager)
    throws Exception
  {
    Source source = new UrlSource(url);
    source.setMarkup(Markup.LATEX);
    manager.put(new Key<Source>(url.toString(), Source.class), source);
    return manager.get(new Key<Spec>(url.toString(), Spec.class));
  }

  protected List<? extends ErrorAnn> typecheck(Term term,
					       SectionManager manager)
    throws Exception
  {
    return TypeCheckUtils.typecheck(term, manager, 
				    useBeforeDecl_, recursiveTypes_);
  }

  class TestNormal
    extends TestCase
  {

    private URL url_;

    TestNormal(URL url)
    {
      url_ = url;
    }

    public void runTest()
    {
      SectionManager manager = getManager();
      List<? extends ErrorAnn> errors = new ArrayList<ErrorAnn>();
      Term term = null;
      try
      {
	//        System.out.println("Test normal: " + url_);
        term = parse(url_, manager);
        errors = typecheck(term, manager);
      }
      catch (RuntimeException e)
      {
        e.printStackTrace();
        fail("\nUnexpected runtime exception" +
          "\n\tFile: " + url_ +
          "\n\tException: " + e.toString());
      }
      catch (Throwable e)
      {
        e.printStackTrace();
        fail("\nUnexpected exception" +
          "\n\tFile: " + url_ +
          "\n\tException: " + e.toString());
      }
      if (errors.size() > 0)
      {
        ErrorAnn errorAnn = errors.get(0);
        fail("\nUnexpected type error" +
          "\n\tFile: " + url_ +
          "\n\tException: " + errorAnn.getErrorMessage().toString() +
          "\nError: " + errorAnn.toString());
      }
    }
  }

  class TestError
    extends TestCase
  {

    private URL url_;
    private String exception_;

    TestError(URL url, String exception)
    {
      url_ = url;
      exception_ = exception;
    }

    public void runTest()
    {
      SectionManager manager = getManager();
      List<? extends ErrorAnn> errors = new ArrayList<ErrorAnn>();
      try
      {
	//        System.out.println("Test error: " + url_);
        Term term = parse(url_, manager);
        if (term == null)
        {
          fail("Parser returned null");
        }
        else
        {
          errors = typecheck(term, manager);
        }
      }
      catch (RuntimeException e)
      {
        e.printStackTrace();
        fail("\nUnexpected runtime exception" +
          "\n\tFile: " + url_ +
          "\n\tException: " + e.toString());
      }
      catch (Throwable e)
      {
        fail("\nUnexpected exception" +
          "\n\tFile: " + url_ +
          "\n\tException: " + e.toString());
      }
      if (errors.size() == 0)
      {
        fail("\nNo type error found" +
          "\n\tFile: " + url_ +
          "\n\tExpected: " + exception_);
      }
      else
      {
        ErrorAnn errorAnn = errors.get(0);
        String actual =
          removeUnderscore(errorAnn.getErrorMessage().toString());
        if (exception_.compareToIgnoreCase(actual) != 0)
        {
          incorrectError(actual);
        }
      }
    }

    private String removeUnderscore(String string)
    {
      String result = new String();
      for (int i = 0; i < string.length(); i++)
      {
        char c = string.charAt(i);
        if (c != '_')
        {
          result += c;
        }
      }
      return result;
    }

    private void incorrectError(String error)
    {
      fail("\nIncorrect type error" +
        "\n\tFile: " + url_ +
        "\n\tError: " + exception_ +
        "\n\tActual: " + error);
    }
  }
}
