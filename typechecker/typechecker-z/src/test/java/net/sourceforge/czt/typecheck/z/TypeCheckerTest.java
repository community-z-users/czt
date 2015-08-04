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

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.Spec;

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
  
  private final SectionManager manager_;
  protected net.sourceforge.czt.base.util.BasePrintVisitor printer_;

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
	  this(Dialect.Z, useBeforeDecl, recursiveTypes);
  }

  public TypeCheckerTest(Dialect dialect, boolean useBeforeDecl, boolean recursiveTypes)
  {
    useBeforeDecl_ = useBeforeDecl;
    recursiveTypes_ = recursiveTypes;
    manager_ = new SectionManager(dialect);
    printer_ = new net.sourceforge.czt.z.util.PrintVisitor();
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
      final File dir = new File(URLDecoder.decode(url.getFile(), "UTF-8"));
      String[] content = dir.list();
      if (content == null) throw new IOException("Couldn't get contents of directory " + dir.getName());
      for (String name : content) {
	//if the file name ends with error, then we have a case with
	//the typechecker should throw the exception specified at the
	//start of the filename
	if (name.endsWith(".error")) {
	  int index = name.indexOf('-');
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
    return manager_;
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

    private final URL url_;

    TestNormal(URL url)
    {
      super("Test normal: " + String.valueOf(url));
      url_ = url;
    }

    @Override
    public void runTest()
    {
      SectionManager manager = getManager();
      List<? extends ErrorAnn> errors = null;
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
      if (errors != null && errors.size() > 0)
      {
        System.out.println("\tfound type errors on normal spec " + this.url_);
        System.out.println("\t"+errors.toString());
        ErrorAnn errorAnn = errors.get(0);
        fail("\nUnexpected type error" +
          "\n\tFile: " + url_ +
          "\n\tException: " + errorAnn.getErrorMessage() +
          "\nError: " + errorAnn.toString());
      }
    }
  }

  class TestError
    extends TestCase
  {

    private final URL url_;
    private final String exception_;

    TestError(URL url, String exception)
    {
      super("Test error - " + exception + ": " + String.valueOf(url));
      url_ = url;
      exception_ = exception;
    }

    @Override
    public void runTest()
    {
      SectionManager manager = getManager();
      List<? extends ErrorAnn> errors = null;
      try
      {
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
      if (errors == null || errors.size() == 0)
      {
        fail("\nNo type error found" +
          "\n\tFile: " + url_ +
          "\n\tExpected: " + exception_);
      }
      else if (errors != null)
      {
        ErrorAnn errorAnn = errors.get(0);
        String actual =
          removeUnderscore(errorAnn.getErrorMessage());
        if (exception_.compareToIgnoreCase(actual) != 0)
        {
          System.out.println("\tfound type error " + actual + " expected " + exception_ + " for " + url_);
          System.out.println("\t"+errors.toString());
          incorrectError(actual);
        }
      }
    }

    private String removeUnderscore(String string)
    {
      StringBuilder result = new StringBuilder();
      for (int i = 0; i < string.length(); i++)
      {
        char c = string.charAt(i);
        if (c != '_')
        {
          result.append(c);
        }
      }
      return result.toString();
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
