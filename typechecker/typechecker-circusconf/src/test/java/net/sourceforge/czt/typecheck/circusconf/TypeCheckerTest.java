/**
Copyright (C) 2004, 2005 Leo Freitas
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
package net.sourceforge.czt.typecheck.circusconf;

import java.io.File;
import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.typecheck.circus.TypeCheckUtils;
import net.sourceforge.czt.util.CztLogger;

/**
 * A JUnit test class for testing the typechecker. This reads any
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
public class TypeCheckerTest
  extends net.sourceforge.czt.typecheck.circus.TypeCheckerTest
{

  // true => looks into tests/circus/debug/*.tex;
  // false=> looks into tests/circus/*.tex
  //protected static boolean DEBUG_TESTING = false; // true;
  // true => executes the printing tests, which will reparse and print files.
  //protected final static boolean VERBOSE = false;
  //protected static Level DEBUG_LEVEL = DEBUG_TESTING ? Level.FINEST : VERBOSE ? Level.WARNING : Level.SEVERE;
  //protected static List<String> TESTS_SOURCEDIR = new ArrayList<String>();

  static
  {
    File shouldDebug = new File("src/test/resources/tests/circusconf/debug-please");
    try
    {
      if (VERBOSE) {
        System.out.println("shouldDebug? \n path = " + shouldDebug.getPath() +
                  "\n abs path = " + shouldDebug.getAbsolutePath() +
                  "\n can path = " + shouldDebug.getCanonicalPath() +
                  " \n exists? = " + shouldDebug.exists());
      }
    }
    catch (java.io.IOException e)
    {
    }
    DEBUG_TESTING = shouldDebug.exists();
    if (DEBUG_TESTING)
    {
      System.out.println("Debug mode is on");
      TESTS_SOURCEDIR.add("tests/circusconf/debug");
      DEBUG_LEVEL = Level.FINEST;
    }
    else
    {
      if (VERBOSE) { System.out.println("Debug mode is off"); }
      TESTS_SOURCEDIR.add("tests/circusconf");
      DEBUG_LEVEL = Level.WARNING;
    }
  }
  
  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();

    TypeCheckerTest checkerTest = new TypeCheckerTest(false);
    checkerTest.collectTests(suite, TESTS_SOURCEDIR);
    return suite;
  }

  public TypeCheckerTest(boolean recursiveTypes)
  {
    this(Dialect.CIRCUSCONF, recursiveTypes);
  }

  public TypeCheckerTest(Dialect dialect, boolean recursiveTypes)
  {
    super(dialect, recursiveTypes);
    printer_ = new net.sourceforge.czt.circusconf.util.PrintVisitor();
  }
    
  @Override
  protected List<? extends net.sourceforge.czt.typecheck.z.ErrorAnn> typecheck(Term term, SectionManager manager)
    throws Exception
  {
    return TypeCheckUtils.typecheck(term,  manager, recursiveTypes_);
  }
  
}
