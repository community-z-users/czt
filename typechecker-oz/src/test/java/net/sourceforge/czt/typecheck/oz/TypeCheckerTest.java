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
package net.sourceforge.czt.typecheck.oz;

import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestSuite;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.parser.util.LatexMarkupFunction;
import net.sourceforge.czt.parser.oz.ParseUtils;

/**
 * A JUnit test class for testing the typechecker. This reads any
 * files not ending with a "_" from the directory tests/oz.
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
  extends net.sourceforge.czt.typecheck.z.TypeCheckerTest
{
  //use strong typing
  protected boolean useStrongTyping_ = false;

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();

    // Weak
    TypeCheckerTest checkerTest = new TypeCheckerTest(false, false);
    checkerTest.collectTests(suite, TypeCheckerTest.class.getResource("/oz/"));

    // Strong
    checkerTest = new TypeCheckerTest(false, true);
    checkerTest.collectTests(suite, TypeCheckerTest.class.getResource("/oz/"));

    // UseBeforeDecl
    checkerTest = new TypeCheckerTest(true, false);
    checkerTest.collectTests(suite,
            TypeCheckerTest.class.getResource("/oz/recursiveTypes/"));

    // StrongOnly
    checkerTest = new TypeCheckerTest(false, true);
    checkerTest.collectTests(suite,
            TypeCheckerTest.class.getResource("/oz/strong/"));

    // WeakOnly
    checkerTest = new TypeCheckerTest(false, false);
    checkerTest.collectTests(suite,
            TypeCheckerTest.class.getResource("/oz/weak/"));

    return suite;
  }

  public TypeCheckerTest(boolean recursiveTypes, boolean useStrongTyping)
  {
    super(recursiveTypes);
    useStrongTyping_ = useStrongTyping;
  }

  protected SectionManager getManager()
  {
    return new SectionManager("oz");
  }

  protected List typecheck(Term term, SectionManager manager)
    throws Exception
  {
    return TypeCheckUtils.typecheck(term,
                                    manager,
                                    recursiveTypes_,
                                    useStrongTyping_);
  }
}
