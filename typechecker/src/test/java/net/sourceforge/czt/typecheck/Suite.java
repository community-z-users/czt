/**
Copyright (C) 2004 Tim Miller
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
package net.sourceforge.czt.typecheck;

import junit.framework.Test;
import junit.framework.TestSuite;

import net.sourceforge.czt.typecheck.util.UnificationEnvTest;
import net.sourceforge.czt.typecheck.z.TypeInference;

/**
 * A JUnit test class for testing the Z typechecker.
 *
 * @author Tim Miller
 */
public class Suite
  extends TestSuite
{
  public static Test suite() {
    TestSuite suite = new TestSuite();
    //suite.addTest(UnificationEnvTest.suite());
    //suite.addTest(TypeInference.suite());
    suite.addTest(net.sourceforge.czt.typecheck.z.TypeCheckerTest.suite());    
    return suite;
  }
}
