/**
Copyright (C) 2003, 2004 Petra Malik
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

package net.sourceforge.czt.animator.eval;

import java.io.IOException;
import java.net.URL;
import java.util.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;

/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public class EvalTest
  extends TestCase
{
  protected SectionManager manager_ = new SectionManager();

  protected URL getTestExample(String name)
  {
    URL result = getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

  public void testFreetypes()
  {
    URL url = getTestExample("animate_freetypes.tex");
  	doFileTest(url);
  }

/*  public void testSets()
  {
    URL url = getTestExample("animate_sets.tex");
  	doFileTest(url);
  }
*/
  private void doFileTest(URL url)
  {
	try {
    	Spec spec = (Spec) ParseUtils.parse(url, manager_);

    	for (Iterator i = spec.getSect().iterator(); i.hasNext(); ) {
			Object sect = i.next();
			if (sect instanceof ZSect) {
				ZSect zsect = (ZSect) sect;
			    for (Iterator p = zsect.getPara().iterator(); p.hasNext(); ) {
					Object para = (Para) p.next();
					if (para instanceof ConjPara) {
						System.out.println(para); // TODO: evaluate it
					}
					else {
						System.out.println("ADD " + para); // Add to the animator
					}
				}
			}
        }
	}
	catch (Exception e) {
		fail("Should not throw exception " + e);
	}
  }

  public static Test suite()
  {
    return new TestSuite(EvalTest.class);
  }
}
