/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.vcg.z.refinement;

import java.net.URL;
import java.util.SortedSet;

import junit.framework.Test;
import junit.framework.TestCase;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityTest;
import net.sourceforge.czt.z.ast.SchemaType;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementTest extends FeasibilityTest implements RefinementPropertyKeys
{
  public static Test suite() throws VCGException
  {
    SectionManager manager = RefinementUtils.getRefinementUtils().createSectionManager(
            RefinementUtils.getRefinementUtils().getExtension());
    RefinementTest test = new RefinementTest(manager, DEBUG_TESTING);
    Test result = test.cztTestSuite(TEST_DIR, null);
    if (DEBUG_TESTING) { System.out.println("Number of tests: " + result.countTestCases()); }
    return result;
  }

  protected RefinementTest(Dialect extension, boolean debug)
  {
    super(extension, debug);
  }

  protected RefinementTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }

  @Override
  protected TestCase createPositiveTest(URL url)
  {
    return new NormalVCGTest<SchemaType, SortedSet<Definition>>(url, RefinementUtils.getRefinementUtils());
  }

}