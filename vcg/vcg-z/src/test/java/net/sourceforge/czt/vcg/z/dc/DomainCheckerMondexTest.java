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

package net.sourceforge.czt.vcg.z.dc;

import junit.framework.Test;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.vcg.util.VCGTest;
import net.sourceforge.czt.vcg.z.VCGException;

/**
 *
 * @author Leo Freitas
 * @date Feb 7, 2012
 */
public class DomainCheckerMondexTest extends DomainCheckerTest
{

  protected final static String TEST_MONDEX_DIR = "/tests/mondex/";

  public static Test suite() throws VCGException
  {
    SectionManager manager =  DomainCheckUtils.getDCUtils().createSectionManager(Dialect.ZEVES);
    VCGTest test = new DomainCheckerMondexTest(manager, DEBUG_TESTING);
    Test result = test.cztTestSuite(TEST_MONDEX_DIR, null);
    if (DEBUG_TESTING) { System.out.println("Number of tests: " + result.countTestCases()); }
    return result;
  }

  protected DomainCheckerMondexTest(Dialect extension, boolean debug)
  {
    super(extension, debug);
  }

  protected DomainCheckerMondexTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }

  @Override
  protected boolean includeVCGTest(String name, boolean positive)
  {
    return false ;//&& positive && name.equals("loadproofs.tex");
  }

}
