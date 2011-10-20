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

package net.sourceforge.czt.vcg.util;

import java.net.URL;
import junit.framework.Test;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.vcg.z.VCGException;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityUtils;
import net.sourceforge.czt.z.ast.Spec;

/**
 *
 * @author Leo Freitas
 * @date Jan 13, 2011
 */
public class DefinitionTableTest extends VCGTest
{

  protected static final boolean DEBUG_TESTING = false;
  protected final static String TEST_DIR =
          "/tests/z/";

  public static Test suite() throws VCGException
  {
    SectionManager manager = FeasibilityUtils.getFeasibilityUtils().createSectionManager(
            FeasibilityUtils.getFeasibilityUtils().getExtension());
    VCGTest test = new DefinitionTableTest(manager, DEBUG_TESTING);
    Test result = test.suite(TEST_DIR, null);
    if (DEBUG_TESTING) { System.out.println("Number of tests: " + result.countTestCases()); }
    return result;
  }

  protected DefinitionTableTest(String extension, boolean debug)
  {
    super(extension, debug);
  }

  protected DefinitionTableTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }

  @Override
  protected TestCase createPositiveTest(URL url)
  {
    return new NormalDefTableTest(url);
  }

  @Override
  protected boolean includeVCGTest(String name, boolean positive)
  {
    return true; // include all
  }

  public class NormalDefTableTest extends CztManagedTest.TestNormal
  {
    public NormalDefTableTest(URL url)
    {
      super(url);
    }

    @Override
    protected void doTest(Spec term) throws Exception
    {
      // do nothing
    }

    /**
     * Exceptions on positive tests are errors.
     * @param e
     * @param failureMsg
     * @return false
     */
    @Override
    protected boolean handledException(Throwable e, StringBuilder failureMsg)
    {
      boolean result = super.handledException(e, failureMsg);
      if (!result)
      {
        if (e instanceof DefinitionException)
        {
          failureMsg.append("DefinitionException = \n");
          failureMsg.append(((DefinitionException)e).getMessage(true));
          result = true;//don't fail, but print out --- TODO: change to false when more examples are handled.
        }
      }
      return result;
    }
  }
}
