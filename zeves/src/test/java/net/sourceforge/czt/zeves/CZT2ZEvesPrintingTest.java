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

package net.sourceforge.czt.zeves;

import java.net.URL;
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.List;
import junit.framework.Test;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;

/**
 *
 * @author nljsf
 */
public class CZT2ZEvesPrintingTest extends CztManagedTest {

  protected CZT2ZEvesPrintingTest(boolean debug)
  {
    super(Dialect.ZEVES, debug);
  }

  protected CZT2ZEvesPrintingTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
    if (manager.getDialect().equals("zeves"))
      throw new IllegalArgumentException("Invalid manager with dialect " + manager.getDialect());
  }

  @Override
  protected void testing(URL resource, Spec term) throws Exception
  {
    String fileName = URLDecoder.decode(resource.getPath(), "UTF-8"); //getFile() returns the protocol as well
    List<String> result = new ArrayList<String>();
    result = CZT2ZEves.runPrinter(fileName, true, DEBUG_TESTING);
    if (DEBUG_TESTING) { System.out.println(result.size() + " Z/EVES command(s) created:\n"); }
    if (!result.isEmpty() && result.get(0).equals("ERRORS"))
    {
      for(String s : result)
      {
        System.out.println(s);
      }
      System.out.println();
      fail("Encountered type errors");
    }
  }

  @Override
  protected boolean encounteredException(URL resource, Throwable e, String failureMsg, boolean handled)
  {
      System.out.println("Exception thrown during testing of " + failureMsg + " - " + e);
      e.printStackTrace();
      return super.encounteredException(resource, e, failureMsg, false);
      //System.exit(0);
  }

  @Override
  protected TestCase createNegativeTest(URL url, String exception, Class<?> expCls)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  protected static final boolean DEBUG_TESTING = false;
  protected final static String TEST_DIR =
          "/tests/";

  public static Test suite()
  {
    CZT2ZEvesPrintingTest test = new CZT2ZEvesPrintingTest(DEBUG_TESTING);
    Test result = test.cztTestSuite(TEST_DIR, null);
    if (DEBUG_TESTING)
    {
      System.out.println("Number of tests for Z/EVES XML protocol printing: " + result.countTestCases());
      System.out.println();
    }
    return result;
  }

}