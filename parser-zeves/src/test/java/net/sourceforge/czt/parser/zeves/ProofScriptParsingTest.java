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

package net.sourceforge.czt.parser.zeves;

import java.net.URL;
import junit.framework.Test;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.util.PrintVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jul 4, 2011
 */

public class ProofScriptParsingTest 
        extends CztManagedTest
{

  protected ProofScriptParsingTest(boolean debug)
  {
    super("zeves", debug);
  }

  protected ProofScriptParsingTest(SectionManager manager, boolean debug)
  {
    super(manager, debug);
  }
  
  private PrintVisitor printer_ = null;

  @Override
  protected void setUp() throws Exception
  {
    super.setUp();
    printer_ = new PrintVisitor(false);
    printer_.setPrintIds(false);
    printer_.setOffset(1, 1);
  }

  @Override
  protected TestCase createNegativeTest(URL url, String exception, Class<?> expCls)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  protected void testing(Spec term)
  {
    if (printer_ != null) ZUtils.setToStringVisitor(term, printer_);
    for(Sect s : term.getSect())
    {
      if (s instanceof ZSect)
      {
        ZSect zs = (ZSect)s;
        System.out.print(zs.getName() + " = ");
        System.out.println(zs.toString());
      }
    }
  }

  @Override
  @SuppressWarnings("CallToThreadDumpStack")
  protected void encounteredException(Throwable e, String failureMsg, boolean handled)
  {
    System.out.println("Encountered exception during parsing: " + e.getClass().getName());
    System.out.println("\t " + failureMsg);
    if (!handled) e.printStackTrace();
  }
  protected static final boolean DEBUG_TESTING = false;
  protected final static String TEST_DIR =
          "/tests/zeves/";

  public static Test suite()
  {
    //String s, t = null;
    //s.replaceAll("", "").trim();
    ProofScriptParsingTest test = new ProofScriptParsingTest(DEBUG_TESTING);
    Test result = test.suite(TEST_DIR, null);
    System.out.println("Number of tests for Z/Eves proofs parsing: " + result.countTestCases());
    return result;
  }
}
