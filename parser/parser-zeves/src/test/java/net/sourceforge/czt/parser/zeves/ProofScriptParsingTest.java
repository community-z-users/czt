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
import java.net.URLDecoder;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import junit.framework.Test;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.util.CztManagedTest;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;
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
    super(Dialect.ZEVES, debug);
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

  private int fStage_ = 0;

  @Override
  protected void testing(URL resource, Spec term) throws Exception
  {
    if (printer_ != null) ZUtils.setToStringVisitor(term, printer_);
    String fileName = URLDecoder.decode(resource.getPath(), "UTF-8");
    if (isDebugging())
    {
      System.out.println("Parsing successful, start printing of " + resource);
    }
    fStage_ = 1;

    LatexScannerDebugger.debugPrinter(new FileSource(fileName), getManager(), term, isDebugging());

    if (isDebugging())
    {
      System.out.println("\nPrinting successful, start re-parsing of derived files");
    }
    List<Markup> markups = new ArrayList<Markup>(Arrays.asList(Markup.values()));

    fStage_ = 2;
    markups.remove(Markup.getMarkup(fileName));
    for(Markup m : markups)
    {
      // we are about to reparse files in different markups, we better reset the manager -
      // otherwise there will be cached entities there for the same ZSects.
      getManager().reset();

      final String refile = fileName + Markup.getDefaultFileExtention(m);
      if (isDebugging())
      {
        System.out.println("  reparsting " + refile);
      }
      parse(refile);
    }
  }

  @Override
  protected Spec parse(String fileName) throws CommandException
  {
    Spec result = super.parse(fileName);
    getManager().reset();
    return result;
  }

  @Override
  protected boolean encounteredException(URL resource, Throwable e, String failureMsg, boolean handled)
  {
    final String stage = fStage_ == 0 ? "parsing" : fStage_==1 ? "printing" : "reparsing";
    System.out.println("Encountered exception during " + stage + " " + e.getClass().getName());
    System.out.println("  " + failureMsg);
    return handled;
  }
  
  protected static final boolean DEBUG_TESTING = false;
  protected final static String TEST_DIR =
          "/tests/zeves/";

  public static Test suite()
  {
    //String s, t = null;
    //s.replaceAll("", "").trim();
    ProofScriptParsingTest test = new ProofScriptParsingTest(DEBUG_TESTING);
    Test result = test.cztTestSuite(TEST_DIR, null);
    if (DEBUG_TESTING)
    {
      System.out.println("Number of tests for Z/EVES proofs parsing: " + result.countTestCases());
      System.out.println();
    }
    return result;
  }



}
