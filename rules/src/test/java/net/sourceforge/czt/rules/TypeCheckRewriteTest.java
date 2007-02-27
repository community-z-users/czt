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
package net.sourceforge.czt.rules;

import java.io.*;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.impl.ZFactoryImpl;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;

import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.typecheck.z.util.SectTypeEnv;
import net.sourceforge.czt.typecheck.z.util.TypeErrorException;

import net.sourceforge.czt.rules.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * @author Tim Miller
 */
public class TypeCheckRewriteTest
  extends net.sourceforge.czt.typecheck.z.TypeCheckerTest
{
  final private static String RULES_FILE = "/rulesets/unfold.tex";

  protected RuleTable rules_ = null;

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    TypeCheckRewriteTest rewriteTest = new TypeCheckRewriteTest();
    rewriteTest.collectTests(suite, "rewrite/");
    return suite;
  }

  public TypeCheckRewriteTest()
  {
    super(false);
  }

  protected SectionManager getManager()
  {
    SectionManager manager = new SectionManager();
    manager.putCommands("zpatt");
    manager.setProperty(PrintPropertiesKeys.PROP_PRINT_NAME_IDS, "true");
    loadRules(manager);
    return manager;
  }

  protected List typecheck(Term term, SectionManager manager)
    throws Exception
  {
    super.typecheck(term, manager);

    //System.err.println("\n\n\n\n\n******** before ***********");
    //printTerm(term, manager);

    //apply rules
    Term rewrittenTerm = preprocess(term, manager);

    //System.err.println("\n~~~~~~~~ after ~~~~~~~~~~~~");
    //printTerm(rewrittenTerm, manager); 

    String sectName = term.accept(new GetZSectNameVisitor());
    return TypeCheckUtils.typecheck(rewrittenTerm, manager, 
				    false, true, sectName);
  }

  public void loadRules(SectionManager manager)
  {
    try {
      URL url = getClass().getResource(RULES_FILE);
      if (url == null) {
	throw new IOException("Cannot getResource(" + RULES_FILE + ")");
      }

      manager.put(new Key(url.toString(), Source.class), new UrlSource(url));
      
      //load the rules
      Term term = (Term) manager.get(new Key(url.toString(), Spec.class));
      String sectName = term.accept(new GetZSectNameVisitor());
      manager.get(new Key(sectName, SectTypeEnvAnn.class)); 
      rules_ = (RuleTable) manager.get(new Key(sectName, RuleTable.class));
    }
    catch (Throwable e) {
      fail("\nUnexpected exception loading " + RULES_FILE + "\n" +
	   "\n\tException: " + e.toString());
    }

    // for debugging only...
    //for (String ruleName : rules_.getRules().keySet())
    //  System.err.println("loaded rule " + ruleName);
  }

  public Term preprocess(Term term, SectionManager manager)
  {
    if (rules_ == null) {
      throw new RuntimeException("preprocessing error: no rules!");
    }
    Factory factory = new Factory(new ProverFactory());
    Term term2 = term.accept(new CopyVisitor(factory));
    Term term3 = Rewrite.rewrite(manager, term2, rules_);
    return term3;
  }

  private void printTerm(Term term, SectionManager manager)
  {
    try {
      PrintUtils.printLatex(term, new PrintWriter(System.err), manager);
    }
    catch (Exception e) {
      System.err.println(e.toString());
      e.printStackTrace();
    }
  }
}
