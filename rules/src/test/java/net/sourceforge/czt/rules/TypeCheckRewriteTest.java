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
import java.util.List;
import java.util.logging.Level;

import junit.framework.Test;
import junit.framework.TestSuite;

import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;

import net.sourceforge.czt.session.*;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.oldrewriter.Rewrite;
import net.sourceforge.czt.zpatt.util.Factory;

/**
 * @author Tim Miller
 */
public class TypeCheckRewriteTest
  extends net.sourceforge.czt.typecheck.z.TypeCheckerTest
{
  protected RuleTable rules_ = null;

  public static Test suite()
  {
    CztLogger.getLogger(SectionManager.class).setLevel(Level.OFF);
    TestSuite suite = new TestSuite();
    TypeCheckRewriteTest rewriteTest = new TypeCheckRewriteTest();
    rewriteTest.collectTests(suite,
	   TypeCheckRewriteTest.class.getResource("/rewrite/"));
    return suite;
  }

  public TypeCheckRewriteTest()
  {
    super(false, false);
  }

  @Override
  protected SectionManager getManager()
  {
    SectionManager manager = new SectionManager(Dialect.ZPATT);
    manager.putCommands(Dialect.ZPATT);
    manager.setProperty(PrintPropertiesKeys.PROP_PRINT_NAME_IDS, "true");
    loadRules(manager);
    return manager;
  }

  @Override
  protected List<? extends ErrorAnn> typecheck(Term term, SectionManager manager)
    throws Exception
  {
    super.typecheck(term, manager);
    //apply rules
    Term rewrittenTerm = preprocess(term, manager);
    String sectName = term.accept(new GetZSectNameVisitor());
    
    // we are going to re-typecheck the section, so remove the previous instance of
    // type information from the section manager
    if (sectName != null) {
    	manager.removeKey(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class));
    }
    
    // continue with typechecking the rewritten section
    // note that we need to use name IDs, otherwise types cannot be resolved correctly
    return TypeCheckUtils.typecheck(rewrittenTerm, manager, 
				    false, false, true);
  }

  public void loadRules(SectionManager manager)
  {
    try {
      URL url = RuleUtils.getUnfoldRules();
      if (url == null) {
	throw new IOException("Cannot get unfold rules");
      }

      manager.put(new Key<Source>(url.toString(), Source.class), new UrlSource(url));
      
      //load the rules
      Term term = manager.get(new Key<Spec>(url.toString(), Spec.class));
      String sectName = term.accept(new GetZSectNameVisitor());
      manager.get(new Key<SectTypeEnvAnn>(sectName, SectTypeEnvAnn.class)); 
      rules_ = manager.get(new Key<RuleTable>(sectName, RuleTable.class));
    }
    catch (Throwable e) {
      fail("\nUnexpected exception loading unfold rules\n" +
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
}
