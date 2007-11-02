/*
  Copyright (C) 2007 Petra Malik
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

package net.sourceforge.czt.rules.rewriter;

import static net.sourceforge.czt.rules.prover.ProverUtils.collectConjectures;

import java.io.OutputStreamWriter;
import java.io.StringWriter;
import java.net.URL;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.RuleUtils;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.prover.ProverUtils.GetZSectNameVisitor;
import net.sourceforge.czt.rules.rewriter.Rewriter;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.unification.Unifier;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.zpatt.util.Factory;

public class InnermostTest
  extends TestCase
{
  private static Factory factory_ = new Factory(new ProverFactory());

  public static Test suite()
    throws Exception
  {
    TestSuite suite = new TestSuite();
    collectTests(suite, "/rewrite.tex");
    return suite;
  }

  /**
   * Rewrites all the conjectures in the given file.
   */
  private static void collectTests(TestSuite suite, String resource)
    throws Exception
  {
    SectionManager manager = new SectionManager();
    manager.putCommands("zpatt");
    Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
    manager.put(new Key("unfold", Source.class), unfoldSource);
    URL url = InnermostTest.class.getResource(resource);
    assertFalse(url == null);
    manager.put(new Key(url.toString(), Source.class), new UrlSource(url));
    Term term = (Term) manager.get(new Key(url.toString(), Spec.class));
    String sectname = term.accept(new GetZSectNameVisitor());
    manager.get(new Key(sectname, SectTypeEnvAnn.class));
    RuleTable rules =
      (RuleTable) manager.get(new Key(sectname, RuleTable.class));
    for (ConjPara conjPara : collectConjectures(term)) {
      Pred pred = conjPara.getPred();
      suite.addTest(new RewriteTester(manager, sectname, rules, pred));
    }
  }

  static class RewriteTester
    extends TestCase
  {
    private SectionManager manager_;
    private String section_;
    private RuleTable rules_;
    private Pred pred_;

    RewriteTester(SectionManager manager, String sectname,
                  RuleTable rules, Pred pred)
    {
      manager_ = manager;
      section_ = sectname;
      rules_ = rules;
      pred_ = pred;
    }

    private void rewrite(Term term, Term expectedResult)
      throws Exception
    {
      Unifier unifier = new Unifier();
      Rewriter rewriter = new RewriteVisitor(rules_, manager_, section_);
      Term rewritten = Strategies.innermost(term, rewriter);
      Term expected = expectedResult.accept(new CopyVisitor(factory_));
      boolean result = unifier.unify(expected, rewritten);
      if (! result) {
        System.out.println("******************** Got *******************");
        print(rewritten);
        System.out.println("*************** Expected *******************");
        print(expectedResult);
        System.out.println(unifier.getCause());
      }
      assertTrue(result);
    }

    private void print(Term term)
    {
      XmlWriter writer = new JaxbXmlWriter();
      PrintUtils.print(term, new OutputStreamWriter(System.out),
                       manager_, section_, Markup.LATEX);
      System.out.println();
      //        writer.write(term, System.out);
    }

    public void runTest()
      throws Exception
    {
      if (pred_ instanceof IffPred) {
        IffPred iffPred = (IffPred) pred_;
        Pred leftPred = (Pred)
          iffPred.getLeftPred().accept(new CopyVisitor(factory_));
        rewrite(leftPred, iffPred.getRightPred());
      }
      else if (pred_ instanceof MemPred) {
        MemPred memPred = (MemPred) pred_;
        Expr leftExpr = (Expr)
          memPred.getLeftExpr().accept(new CopyVisitor(factory_));
        rewrite(leftExpr,
                ((SetExpr) memPred.getRightExpr()).getZExprList().get(0));
      }
      else {
        fail("Conjecture " + pred_ + " not supported");
      }
    }
  }
}
