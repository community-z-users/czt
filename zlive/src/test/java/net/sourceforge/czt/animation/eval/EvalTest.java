/**
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.animation.eval;

import java.math.BigInteger;
import java.net.URL;
import java.util.List;
import java.util.logging.Logger;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.ZUtils;

/**
* A (JUnit) test class for testing the Animator
*
* @author Mark Utting
*/
public abstract class EvalTest extends TestCase
{
  private static final Logger LOG
  = Logger.getLogger("net.sourceforge.czt.animation.eval");

  /** Get the line number of a term, or null if line number is unknown */
  private static BigInteger getLineNumFrom(Term term)
  {
    LocAnn loc = term.getAnn(LocAnn.class);
    if (loc != null && loc.getLine() != null)
        return loc.getLine();
    return null;
  }
  

  /** Get the line number of a term or its subterms.
   *  @return A line number, or null if unknown.
   */
  public static BigInteger getLineNum(Term term)
  {
    BigInteger result = getLineNumFrom(term);
    if (result != null)
      return result;
    
    // look for line numbers in the children...
    for (Object child : term.getChildren()) {
      if (child instanceof Term) {
        result = getLineNum((Term) child);
        if (result != null)
          return result;
      }
    }
    
    return null;
  }

  public static URL getTestExample(String name)
  {
    return EvalTest.class.getResource("/" + name);
  }

  /** If the predicate is Expr=undefnum, then return Expr. */
  private static Expr undefExpr(Pred pred) {
    Expr result = null;
    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      Expr leftExpr = memPred.getLeftExpr();
      Expr rightExpr = memPred.getRightExpr();
      if (rightExpr instanceof SetExpr) {
        List<Expr> exprList = ((SetExpr) rightExpr).getZExprList();
        if (exprList.size() == 1) {
          Expr refExpr = exprList.get(0);
          if (refExpr instanceof RefExpr) {
            ZName refName = ((RefExpr) refExpr).getZName();
            if ((refName.getWord()).equals("undefnum")) {
              result = leftExpr;
            }
          }
        }
      }
    }
    return result;
  }

  /** This class tests one predicate */
  static class PredTest extends TestCase
  {
    private Pred pred_; // the predicate to evaluate
    private ZLive animator_;

    PredTest(String testname, Pred pred, ZLive anim) {
      setName(testname);
      pred_ = pred;
      animator_ = anim;
    }

    /** Test that a predicate evaluates to TruePred. */
    public void runTest() {
      LOG.fine("running PredTest("+getName()+")");
      Pred result = animator_.evalPred(pred_);
      assertNotNull(result);
      assertTrue(result instanceof TruePred);
      System.out.println("Passed test:" + getName());
    }
  }

  /** This class tests that an expr is undefined. */
  static class UndefTest extends TestCase
  {
    private Expr expr_; // the expr that should be undefined.
    private ZLive animator_;

    UndefTest(String testname, Expr expr, ZLive anim) {
      setName(testname);
      expr_ = expr;
      animator_ = anim;
    }

    /** Test that an expression throws an undefined exception. */
    public void runTest() {
      LOG.fine("running UndefTest("+getName()+")");
      try {
        animator_.evalExpr(expr_);
        System.out.println("FAILED undef test (not undefined): " + getName());
        fail("Should be undefined: " + expr_);
      } catch (UndefException e) {
        System.out.println("Passed undef test: " + getName());
      }
    }
  }

  public static Test generateSuite(String filename) {
    ZLive animator = new ZLive();
    //ZFormatter.startLogging("net.sourceforge.czt.animation.eval",
    //    "zlive.log", Level.FINER);
    TestSuite tests = new TestSuite();
    int count = 0;
    Spec spec = null;
    try {
      SectionManager sectman = animator.getSectionManager();
      URL url = getTestExample(filename);
      sectman.put(new Key<Source>(filename,Source.class),
		  new UrlSource(url));
      spec = sectman.get(new Key<Spec>(filename,Spec.class));
      //System.out.println("parsing '"+url+"' gives: " + spec);
      String sectName = null;
      // set zlive to use the first Z section in the file.
      if (spec != null) {
        for (Sect sect : spec.getSect()) {
          if (sect instanceof ZSect) {
            sectName = ((ZSect)sect).getName();
            break;
          }
        }
        if (sectName == null)
          fail("Error: could not find ZSect after parsing");
        else
          animator.setCurrentSection(sectName);
        //System.out.println(sectman.getInfo(sectName, DefinitionTable.class).toString());
      }
    } catch (Exception e) {
      fail("Error opening/parsing file: "+filename+": "+e);
    }
    for (Sect sect : spec.getSect()) {
      if (sect instanceof ZSect) {
        ZSect zsect = (ZSect) sect;
        for (Para para : ZUtils.assertZParaList(zsect.getParaList())) {
          if (para instanceof ConjPara) {
            Pred pred = ((ConjPara) para).getPred();
            // construct a nice name for this test.
            count++;
            String name = filename + "::" + count;
            BigInteger lineNum = getLineNum(pred);
            if (lineNum != null)
              { name = filename + ":" + lineNum.intValue(); }
            int slash = name.lastIndexOf("/");
            if (slash >= 0)
              name = name.substring(slash+1);
            // create the test as a TestCase object.
            Expr undefexpr = undefExpr(pred);
            if (undefexpr == null)
              tests.addTest(new PredTest(name, pred, animator));
            else
              tests.addTest(new UndefTest(name, undefexpr, animator));
          }
        }
      }
    }
    return tests;
  }
}
