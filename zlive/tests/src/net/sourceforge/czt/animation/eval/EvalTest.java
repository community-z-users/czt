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

import java.io.IOException;
import java.net.URL;
import java.util.*;

import junit.framework.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.animation.eval.*;

/**
 * A (JUnit) test class for testing the Animator
 *
 * @author Mark Utting
 */
public abstract class EvalTest extends TestCase
{
  protected static ZLive animator_ = new ZLive();

  protected static String filename_;
  
  protected static URL getTestExample(String name) {
    Object stupid = new EnvirTest();
    URL result = stupid.getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }

  /** Get the LocAnn of a term, or null if it does not have one. */
  public static LocAnn getLocAnn(TermA term)
  {
    List anns = term.getAnns();
    Iterator i = anns.iterator();
    while (i.hasNext()) {
      Object ann = i.next();
	if (ann instanceof LocAnn)
	  return (LocAnn)ann;
    }
    return null;
  }

  /** If the predicate is Expr=undefnum, then return Expr. */
  private static Expr undefExpr(Pred pred) {
    Expr result = null;
    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred) pred;
      Expr leftExpr = memPred.getLeftExpr();
      Expr rightExpr = memPred.getRightExpr();
      if (rightExpr instanceof SetExpr) {
        List exprList = ((SetExpr) rightExpr).getExpr();
        if (exprList.size() == 1) {
          Expr refExpr = (Expr) exprList.get(0);
          if (refExpr instanceof RefExpr) {
            RefName refName = ((RefExpr) refExpr).getRefName();
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

    PredTest(String testname, Pred pred) {
      setName(testname);
      pred_ = pred;
    }

    /** Test that a predicate evaluates to TruePred. */
    public void runTest() {
      try {
        assertTrue(animator_.evalPred(pred_) instanceof TruePred);
        System.out.println("Passed test:" + getName());
      } catch (Exception e) {
        fail("Should not throw exception " + e);
      }
    }
  }

  /** This class tests that an expr is undefined. */
  static class UndefTest extends TestCase
  {
    private Expr expr_; // the expr that should be undefined.

    UndefTest(String testname, Expr expr) {
      setName(testname);
      expr_ = expr;
    }

    /** Test that an expression throws an undefined exception. */
    public void runTest() {
      try {
        animator_.evalExpr(expr_);
        fail("Should be undefined: " + expr_);
      } catch (UndefException e) {
        System.out.println("Passed undef test: " + getName());
      } catch (EvalException e) {
        fail("Exception while evaluating undef expr. " + e);
      }
    }
  }

  public static Test suite() {
    TestSuite tests = new TestSuite();
    int count = 0;
    Spec spec = null;
    try {
      spec = (Spec)ParseUtils.parse(getTestExample(filename_), 
          		animator_.getSectionManager());
    } catch (IOException e) {
      fail("Error opening file: "+filename_+": "+e);
    } catch (ParseException e) {
      fail("Error parsing file: "+filename_+": "+e);
    }
    for (Iterator i = spec.getSect().iterator(); i.hasNext();) {
      Object sect = i.next();
      if (sect instanceof ZSect) {
        ZSect zsect = (ZSect) sect;
        for (Iterator p = zsect.getPara().iterator(); p.hasNext();) {
          Object para = (Para) p.next();
          if (para instanceof ConjPara) {
            Pred pred = ((ConjPara) para).getPred();
            // construct a nice name for this test.
            count++;
            String name = filename_ + "::" + count;
	    LocAnn loc = getLocAnn(pred);
	    if (loc != null)
		{ name = filename_ + ":" + loc.getLine().intValue(); }
            int slash = name.lastIndexOf("/");
            if (slash >= 0)
              name = name.substring(slash+1);
            // create the test as a TestCase object.
            Expr undefexpr = undefExpr(pred);
            if (undefexpr == null)
              tests.addTest(new PredTest(name, pred));
            else
              tests.addTest(new UndefTest(name, undefexpr));
          }
        }
      }
    }
    return tests;
  }
}
