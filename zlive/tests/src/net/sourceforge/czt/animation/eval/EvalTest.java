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

import net.sourceforge.czt.base.ast.Term;
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
public class EvalTest
  extends TestCase
{
  protected static ZLive animator = new ZLive();

  protected static URL getTestExample(String name)
  {
    Object stupid = new EvalTest();
    URL result = stupid.getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
  
  public static Test suite()
  {
    TestSuite tests = new TestSuite();
    tests.addTest(new FileTest(getTestExample("animate_freetypes.tex")));
    tests.addTest(new FileTest(getTestExample("animate_ints.tex")));
    tests.addTest(new FileTest(getTestExample("animate_scope.tex")));
    tests.addTest(new FileTest(getTestExample("animate_schemas.tex")));
    tests.addTest(new FileTest(getTestExample("animate_sequences.tex")));
    tests.addTest(new FileTest(getTestExample("animate_relations.tex")));
    tests.addTest(new FileTest(getTestExample("animate_misc.tex")));
    tests.addTest(new FileTest(getTestExample("animate_sets.tex")));
    return tests;
  }
  
  /** If the predicate is Expr=undefnum, then return Expr. */
  private static Expr undefExpr(Pred pred)
  {
    Expr result = null;
    if (pred instanceof MemPred) {
      MemPred memPred = (MemPred)pred;
      Expr leftExpr = memPred.getLeftExpr();
      Expr rightExpr = memPred.getRightExpr();
      if (rightExpr instanceof SetExpr) {
        List exprList = ((SetExpr)rightExpr).getExpr();
        if(exprList.size()==1) {
          Expr refExpr = (Expr) exprList.get(0);
          if(refExpr instanceof RefExpr) {
            RefName refName = ((RefExpr)refExpr).getRefName();
            if ((refName.getWord()).equals("undefnum")) {
              result = leftExpr;
            }
          }
        }
      }
    }
    return result;
  }

  /** Test a whole file full of conjectures. */
  static class FileTest extends TestCase
  {
    private URL filename;
    
    public FileTest(URL name)
    {
      filename = name;
    }
    
    /** Test that a predicate evaluates to TruePred. */
    private void doPredTest(Pred pred)
    {
      try {
        assertTrue(animator.evalPred(pred) instanceof TruePred);
        System.out.println("Test Passed - evalPred");
      }
      catch (Exception e) {
        fail("Should not throw exception " + e);
      }
    }
    
    /** Test that an expression throws an undefined exception. */
    private void doUndefTest(Expr undefexpr)
    {
      try {
        animator.evalExpr(undefexpr);
        fail("Should be undefined: "+undefexpr);
      }
      catch (Exception e) {
        System.out.println("Test Passed - Undefined Expression");
      }
    }
    
    /** Override this method so that we can execute many tests. */
    public void run(TestResult result) {
      try {
        Spec spec = (Spec) ParseUtils.parse(filename, animator.getSectionManager());
        for (Iterator i = spec.getSect().iterator(); i.hasNext(); ) {
          Object sect = i.next();
          if (sect instanceof ZSect) {
            ZSect zsect = (ZSect) sect;
            for (Iterator p = zsect.getPara().iterator(); p.hasNext(); ) {
              Object para = (Para) p.next();
              if (para instanceof ConjPara) {
                Pred pred = ((ConjPara)para).getPred();
                // TODO: somehow add the line number to the test name.
                result.startTest(this); 
                try {setUp();}
                catch (Exception e) {fail("tearDown exception: "+e);}
                try {
                  Expr undefexpr = undefExpr(pred);
                  if(undefexpr == null) {
                    doPredTest(pred);
                  }
                  else {
                    //System.out.println("Reached undefined test loop");
                    doUndefTest(undefexpr);
                  }
                } 
                catch (AssertionFailedError e) { //1 
                  result.addFailure(this, e); 
                } 
                catch (Throwable e) { // 2 
                  result.addError(this, e); 
                } 
                finally { 
                  try {tearDown();}
                  catch (Exception e) {fail("tearDown exception: "+e);}
                }                   
              }
            }
          }
        }
      }
      catch (Exception e) {
        fail("Parse Error :" + e);
      }
    }
  }
}
