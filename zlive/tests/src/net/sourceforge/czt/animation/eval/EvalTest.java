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
  protected ZLive animator = new ZLive();

  protected URL getTestExample(String name)
  {
    URL result = getClass().getResource("/tests/z/" + name);
    if (result == null) {
      throw new CztException("Cannot find example " + name);
    }
    return result;
  }
  
  
/**Working Properly :- Freetypes,Ints,Misc,Relations,Schemas,Scope*/
/**Not Working Properly :- Sequences, Sets (It seems to be just an error with the last line)*/


  public void testFreetypes()
  {
    URL url = getTestExample("animate_freetypes.tex");
  	doFileTest(url);
  }

  public void testInts()
  {
    URL url = getTestExample("animate_ints.tex");
  	doFileTest(url);
  }

  public void testMisc()
    {
      URL url = getTestExample("animate_misc.tex");
    	doFileTest(url);
  }

  public void testRelations()
    {
      URL url = getTestExample("animate_relations.tex");
    	doFileTest(url);
  }

  public void testSchemas()
    {
      URL url = getTestExample("animate_schemas.tex");
    	doFileTest(url);
  }

  public void testScope()
    {
      URL url = getTestExample("animate_scope.tex");
    	doFileTest(url);
  }

  public void testSequences()
    {
      URL url = getTestExample("animate_sequences.tex");
    	doFileTest(url);
  }

 public void testSets()
  {
      URL url = getTestExample("animate_sets.tex");
    	doFileTest(url);
  }


  private void doFileTest(URL url)
  {
    try {
      Spec spec = (Spec) ParseUtils.parse(url, animator.getSectionManager());

      for (Iterator i = spec.getSect().iterator(); i.hasNext(); ) {
	Object sect = i.next();
	if (sect instanceof ZSect) {
	  ZSect zsect = (ZSect) sect;
	  for (Iterator p = zsect.getPara().iterator(); p.hasNext(); ) {
	    Object para = (Para) p.next();
	    if (para instanceof ConjPara) {
              try {
                Pred pred = ((ConjPara)para).getPred();
                if(! isUndef(pred)) {
                  try {
                    animator.evalPred(pred);
                    System.out.println("Test Passed - evalPred");
                  }
                  catch (EvalException e) {
                    System.out.println("Test Failes - evalPred");
                  }
                }
              }
              catch (Exception e) {
                fail ("Should not throw exception " + e);
              }
            }
            //System.out.println(para); // TODO: evaluate it
	    else {
	      System.out.println("ADD " + para); // Ignore others
	    }
	  }
	}
      }
    }
    catch (Exception e) {
      fail("Should not throw exception " + e);
    }
  }
  private boolean isUndef(Pred pred)
  {
    boolean result = false;
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
              result = true;
              try {
                animator.evalExpr(leftExpr);
                System.out.println("This is undefined. Test Failed - evalExpr");
              }
              catch (EvalException excundef) {
                System.out.println("Test Passed - evalExpr");
              }
            }
          }
        }
      }
    }
    return result;
  }
}

