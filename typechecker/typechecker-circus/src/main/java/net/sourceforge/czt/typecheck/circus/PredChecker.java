/*
  Copyright (C) 2007 Leo Freitas
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
package net.sourceforge.czt.typecheck.circus;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.circus.ast.ActionTransformerPred;
//import net.sourceforge.czt.circus.ast.CircusCommunicationList;
import net.sourceforge.czt.circus.ast.ProcessTransformerPred;
import net.sourceforge.czt.circus.visitor.ActionTransformerPredVisitor;
import net.sourceforge.czt.circus.visitor.ProcessTransformerPredVisitor;
import net.sourceforge.czt.typecheck.z.util.UResult;


/**
 * General PredChecker for all predicates. This is just a place holder for 
 * a more specialised implementation, and nothing is added to the z.PredChecker.
 * A CircusPattern type checker might want to extend this checker to deal with
 * checking TransformerPred and its subclasses. In here we provided a basic 
 * definition, which defers the calculation to the UnificationEnv. This visitor
 * does not add any annotation to the predicates being checked.
 *
 * @author Leo Freitas
 */
public class PredChecker 
  extends Checker<UResult>
  implements 
    ActionTransformerPredVisitor<UResult>,
    ProcessTransformerPredVisitor<UResult>
{    
  //a Z pred checker
  protected net.sourceforge.czt.typecheck.z.PredChecker zPredChecker_;

  public PredChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
    zPredChecker_ = new net.sourceforge.czt.typecheck.z.PredChecker(typeChecker);
  }

  /**
   * For all other predicate terms, use the standard Z typechecking rules 
   * within the  checking environment for Circus.
   *
   *@law C.18.7
   */
  @Override
  public UResult visitTerm(Term term)
  {
    return term.accept(zPredChecker_);
  }    

  @Override
  public UResult visitProcessTransformerPred(ProcessTransformerPred term)  
  {
//    CircusCommunicationList spec = 
    			term.getSpec().accept(processChecker());
//    CircusCommunicationList impl = 
    		term.getImpl().accept(processChecker());
    
//    ProcessType ptSpec = factory().createProcessType(psSpec);
//    ProcessType ptImpl = factory().createProcessType(psImpl);
//    UResult result = unificationEnv().unify(ptSpec, ptImpl);
//    
//    // TODO: CHECK: we need to handle PARTIAL. Recheck? See z.PredChecker() on this.
//    if (resultSUCC)
//    {    
//      ProdType resultType = factory().createProdType(ptSpec, ptImpl);    
//      addTypeAnn(term, resultType);
//    }    
    return UResult.SUCC;
  }

  public UResult visitActionTransformerPred(ActionTransformerPred term)
  {
//    CircusCommunicationList spec = 
    		visit(term.getSpec());
//    CircusCommunicationList impl = 
    		visit(term.getImpl());
    
//    ActionType atSpec = factory().createProcessType(asSpec);
//    ActionType atImpl = factory().createProcessType(asImpl);
//    UResult result = unificationEnv().unify(atSpec, atImpl);
//    
//    // TODO: CHECK: we need to handle PARTIAL. Recheck? See z.PredChecker() on this.
//    if (result == SUCC)
//    {    
//      ProdType resultType = factory().createProdType(atSpec, atImpl);    
//      addTypeAnn(term, resultType);
//    }
    
    return UResult.SUCC;
  }
}