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
package net.sourceforge.czt.typecheck.zeves;

import java.util.List;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.visitor.ProofScriptVisitor;

/**
 *
 * @author Leo Freitas
 */
public class ParaChecker
  extends Checker<Signature>        
  implements  ProofScriptVisitor<Signature>,
              AxParaVisitor<Signature>,
              ConjParaVisitor<Signature>
{   
  /**
   * Reference to a Z paragraph checker for checking Z paragraphs
   */
  protected net.sourceforge.czt.typecheck.z.ParaChecker zParaChecker_;
  
  public ParaChecker(TypeChecker typeChecker)
  {
    super(typeChecker);    
    zParaChecker_ = new net.sourceforge.czt.typecheck.z.ParaChecker(typeChecker);    
  }  
  
  @Override
  public Signature visitTerm(Term term)
  {
    return term.accept(zParaChecker_);
  }

  @Override
  public Signature visitAxPara(AxPara term)
  {
    // clear previous labelled preds known - maybe move it to Checker...
    ((PredChecker)predChecker()).clearLabelledPredList();

    // check it using the zParaChecker. This will eventually get to PredChecker
    // within Z/Eves, which will collect potential ZLabel names
    Signature result = term.accept(zParaChecker_);
    if (term.getBox().equals(Box.AxBox))
    {
      // extend the AxPara signature with available labelled predicates. This method will clear the underlying
      List<NameTypePair> labelledPreds = ((PredChecker)predChecker()).getLabelledPredsSignature();
      for(NameTypePair labelledPred : labelledPreds)
      {
        result.getNameTypePair().add(labelledPred);
      }
    }
    return result;
  }

  @Override
  public Signature visitProofScript(ProofScript term)
  {
    Name name = term.getName();
    Type found = getType(name);
    setCurrentProofName(name);
    setCurrentProofRefConjType(found);

    if (found instanceof UnknownType)
    {
      warningManager().warn(term, WarningMessage.PROOF_SCRIPT_HAS_NO_CONJ, name);
    }

    ProofType pt = factory().getZEvesFactory().createProofType(factory().getZEvesFactory().createProofCommandInfoList());
    for (ProofCommand pc : term.getProofCommandList())
    {
      ProofCommandInfo pct = pc.accept(proofCommandChecker());
      pt.getProofCommandInfoList().add(pct);
    }
    Signature result = factory().createSignature(
            factory().list(factory().createNameTypePair(term.getName(), pt)));
    addSignatureAnn(term, result);

    setCurrentProofRefConjType(null);
    setCurrentProofName(null);
    return result;
  }

  @Override
  public Signature visitConjPara(ConjPara term)
  {
    // Z typechecker already checks for duplicate theorem names
    Signature result = term.accept(zParaChecker_);

//    ZName thmName = factory().createZName(term.getName());
//    Signature result = factory().createSignature(
//            factory().list(factory().createNameTypePair(
//              thmName,
//              factory().getZEvesFactory().createProofType(
//                factory().getZEvesFactory().createProofCommandInfoList()))));
//    addSignatureAnn(term, result);
    return result;
  }

}
