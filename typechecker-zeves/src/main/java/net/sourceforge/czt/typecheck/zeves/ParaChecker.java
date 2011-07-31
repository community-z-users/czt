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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
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