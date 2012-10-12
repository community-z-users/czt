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
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.util.ZEvesString;
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
    // within Z/EVES, which will collect potential ZLabel names
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

  private boolean domainCheckName(Name name)
  {
    boolean result = name instanceof ZName;
    if (result)
    {
      ZName zn = ZUtils.assertZName(name);
      result = zn.getWord().endsWith(ZEvesString.ZPROOFDOLLAR + ZEvesString.DOMAIN_CHECK);
      //System.out.println("Considering DC name " + name + " = " + result);
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

    if (found instanceof UnknownType && !domainCheckName(name))
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

  /**
   * ConjPara typechecking is slightly different from Z. That's because Z/EVES allows
   * name jokers within predicate part of the theorem. So, we want to switch "undeclarare-name"
   * errors off in that case. To do that, we tag the *terms within the Pred part only*, and
   * during post checking, tagged terms that flag "undeclared-name" errors after post checking,
   * are treated such that the error becomes a warning.
   *
   * But that stops undeclared name typechecking at DeclPart of theorems, like the case with
   * generic operator templates (e.g., the only one we could imagine/create) like
   *
   * \begin{theorem}{lOpGenInThm}[X,Y]
   *   \forall f: X \zevesthmgen Y @ f \neq \emptyset
   * \end{theorem}
   *
   * In this case, both "f" and \zevesthmgen (defined as a \generic (\_ \zevesthmgen \_) template)
   * are wrongly tagged for postchecking. This is the only case that is dangerous.
   *
   * @param term
   * @return
   */
  @Override
  public Signature visitConjPara(ConjPara term)
  {
    // enable term tagging for certain terms within ConjPara (e.g., all those PostCheck able)
    setIgnoreUndeclaredNames(true);

    setCurrentThmName(term.getName());

    // Z typechecker already checks for duplicate theorem names
    Signature result = term.accept(zParaChecker_);

    setCurrentThmName(null);

    // disable term tagging
    setIgnoreUndeclaredNames(false);

    return result;
  }

}
