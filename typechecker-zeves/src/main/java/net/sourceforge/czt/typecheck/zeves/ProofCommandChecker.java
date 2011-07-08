/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.typecheck.zeves;

import net.sourceforge.czt.typecheck.z.impl.UnknownType;
import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.NormalizationKind;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofStepKind;
import net.sourceforge.czt.zeves.ast.ProofStepScope;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.ast.QuantifiersCommand;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionCommand;
import net.sourceforge.czt.zeves.ast.UseCommand;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.zeves.visitor.ApplyCommandVisitor;
import net.sourceforge.czt.zeves.visitor.CaseAnalysisCommandVisitor;
import net.sourceforge.czt.zeves.visitor.InstantiationListVisitor;
import net.sourceforge.czt.zeves.visitor.InstantiationVisitor;
import net.sourceforge.czt.zeves.visitor.NormalizationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.QuantifiersCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SimplificationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SubstitutionCommandVisitor;
import net.sourceforge.czt.zeves.visitor.UseCommandVisitor;
import net.sourceforge.czt.zeves.visitor.WithCommandVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jul 8, 2011
 */
public class ProofCommandChecker extends Checker<ProofCommandInfo>
  implements 
    NormalizationCommandVisitor<ProofCommandInfo>,
    UseCommandVisitor<ProofCommandInfo>,
    WithCommandVisitor<ProofCommandInfo>,
    SubstitutionCommandVisitor<ProofCommandInfo>,
    SimplificationCommandVisitor<ProofCommandInfo>,
    CaseAnalysisCommandVisitor<ProofCommandInfo>,
    QuantifiersCommandVisitor<ProofCommandInfo>,
    ApplyCommandVisitor<ProofCommandInfo>,
    InstantiationVisitor<ProofCommandInfo>,
    InstantiationListVisitor<ProofCommandInfo>
{

  public ProofCommandChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  @Override
  public ProofCommandInfo visitNormalizationCommand(NormalizationCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getKind().equals(NormalizationKind.Command))
    {
      if (term.getProofCommand() == null)
      {
        error(term, ErrorMessage.WITH_NORMALIZATION_NO_CMD, getCurrentProofName());
      }
      else
      {
        ProofCommandInfo innerPci = term.getProofCommand().accept(proofCommandChecker());
        result.setProofStepScope(innerPci.getProofStepScope());
        result.setProofStepKind(ProofStepKind.Medium);
      }
    }
    else
    {
      result.setProofStepKind(ProofStepKind.Trivial);
      result.setProofStepScope(ProofStepScope.Global);
    }
    return result;
  }

  @Override
  public ProofCommandInfo visitUseCommand(UseCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    Type2 found = GlobalDefs.unwrapType(term.getTheoremRef().accept(exprChecker()));
    if (found instanceof UnknownType) // or check to be !ProofType
    {
      error(term, ErrorMessage.USE_CMD_THMREF, getCurrentProofName(), term.getTheoremRef(), found);
    }

    int cnt = 1; int all = term.getInstantiationList().size();

    if (all == 0)
    {
      warningManager().warn(term, WarningMessage.USE_CMD_EMPTY_INST,
              getCurrentProofName(), term.getTheoremRef());
    }
    else
    {
      for(Instantiation i : term.getInstantiationList())
      {
        if (i.getKind().equals(InstantiationKind.Quantifier))
        {
          error(term, ErrorMessage.USE_CMD_INVALID_REPL, getCurrentProofName(), cnt, all, i.getName());
        }
        else
        {
          Type2 varType = GlobalDefs.unwrapType(getType(i.getName()));
          Type2 exprType= GlobalDefs.unwrapType(i.getExpr().accept(exprChecker()));
          UResult res   = unify(varType, exprType);
          if (!res.equals(UResult.SUCC))
          {
            error(term, ErrorMessage.USE_CMD_REPL, getCurrentProofName(), cnt, all, i.getName(), varType, exprType);
          }
        }
        cnt++;
      }
    }
    return result;
  }

  @Override
  public ProofCommandInfo visitWithCommand(WithCommand term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitSubstitutionCommand(SubstitutionCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    switch (term.getKind())
    {
      case Equality:
        if (term.getPred() != null || term.getProofCommand() != null || (term.getNameList() instanceof ZNameList && !term.getZNameList().isEmpty()))
        {
          warningManager().warn(term, WarningMessage.SUBST_CMD_INVALID_EQS, getCurrentProofName(), term);
        }
        if (term.getExpr() != null)
        {
          Type found = term.getExpr().accept(exprChecker());
          warningManager().warn(term, WarningMessage.SUBST_CMD_EXPR_EQS, getCurrentProofName(), term.getExpr(), found);
        }
        // otherwise do nothing
        break;
      case Invoke:
        if (term.getExpr() != null || term.getProofCommand() != null)
        {
          warningManager().warn(term, WarningMessage.SUBST_CMD_INVALID_INVOKE, getCurrentProofName(), term);
        }
        if (term.getPred() != null)
        {
          typeCheckPred(term, term.getPred());
        }
        else if (!term.getZNameList().isEmpty())
        {
          Type found = getType(term.getZNameList().get(0));
          if (found instanceof UnknownType)
          {
            error(term, ErrorMessage.SUBST_CMD_PRED_INVOKE, getCurrentProofName(), term.getZNameList().get(0), found);
          }
          if (term.getZNameList().size() != 1)
          {
            error(term, ErrorMessage.SUBST_CMD_BADNAME_INVOKE, getCurrentProofName(), term.getZNameList().size());
          }
        }
        // otherwise do nothing
        break;
    }
    return result;
  }

  @Override
  public ProofCommandInfo visitSimplificationCommand(SimplificationCommand term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitQuantifiersCommand(QuantifiersCommand term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitApplyCommand(ApplyCommand term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitInstantiation(Instantiation term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }

  @Override
  public ProofCommandInfo visitInstantiationList(InstantiationList term)
  {
    throw new UnsupportedOperationException("Not supported yet.");
  }
}
