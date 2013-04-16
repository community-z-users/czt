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

import net.sourceforge.czt.typecheck.z.util.GlobalDefs;
import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisKind;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.NormalizationKind;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofStepKind;
import net.sourceforge.czt.zeves.ast.ProofStepScope;
import net.sourceforge.czt.zeves.ast.QuantifiersCommand;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SorryCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionCommand;
import net.sourceforge.czt.zeves.ast.UseCommand;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.zeves.visitor.ApplyCommandVisitor;
import net.sourceforge.czt.zeves.visitor.CaseAnalysisCommandVisitor;
import net.sourceforge.czt.zeves.visitor.NormalizationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.QuantifiersCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SimplificationCommandVisitor;
import net.sourceforge.czt.zeves.visitor.SorryCommandVisitor;
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
        SorryCommandVisitor<ProofCommandInfo>,
        ApplyCommandVisitor<ProofCommandInfo>//,
//    InstantiationVisitor<ProofCommandInfo>,
//    InstantiationListVisitor<ProofCommandInfo>
{

  public ProofCommandChecker(TypeChecker typeChecker)
  {
    super(typeChecker);
  }

  // TODO: these typeCheckXXX functions could return ProofStepKind when expr / pred were complicated
  protected void typeCheckInstantiation(ProofCommand term, Instantiation i, int cnt, int all, ErrorMessage msg)
  {
    Type2 varType = GlobalDefs.unwrapType(getType(i.getName()));
    Type2 exprType = GlobalDefs.unwrapType(typeCheckExpr(term, i.getExpr(), null));
    UResult res = unify(varType, exprType);
    if (!res.equals(UResult.SUCC))
    {
      // Keep it as a warning
      //error(term, msg, getCurrentProofName(), cnt, all, i.getName(), varType, exprType);
      warningManager().warn(term, msg, getCurrentProofName(), cnt, all, i.getName(), varType, exprType);
    }
  }

  @Override
  public ProofCommandInfo visitNormalizationCommand(NormalizationCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getNormalizationKind().equals(NormalizationKind.Command))
    {
      if (term.getProofCommand() == null)
      {
        error(term, ErrorMessage.WITH_NORMALIZATION_NO_CMD, getCurrentProofName());
      }
      else
      {
        ProofCommandInfo innerPci = term.getProofCommand().accept(proofCommandChecker());
        result.setProofStepScope(innerPci.getProofStepScope());
        result.setProofStepKind(innerPci.getProofStepKind().ordinal() > ProofStepKind.Simple.ordinal() ?
          innerPci.getProofStepKind() : ProofStepKind.Simple);
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

    typeCheckThmRef(term, term.getTheoremRef(), ErrorMessage.USE_CMD_THMREF);

    int cnt = 1;
    int all = term.getInstantiationList() == null ? 0 : term.getInstantiationList().size();

    if (all == 0)
    {
      //warningManager().warn(term, WarningMessage.USE_CMD_EMPTY_INST,
      //        getCurrentProofName(), term.getTheoremRef());
      result.setProofStepKind(ProofStepKind.Medium);
    }
    else
    {
      for (Instantiation i : term.getInstantiationList())
      {
        if (i.getInstantiationKind().equals(InstantiationKind.Quantifier))
        {
          error(term, ErrorMessage.USE_CMD_INVALID_REPL, getCurrentProofName(), cnt, all, i.getName());
        }
        else
        {
          typeCheckInstantiation(term, i, cnt, all, ErrorMessage.USE_CMD_REPL);
        }
        cnt++;
      }
      result.setProofStepKind(ProofStepKind.Complex);
    }
    result.setProofStepScope(ProofStepScope.Global);
    return result;
  }

  @Override
  public ProofCommandInfo visitWithCommand(WithCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getProofCommand() == null //||
       //(term.getNameList() != null term.getNameList() instanceof ZNameList && term.getZNameList().isEmpty())
       )
    {
      error(term, ErrorMessage.WITH_CMD_INVALID, getCurrentProofName());
    }
    else
    {
      ProofStepKind base = ProofStepKind.Simple;
      if (term.getEnabled() != null)
      {
        assert !term.getZNameList().isEmpty(); // TODO: check above for structural weird aspects
        for (Name n : term.getZNameList())
        {
          typeCheckThmRef(term, n, ErrorMessage.WITH_CMD_THMNAME);
        }
      }
      else if (term.getExpr() != null)
      {
        assert term.getPred() == null;
        typeCheckExpr(term, term.getExpr(), null);
        base = ProofStepKind.Medium;
      }
      else if (term.getPred() != null)
      {
        assert term.getExpr() == null;
        typeCheckPred(term, term.getPred());
        base = ProofStepKind.Medium;
      }
      ProofCommandInfo innerPci = term.getProofCommand().accept(proofCommandChecker());
      result.setProofStepScope(innerPci.getProofStepScope());
      result.setProofStepKind(innerPci.getProofStepKind().ordinal() > base.ordinal() ?
          innerPci.getProofStepKind() : base);
    }
    return result;
  }

  @Override
  public ProofCommandInfo visitSubstitutionCommand(SubstitutionCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    switch (term.getSubstitutionKind())
    {
      case Equality:
        if (term.getPred() != null || term.getProofCommand() != null || (term.getNameList() instanceof ZNameList && !term.getZNameList().isEmpty()))
        {
          // TODO: make it an error?
          warningManager().warn(term, WarningMessage.SUBST_CMD_INVALID_EQS, getCurrentProofName(), term);
        }
        if (term.getExpr() != null)
        {
          typeCheckExpr(term, term.getExpr(), WarningMessage.SUBST_CMD_EXPR_EQS);

          result.setProofStepKind(ProofStepKind.Simple);
          result.setProofStepScope(ProofStepScope.Local);
        }
        else
        {
          result.setProofStepKind(ProofStepKind.Trivial);
          result.setProofStepScope(ProofStepScope.Global);
        }
        break;
      case Invoke:
        if (term.getExpr() != null || term.getProofCommand() != null)
        {
          // TODO: make it an error?
          warningManager().warn(term, WarningMessage.SUBST_CMD_INVALID_INVOKE, getCurrentProofName(), term);
        }
        if (term.getPred() != null)
        {
          assert term.getNameList() == null || term.getZNameList().isEmpty();
          typeCheckPred(term, term.getPred());

          result.setProofStepKind(ProofStepKind.Simple);
          result.setProofStepScope(ProofStepScope.Local);
        }
        else if (term.getNameList() != null && !term.getZNameList().isEmpty())
        {
          assert term.getPred() == null;
          typeCheckThmRef(term, term.getZNameList().get(0), ErrorMessage.SUBST_CMD_PRED_INVOKE);
          if (term.getZNameList().size() != 1)
          {
            error(term, ErrorMessage.SUBST_CMD_BADNAME_INVOKE, getCurrentProofName(), term.getZNameList().size());
          }

          result.setProofStepKind(ProofStepKind.Simple);
          result.setProofStepScope(ProofStepScope.Local);
        }
        else
        {
          result.setProofStepKind(ProofStepKind.Trivial);
          result.setProofStepScope(ProofStepScope.Global);
        }
        break;
    }
    return result;
  }

  @Override
  public ProofCommandInfo visitSimplificationCommand(SimplificationCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    switch (term.getRewritePower())
    {
      case None:
        result.setProofStepKind(ProofStepKind.Simple);
        break;
      case Prove:
        result.setProofStepKind(ProofStepKind.Trivial);
        break;
      case Trivial:
        result.setProofStepKind(ProofStepKind.Medium);
        break;
    }
    result.setProofStepScope(ProofStepScope.Global);
    return result;
  }

  @Override
  public ProofCommandInfo visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getCaseAnalysisKind().equals(CaseAnalysisKind.Split))
    {
      if (term.getPred() == null)
      {
        // TODO: make it an error?
        warningManager().warn(term, WarningMessage.SPLIT_CMD_INVALID_PRED, getCurrentProofName());
      }
      else
      {
        typeCheckPred(term, term.getPred());
      }
      result.setProofStepKind(ProofStepKind.Medium);
    }
    else
    {
      result.setProofStepKind(ProofStepKind.Trivial);
    }
    result.setProofStepScope(ProofStepScope.Global);
    return result;
  }

  @Override
  public ProofCommandInfo visitQuantifiersCommand(QuantifiersCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getInstantiationList() == null)
    {
      result.setProofStepKind(ProofStepKind.Trivial);
    }
    else
    {
      int cnt = 1;
      int all = term.getInstantiationList().size();
      for (Instantiation i : term.getInstantiationList())
      {
        if (i.getInstantiationKind().equals(InstantiationKind.ThmReplacement))
        {
          error(term, ErrorMessage.QNT_CMD_INVALID_INST, getCurrentProofName(), cnt, all, i.getName());
        }
        else
        {
          typeCheckInstantiation(term, i, cnt, all, ErrorMessage.QNT_CMD_INST);
        }
        cnt++;
      }
      // TODO: maybe add some discretion here given the complexity of the instantiated variable?
      result.setProofStepKind(ProofStepKind.Complex);
    }
    result.setProofStepScope(ProofStepScope.Global);
    return result;
  }

  @Override
  public ProofCommandInfo visitApplyCommand(ApplyCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    if (term.getProofCommand() != null || (term.getNameList() instanceof ZNameList && term.getZNameList().isEmpty()))
    {
      warningManager().warn(term, WarningMessage.APPLY_CMD_INVALID, getCurrentProofName(), term);
    }

    typeCheckThmRef(term, term.getThmName(), ErrorMessage.APPLY_CMD_THMNAME);
    
    if (term.getPred() != null)
    {
      assert term.getExpr() == null;
      typeCheckPred(term, term.getPred());
      result.setProofStepKind(ProofStepKind.Medium);
      result.setProofStepScope(ProofStepScope.Local);
    }
    else if (term.getExpr() != null)
    {
      assert term.getPred() == null;
      typeCheckExpr(term, term.getExpr(), WarningMessage.APPLY_CMD_EXPR);
      result.setProofStepKind(ProofStepKind.Medium);
      result.setProofStepScope(ProofStepScope.Local);
    }
    else
    {
      assert term.getExpr() == null && term.getPred() == null;
      result.setProofStepKind(ProofStepKind.Simple);
      result.setProofStepScope(ProofStepScope.Global);
    }
    return result;
  }
  // TODO: maybe add another checker... but this would be overkill perhaps
//  @Override
//  public ProofCommandInfo visitInstantiation(Instantiation term)
//  {
//    term.
//  }
//
//  @Override
//  public ProofCommandInfo visitInstantiationList(InstantiationList term)
//  {
//    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
//
//    for (Instantiation i : term)
//    {
//      ProofCommandInfo instPCI = i.accept(proofCommandChecker());
//    }
//    result.setProofStepScope(ProofStepScope.Global);
//    return result;
//  }

  @Override
  public ProofCommandInfo visitSorryCommand(SorryCommand term)
  {
    ProofCommandInfo result = factory().getZEvesFactory().createProofCommandInfo();
    // do something about undoing effects ?
    return result;
  }
}
