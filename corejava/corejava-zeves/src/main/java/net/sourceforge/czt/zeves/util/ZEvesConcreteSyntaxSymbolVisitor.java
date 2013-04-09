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

package net.sourceforge.czt.zeves.util;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.util.IsEmptyNameList;
import net.sourceforge.czt.z.util.StandardZ;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofCommandInfoList;
import net.sourceforge.czt.zeves.ast.ProofCommandList;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.ast.QuantifiersCommand;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SorryCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionCommand;
import net.sourceforge.czt.zeves.ast.UseCommand;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.ast.ZEvesNote;
import net.sourceforge.czt.zeves.visitor.ZEvesVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jul 8, 2011
 */
public class ZEvesConcreteSyntaxSymbolVisitor
        implements ZEvesVisitor<ZEvesConcreteSyntaxSymbol>
{
  public ZEvesConcreteSyntaxSymbolVisitor()
  {
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitZEvesLabel(ZEvesLabel term)
  {
    return ZEvesConcreteSyntaxSymbol.ZEVESLABEL;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitZEvesNote(ZEvesNote term)
  {
    return ZEvesConcreteSyntaxSymbol.ZEVESNOTE;
  }

  public interface Utils
    extends IsEmptyNameList
  {
  }

  public static class UtilsImpl
    extends StandardZ
    implements Utils
  {
  }


  protected ZEvesConcreteSyntaxSymbol visit(Term term)
  {
    if (term != null) return term.accept(this);
    return null;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitProofType(ProofType term)
  {
    return null;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitNormalizationCommand(NormalizationCommand term)
  {
    switch (term.getNormalizationKind())
    {
      case Conjunctive: return ZEvesConcreteSyntaxSymbol.CONJUNCTIVE_CMD;
      case Disjunctive: return ZEvesConcreteSyntaxSymbol.DISJUNCTIVE_CMD;
      case Rearrange:   return ZEvesConcreteSyntaxSymbol.REARRANGE_CMD;
      case Command:     return ZEvesConcreteSyntaxSymbol.WITH_NORM_CMD.add(visit(term.getProofCommand()));
      default:
        throw new Error();
    }
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitUseCommand(UseCommand term)
  {
    if (!term.getInstantiationList().isEmpty())
      return ZEvesConcreteSyntaxSymbol.USE_COMPLEX_CMD;
    else if(term.getTheoremRef().getExplicit())
      return ZEvesConcreteSyntaxSymbol.USE_GENTHM_CMD;
    else
      return ZEvesConcreteSyntaxSymbol.USE_TRIVIAL_CMD;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitProofCommandList(ProofCommandList term)
  {
    return ZEvesConcreteSyntaxSymbol.ZPROOF_CMD_LIST;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitWithCommand(WithCommand term)
  {
    if (term.getPred() != null)
      return ZEvesConcreteSyntaxSymbol.WITH_PRED_CMD.add(visit(term.getProofCommand()));
    else if (term.getExpr() != null)
      return ZEvesConcreteSyntaxSymbol.WITH_EXPR_CMD.add(visit(term.getProofCommand()));
    else if (term.getEnabled() != null)
    {
      if (term.getEnabled())
        return ZEvesConcreteSyntaxSymbol.WITH_ENABLED_CMD.add(visit(term.getProofCommand()));
      else
        return ZEvesConcreteSyntaxSymbol.WITH_DISABLED_CMD.add(visit(term.getProofCommand()));
    }
    else
      return null;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitSubstitutionCommand(SubstitutionCommand term)
  {
    switch (term.getSubstitutionKind())
    {
      case Invoke:
        if (term.getPred() != null)
          return ZEvesConcreteSyntaxSymbol.INVOKE_PRED_CMD;
        else if (term.getNameList() != null && !term.getZNameList().isEmpty())
          return ZEvesConcreteSyntaxSymbol.INVOKE_NAME_CMD;
        else
          return ZEvesConcreteSyntaxSymbol.INVOKE_GLOBAL_CMD;
      case Equality:
        if (term.getExpr() != null)
          return ZEvesConcreteSyntaxSymbol.EQUALITY_LOCAL_CMD;
        else
          return ZEvesConcreteSyntaxSymbol.EQUALITY_GLOBAL_CMD;
      default: return null;
    }
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitSorryCommand(SorryCommand term)
  {
    if (term.getKeepGoal())
      return ZEvesConcreteSyntaxSymbol.SORRY_COMMAND;
    else
      return ZEvesConcreteSyntaxSymbol.OOPS_COMMAND;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitProofScript(ProofScript term)
  {
    return ZEvesConcreteSyntaxSymbol.ZPROOF_PARA;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitSimplificationCommand(SimplificationCommand term)
  {
    switch (term.getRewriteKind())
    {
      case Reduce  :
         switch (term.getRewritePower())
         {
           case None:     return ZEvesConcreteSyntaxSymbol.REDUCE_CMD;
           case Prove:    return ZEvesConcreteSyntaxSymbol.PROVE_RD_CMD;
           case Trivial:  return null;
           default: return null;
         }
      case Rewrite :
         switch (term.getRewritePower())
         {
           case None:     return ZEvesConcreteSyntaxSymbol.REWRITE_CMD;
           case Prove:    return ZEvesConcreteSyntaxSymbol.PROVE_RW_CMD;
           case Trivial:  return ZEvesConcreteSyntaxSymbol.TRIVIAL_RW_CMD;
           default: return null;
         }

      case Simplify:
         switch (term.getRewritePower())
         {
           case None:     return ZEvesConcreteSyntaxSymbol.SIMPLIFY_CMD;
           case Prove:    return null;
           case Trivial:  return ZEvesConcreteSyntaxSymbol.TRIVIAL_SIMP_CMD;
           default: throw new Error();
         }

      default:     return null;
    }
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitProofCommandInfo(ProofCommandInfo term)
  {
    return null;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    switch (term.getCaseAnalysisKind())
    {
      case Cases:   return ZEvesConcreteSyntaxSymbol.CASES_CMD;
      case Next:    return ZEvesConcreteSyntaxSymbol.NEXT_CMD;
      case Split:   return ZEvesConcreteSyntaxSymbol.SPLIT_CMD;
      default:      return null;
    }
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitQuantifiersCommand(QuantifiersCommand term)
  {
    if (term.getInstantiationList() == null || term.getInstantiationList().isEmpty())
      return ZEvesConcreteSyntaxSymbol.PRENEX_CMD;
    else
      return ZEvesConcreteSyntaxSymbol.INSTANTIATE_CMD;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitApplyCommand(ApplyCommand term)
  {
    if (term.getExpr() != null)
      return ZEvesConcreteSyntaxSymbol.APPLY_EXPR_CMD;
    else if (term.getPred() != null)
      return ZEvesConcreteSyntaxSymbol.APPLY_PRED_CMD;
    else
      return ZEvesConcreteSyntaxSymbol.APPLY_GLOBAL_CMD;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitInstantiation(Instantiation term)
  {
    switch (term.getInstantiationKind())
    {
      case Quantifier:     return ZEvesConcreteSyntaxSymbol.INSTANTIATION;
      case ThmReplacement: return ZEvesConcreteSyntaxSymbol.THMREPLACEMENT;
      default: return null;
    }
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitProofCommandInfoList(ProofCommandInfoList term)
  {
    return null;
  }

  @Override
  public ZEvesConcreteSyntaxSymbol visitInstantiationList(InstantiationList term)
  {
    return ZEvesConcreteSyntaxSymbol.INSTANTIATION_LIST;
  }
}
