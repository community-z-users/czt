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

import java.util.Iterator;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.Section;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.ProofCommand;
import net.sourceforge.czt.zeves.ast.ProofCommandInfo;
import net.sourceforge.czt.zeves.ast.ProofCommandInfoList;
import net.sourceforge.czt.zeves.ast.ProofCommandList;
import net.sourceforge.czt.zeves.ast.ProofScript;
import net.sourceforge.czt.zeves.ast.ProofType;
import net.sourceforge.czt.zeves.ast.QuantifiersCommand;
import net.sourceforge.czt.zeves.ast.SimplificationCommand;
import net.sourceforge.czt.zeves.ast.SubstitutionCommand;
import net.sourceforge.czt.zeves.ast.UseCommand;
import net.sourceforge.czt.zeves.ast.WithCommand;
import net.sourceforge.czt.zeves.visitor.ZEvesVisitor;

/**
 *
 * @author Leo Freitas
 * @date Jun 27, 2011
 */
public class PrintVisitor 
  extends net.sourceforge.czt.z.util.PrintVisitor
  implements ZEvesVisitor<String>,
             SpecVisitor<String>,
             ZSectVisitor<String>,
             ZParaListVisitor<String>,
             NarrParaVisitor<String>
{

  private InstantiationKind currInstKind_ = null;

  public PrintVisitor()
  {
    this(false);
  }

  public PrintVisitor(boolean printUnicode)
  {
    super(printUnicode);
  }

  public String visitSpec(Spec term)
  {
    StringBuilder result = new StringBuilder();
    for(Sect s : term.getSect())
    {
      result.append(visit(s));
    }
    return result.toString();
  }

  public String visitZSect(ZSect term)
  {
    if (!isAnyStandardSection(term.getName()))
    {
      StringBuilder result = new StringBuilder();
      result.append(term.getName());
      result.append("\n");
      result.append(visit(term.getZParaList()));
      return result.toString();
    }
    else
      return visitTerm(term);
  }

  public String visitZParaList(ZParaList term)
  {
    StringBuilder result = new StringBuilder();
    for(Para p : term)
    {
      result.append(visit(p));
    }
    return result.toString();
  }

  public String visitNarrPara(NarrPara term)
  {
    StringBuilder result = new StringBuilder("NarrPara {");
    for(Object o : term.getContent())
    {
      if (o instanceof Term)
      {
        result.append(visit(term));
      }
      else //if (o instanceof String)
      {
        result.append(String.valueOf(o));
      }
    }
    result.append("}\n");
    return result.toString();
  }

  @Override
  public String visitProofScript(ProofScript term)
  {
    StringBuilder result = new StringBuilder("\\begin{zproof}[");
    result.append(visit(term.getName()));
    result.append("]\n");
    result.append(visit(term.getProofCommandList()));
    result.append("\\end{zproof}\n");
    return result.toString();
  }

  @Override
  public String visitProofCommandList(ProofCommandList term)
  {
    StringBuilder result = new StringBuilder();
    for (ProofCommand pc : term)
    {
      result.append(visit(pc));
      result.append(";\n");
    }
    return result.toString();
  }

  @Override
  public String visitNormalizationCommand(NormalizationCommand term)
  {
    switch (term.getKind())
    {
      case Conjunctive: return "conjunctive";
      case Disjunctive: return "disjunctive";
      case Rearrange:   return "rearrange";
      case Command:     return "with normalization " + visit(term.getProofCommand());
      default:
        throw new Error();
    }
  }

  @Override
  public String visitUseCommand(UseCommand term)
  {
    StringBuilder result = new StringBuilder("use ");
    result.append(visit(term.getTheoremRef()));
    if (term.getInstantiationList() != null)
    {
      currInstKind_ = InstantiationKind.ThmReplacement;
      if (!term.getInstantiationList().isEmpty())
      {
        result.append("[");
        result.append(visit(term.getInstantiationList()));
        result.append("]");
      }
    }
    return result.toString();
  }

  @Override
  public String visitWithCommand(WithCommand term)
  {
    assert term.getProofCommand() != null : "with command must have an inner command";
    StringBuilder result = new StringBuilder("with ");
    if (term.getExpr() != null)
    {
      assert term.getPred() == null : "with expression command cannot have pred"; //&& term.getZNameList().isEmpty();
      result.append("expression (");
      result.append(visit(term.getExpr()));
      result.append(") ");
    }
    else if (term.getPred() != null)
    {
      assert term.getExpr() == null : "with predicate command cannot have expr";
      result.append("predicate (");
      result.append(visit(term.getPred()));
      result.append(") ");
    }
    else if (term.getEnabled() != null)
    {
      assert term.getExpr() == null && term.getPred() == null &&
             term.getNameList() instanceof ZNameList &&
             !term.getZNameList().isEmpty() : "with enabled/disabled command cannot have expr or pred and name list must not be empty";
      result.append(term.getEnabled() ? "enabled " : "disabled ");
      result.append("(");
      result.append(visit(term.getZNameList()));
      result.append(") ");
    }
    else
    {
      result.append("ERROR");
    }
    result.append(visit(term.getProofCommand()));
    return result.toString();
  }

  @Override
  public String visitSubstitutionCommand(SubstitutionCommand term)
  {
    assert term.getProofCommand() == null &&
           term.getNameList() == null || term.getNameList() instanceof ZNameList : "subst command must have a subcmd and a Z namelist";
    switch (term.getKind())
    {
      case Invoke:
         assert term.getExpr() == null : "invoke command cannot have an expression";
         if (term.getPred() != null)
         {
           return "invoke predicate " + visit(term.getPred());
         }
         else if (term.getNameList() == null || term.getZNameList().isEmpty())
         {
           return "invoke";
         }
         else
         {
           assert term.getNameList() != null && term.getZNameList().size() == 1 : "invoke cmd only on a single name";
           return "invoke " + visit(term.getZNameList().get(0));
         }
      case Equality:
         assert term.getPred() == null : "equality substitute command cannot have a predicate";
         if (term.getExpr() != null)
         {
           return "equality substitute " + visit(term.getExpr());
         }
         else
         {
           return "equality substitute";
         }
      default:
        throw new Error();
    }
  }

  @Override
  public String visitSimplificationCommand(SimplificationCommand term)
  {
    switch (term.getKind())
    {
      case Reduce  :
         switch (term.getPower())
         {
           case None:     return "reduce";
           case Prove:    return "prove by reduce";
           case Trivial:  return "INVALID(trivial reduce)";
           default: throw new Error();
         }
      case Rewrite :
         switch (term.getPower())
         {
           case None:     return "rewrite";
           case Prove:    return "prove by rewrite";
           case Trivial:  return "trivial rewrite";
           default: throw new Error();
         }

      case Simplify:
         switch (term.getPower())
         {
           case None:     return "simplify";
           case Prove:    return "INVALID(prove by simplify)";
           case Trivial:  return "trivial simplify";
           default: throw new Error();
         }

      default:      throw new Error();
    }
  }

  @Override
  public String visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    switch (term.getKind())
    {
      case Cases:   return "cases";
      case Next:    return "next";
      case Split:   return "split " + visit(term.getPred());
      default:      throw new Error();
    }
  }

  @Override
  public String visitQuantifiersCommand(QuantifiersCommand term)
  {
    StringBuilder result = new StringBuilder();
    if (term.getInstantiationList() == null || term.getInstantiationList().isEmpty())
    {
      result.append("prenex");
    }
    else
    {
      assert term.getInstantiationList() != null && !term.getInstantiationList().isEmpty() : "quantifiers instantiation list cannot be empty";
      result.append("instantiate ");
      currInstKind_ = InstantiationKind.Quantifier;
      result.append(visit(term.getInstantiationList()));
    }
    return result.toString();
  }

  @Override
  public String visitApplyCommand(ApplyCommand term)
  {
    assert term.getProofCommand() == null &&
           term.getNameList() != null &&
           term.getNameList() instanceof ZNameList &&
           term.getZNameList().size() == 1 : "apply command cannot have subcommand and must have a singleton Z namelist";
    StringBuilder result = new StringBuilder("apply ");
    result.append(visit(term.getZNameList().get(0)));
    if (term.getPred() != null)
    {
      assert term.getExpr() == null : "apply to predicate cannot have an expression";
      result.append(" to predicate ");
      result.append(visit(term.getPred()));
    }
    else if (term.getExpr() != null)
    {
      assert term.getPred() == null : "apply to expression cannot have an predicate";
      result.append(" to expression "); // )");
      result.append(visit(term.getExpr()));
      //result.append(")");
    }
    return result.toString();
  }

  @Override
  public String visitInstantiation(Instantiation term)
  {
    assert currInstKind_ == term.getKind() : "inconsistent instantiation kind. found " + term.getKind() + "; expected " + currInstKind_;
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getZName()));
    result.append(currInstKind_ == InstantiationKind.Quantifier ? " == " : " := ");
    result.append(visit(term.getExpr()));
    return result.toString();
  }

  @Override
  public String visitInstantiationList(InstantiationList term)
  {
    StringBuilder result = new StringBuilder();
    Iterator<Instantiation> it = term.iterator();
    assert it.hasNext() : "empty instantiations are not allowed for instantiation kind " + currInstKind_;
    result.append(visit(it.next()));
    while (it.hasNext())
    {
      result.append(",\n\t");
      result.append(visit(it.next()));
    }
    return result.toString();
  }

  private boolean isAnyStandardSection(String name)
  {
    for(Section s : Section.values())
    {
      if (s.getName().equals(name)) return true;
    }
    return false;
  }

  @Override
  public String visitProofType(ProofType term)
  {
    return " : " + visit(term.getProofCommandInfoList());
  }

  @Override
  public String visitProofCommandInfo(ProofCommandInfo term)
  {
    return term.getProofStepScope().toString() + " " +
           term.getProofStepKind().toString() + " " +
           term.getProofStepRank().toString();
  }

  @Override
  public String visitProofCommandInfoList(ProofCommandInfoList term)
  {
    if (term.isEmpty())
      return "";
    else
    {
      StringBuilder result = new StringBuilder();
      long step = 1;
      Iterator<ProofCommandInfo> it = term.iterator();
      result.append(step);
      result.append(" = ");
      result.append(visit(it.next()));
      while (it.hasNext())
      {
        step++;
        result.append("\n ");
        result.append(step);
        result.append(" = ");
        result.append(visit(it.next()));
      }
      return result.toString();
    }
  }
}
