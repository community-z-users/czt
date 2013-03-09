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
import java.util.regex.Matcher;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.ast.And;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.Directive;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ExprPred;
import net.sourceforge.czt.z.ast.ForallExpr;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.NameList;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.Qnt1Expr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZParaList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.util.Section;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.ConjParaVisitor;
import net.sourceforge.czt.z.visitor.ExprPredVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.PredVisitor;
import net.sourceforge.czt.z.visitor.Qnt1ExprVisitor;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SpecVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.ZParaListVisitor;
import net.sourceforge.czt.z.visitor.ZSchTextVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.LabelUsage;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
import net.sourceforge.czt.zeves.ast.ProofCommand;
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
 * @date Jun 27, 2011
 */
public class PrintVisitor
        extends net.sourceforge.czt.z.util.PrintVisitor
        implements ZEvesVisitor<String>,
        LatexMarkupParaVisitor<String>,
        SpecVisitor<String>,
        ZSectVisitor<String>,
        ZParaListVisitor<String>,
        NarrParaVisitor<String>,
        AxParaVisitor<String>,
        ConjParaVisitor<String>,
        PredVisitor<String>,
        SchExprVisitor<String>,
        ZSchTextVisitor<String>,
        AndPredVisitor<String>,
        ExprPredVisitor<String>,
        Qnt1ExprVisitor<String>,
        RenameExprVisitor<String>,
        ThetaExprVisitor<String>
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

  @Override
  protected String matchOtherStrings(String zNameWord)
  {
    if (zNameWord.indexOf("$") != -1)
    {
      // replaces $ to \$
      //return zNameWord.replaceAll("\\$", "\\\\$");
      return zNameWord.replaceAll(Matcher.quoteReplacement("$"), Matcher.quoteReplacement("\\$"));
    }
    else
    {
      return super.matchOtherStrings(zNameWord);
    }
  }

  @Override
  protected int matchOtherSize(String other)
  {
    int result = super.matchOtherSize(other);

    if (other.indexOf("$") != -1)
    {
      // minus the ammount of "\" added per each dollar
      // unless the dollar is in the end (e.g., x$), the split shouldn't add "+1"
      result = result - other.split(Matcher.quoteReplacement("\\$")).length
               + // if dollar is in the end, then split "x$" = ["x"] (no adjustment)
              // if dollar is in the middle, then split "x$domcheck" = ["x", "domcheck"] (adjust one)
              (other.lastIndexOf("$") + 1 == other.length() ? 0 : 1);
    }
    return result;
  }

  private ZEvesLabel appendBeginEnv(Term term, StringBuilder result)
  {
    ZEvesLabel label = ZEvesUtils.getLabel(term);
    result.append("\\begin");
    if (label != null && label.getLabelAbility().equals(LabelAbility.disabled))
    {
      result.append("[disabled]");
    }
    return label;
  }

  @Override
  public String visitPred(Pred term)
  {
    StringBuilder result = new StringBuilder();
    ZEvesLabel label = ZEvesUtils.getLabel(term);
    if (label!=null)
    {
      result.append(visit(label));
    }
    result.append("\t");
    result.append(term.getClass().getName());
    return result.toString();
  }

  @Override
  public String visitExprPred(ExprPred term)
  {
    return visit(term.getExpr());
  }

  @Override
  public String visitQnt1Expr(Qnt1Expr term)
  {
    StringBuilder result = new StringBuilder();
    boxedSchemaExpr_ = false; // we are on-the-fly in a paragraph, like \forall S @ expr
    if (term instanceof ForallExpr)
    {
      result.append("\\forall ");
    }
    else if (term instanceof ExistsExpr)
    {
      result.append("\\exists ");
    }
    else
    {
      result.append(term.getClass().getSimpleName());
      result.append(" ");
    }
    result.append(visit(term.getSchText()));
    result.append(" @ ");
    result.append(visit(term.getExpr()));
    return result.toString();
  }

  @Override
  public String visitAndPred(AndPred term)
  {
    if (term.getAnd().equals(And.NL) || term.getAnd().equals(And.Semi))
    {
      StringBuilder result = new StringBuilder();
      result.append(visit(term.getLeftPred()));
      result.append("\n");
      result.append(visit(term.getRightPred()));
      return result.toString();
    }
    else
      return visitPred(term);
  }

  @Override
  public String visitThetaExpr(ThetaExpr term)
  {
    StringBuilder result  = new StringBuilder("\\theta ");
    result.append(visit(term.getExpr()));
    result.append(visit(term.getStrokeList()));
    return result.toString();
  }

  @Override
  public String visitRenameExpr(RenameExpr term)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getExpr()));
    currInstKind_ = InstantiationKind.ThmReplacement;
    result.append("[");
    result.append(visit(term.getRenameList()));
    result.append("]");
    currInstKind_ = null;
    return result.toString();
  }

  private boolean boxedSchemaExpr_ = false;
  
  @Override
  public String visitAxPara(AxPara term)
  {
    StringBuilder result = new StringBuilder();
    NameList gen = ZUtils.getAxParaGenFormals(term);
    boolean hasGenerics = gen != null &&
            gen instanceof ZNameList && !((ZNameList)gen).isEmpty();
    if (term.getBox().equals(Box.AxBox))
    {
      if (hasGenerics)
      {
        result.append("\\begin{gendef}[");
        result.append(visit(gen));
        result.append("]");
      }
      else
      {
        result.append("\\begin{axdef}");
      }
      result.append("\n\t");
      result.append(visit(ZUtils.getAxBoxDecls(term)));
      result.append("\n\\where\n\t");
      result.append(visit(ZUtils.getAxBoxPred(term)));
      result.append("\n\\end{");
      result.append(hasGenerics ? "gendef" : "axdef");
      result.append("}\n");
    }
    else if (term.getBox().equals(Box.SchBox))
    {
      appendBeginEnv(term, result);
      result.append("{schema}{");
      result.append(visit(ZUtils.getSchemaName(term)));
      result.append("}");
      if (hasGenerics)
      {
        result.append("[");
        result.append(visit(gen));
        result.append("]");
      }
      result.append("\n\t");
      boxedSchemaExpr_ = true;
      result.append(visit(ZUtils.getSchemaDefExpr(term)));
      result.append("\n\\end{schema}\n");
    }
    else if (term.getBox().equals(Box.OmitBox))
    {
      appendBeginEnv(term, result);
      result.append("{zed}\n\t");
      result.append(visit(ZUtils.getAbbreviationName(term)));
      if (hasGenerics)
      {
        result.append(" [");
        result.append(visit(gen));
        result.append("]");
      }
      boxedSchemaExpr_ = false;
      Expr abbrvExpr = ZUtils.getAbbreviationExpr(term);
      // TODO: here there is a simplification for the schema calculus: I don't have \\defs for S \land T, say
      result.append(abbrvExpr instanceof SchExpr ? " \\defs " : " == ");
      result.append("[ ");
      result.append(visit(abbrvExpr));
      result.append(" ]");
      result.append("\n\\end{zed}\n");
    }
    else
    {
      result.append(term.getClass().getName());
    }
    return result.toString();
  }

  @Override
  public String visitSchExpr(SchExpr term)
  {
    return visit(term.getSchText());
  }

  @Override
  public String visitZSchText(ZSchText term)
  {
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getDeclList()));
    result.append(boxedSchemaExpr_ ? "\n\\where\n\t" : " | ");
    result.append(visit(term.getPred()));
    return result.toString();
  }

  @Override
  public String visitConjPara(ConjPara term)
  {
    StringBuilder result = new StringBuilder();
    ZEvesLabel label = appendBeginEnv(term, result);
    result.append("{theorem}");
    if (term.getName() != null)
    {
      result.append("{");
      if (label != null && !label.getLabelUsage().equals(LabelUsage.none))
      {
        result.append(label.getLabelUsage());
        result.append(" ");
      }
      result.append(term.getName());
      result.append("}");
    }
    NameList gen = term.getNameList();
    boolean hasGenerics = gen != null &&
            gen instanceof ZNameList && !((ZNameList)gen).isEmpty();
    if (hasGenerics)
    {
      result.append("[");
      result.append(visit(gen));
      result.append("]");
    }
    result.append("\n");
    result.append(visit(term.getPred()));
    result.append("\n");
    result.append("\\end{theorem}");
    return result.toString();
  }

  @Override
  public String visitLatexMarkupPara(LatexMarkupPara term)
  {
    StringBuilder result = new StringBuilder();
    for (Directive d : term.getDirective())
    {
      switch (d.getDirectiveType())
      {
        case IN:
          result.append("Zin");
          break;

        case PRE:
          result.append("Zpre");
          break;

        case POST:
          result.append("Zpost");
          break;

        default:
          result.append("Z");
          break;
      }
      if (d.getUnicode().startsWith("U+"))
      {
        result.append("char");
      }
      else
      {
        result.append("word");
      }
      result.append(" ");
      result.append(d.getCommand());
      result.append(" ");
      result.append(d.getUnicode());
      result.append("\n");
    }
    return result.toString();
  }

  @Override
  public String visitSpec(Spec term)
  {
    StringBuilder result = new StringBuilder();
    for (Sect s : term.getSect())
    {
      result.append(visit(s));
    }
    return result.toString();
  }

  @Override
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
    {
      return visitTerm(term);
    }
  }

  @Override
  public String visitZParaList(ZParaList term)
  {
    StringBuilder result = new StringBuilder();
    for (Para p : term)
    {
      result.append(visit(p));
    }
    return result.toString();
  }

  @Override
  public String visitNarrPara(NarrPara term)
  {
    StringBuilder result = new StringBuilder("NarrPara {");
    for (Object o : term.getContent())
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
    switch (term.getNormalizationKind())
    {
      case Conjunctive:
        return "conjunctive";
      case Disjunctive:
        return "disjunctive";
      case Rearrange:
        return "rearrange";
      case Command:
        return "with normalization " + visit(term.getProofCommand());
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
      currInstKind_ = null;
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
      assert term.getExpr() == null && term.getPred() == null
             && term.getNameList() instanceof ZNameList
             && !term.getZNameList().isEmpty() : "with enabled/disabled command cannot have expr or pred and name list must not be empty";
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
    assert term.getProofCommand() == null
           && term.getNameList() == null || term.getNameList() instanceof ZNameList : "subst command must have a subcmd and a Z namelist";
    switch (term.getSubstitutionKind())
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
    switch (term.getRewriteKind())
    {
      case Reduce:
        switch (term.getRewritePower())
        {
          case None:
            return "reduce";
          case Prove:
            return "prove by reduce";
          case Trivial:
            return "INVALID(trivial reduce)";
          default:
            throw new Error();
        }
      case Rewrite:
        switch (term.getRewritePower())
        {
          case None:
            return "rewrite";
          case Prove:
            return "prove by rewrite";
          case Trivial:
            return "trivial rewrite";
          default:
            throw new Error();
        }

      case Simplify:
        switch (term.getRewritePower())
        {
          case None:
            return "simplify";
          case Prove:
            return "INVALID(prove by simplify)";
          case Trivial:
            return "trivial simplify";
          default:
            throw new Error();
        }

      default:
        throw new Error();
    }
  }

  @Override
  public String visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    switch (term.getCaseAnalysisKind())
    {
      case Cases:
        return "cases";
      case Next:
        return "next";
      case Split:
        assert term.getPred() != null : "Invalid split - null predicate";
        return "split " + visit(term.getPred());
      default:
        throw new Error();
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
      currInstKind_ = null;
    }
    return result.toString();
  }

  @Override
  public String visitApplyCommand(ApplyCommand term)
  {
    assert term.getProofCommand() == null
           && term.getNameList() != null
           && term.getNameList() instanceof ZNameList
           && term.getZNameList().size() == 1 : "apply command cannot have subcommand and must have a singleton Z namelist";
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
	assert term != null && term.getInstantiationKind() != null;
    if (currInstKind_ != null && !term.getInstantiationKind().equals(currInstKind_))
      throw new IllegalArgumentException("Inconsistent known instantiation kind. Found " + term.getInstantiationKind() + "; expected " + currInstKind_);
    StringBuilder result = new StringBuilder();
    result.append(visit(term.getZName()));
    result.append(term.getInstantiationKind().equals(InstantiationKind.Quantifier) ? " == " : " := ");
    result.append(visit(term.getExpr()));
    return result.toString();
  }

  @Override
  public String visitInstantiationList(InstantiationList term)
  {
    StringBuilder result = new StringBuilder();
    Iterator<Instantiation> it = term.iterator();
    assert it.hasNext() : "empty instantiations are not allowed";
    result.append(visit(it.next()));
    while (it.hasNext())
    {
      result.append(",\n\t");
      result.append(visit(it.next()));
    }
    it = null;
    return result.toString();
  }

  private boolean isAnyStandardSection(String name)
  {
    for (Section s : Section.values())
    {
      if (s.getName().equals(name))
      {
        return true;
      }
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
    StringBuilder result = new StringBuilder();
    result.append("PCI(S=");
    result.append(String.valueOf(term.getProofStepScope()));
    result.append(" K=");
    result.append(String.valueOf(term.getProofStepKind()));
    result.append(" R=");
    result.append(String.valueOf(term.getProofStepRank()));
    result.append(")");
    return result.toString();
  }

  @Override
  public String visitProofCommandInfoList(ProofCommandInfoList term)
  {
    if (term.isEmpty())
    {
      return "";
    }
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
      it = null;
      return result.toString();
    }
  }

  @Override
  public String visitZEvesLabel(ZEvesLabel term)
  {
    StringBuilder result = new StringBuilder("\\Label{");
    if (!term.getLabelAbility().equals(LabelAbility.none))
    {
      result.append(term.getLabelAbility());
      result.append(" ");
    }
    if (!term.getLabelUsage().equals(LabelUsage.none))
    {
      result.append(term.getLabelUsage());
      result.append(" ");
    }
    result.append(visit(term.getName()));
    result.append("}\n");
    return result.toString();
  }

  @Override
  public String visitZEvesNote(ZEvesNote term)
  {
    StringBuilder result = new StringBuilder();
    result.append("\\znote{");
    result.append(term.getNote());
    result.append("}\n");
    return result.toString();
  }

  @Override
  public String visitSorryCommand(SorryCommand term)
  {
    if (term.getKeepGoal())
      return "oops";
    else
      return "sorry";
  }

}
