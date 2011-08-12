/*
Copyright (C) 2004, 2005, 2006 Petra Malik, Leo Freitas
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
package net.sourceforge.czt.print.zeves;

import java.util.Properties;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.parser.zeves.ZEvesProofKeyword;
import net.sourceforge.czt.parser.zeves.ZEvesProofToken;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.z.ast.ConjPara;
import net.sourceforge.czt.z.ast.ParenAnn;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZRenameList;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.visitor.RenameExprVisitor;
import net.sourceforge.czt.zeves.ast.ApplyCommand;
import net.sourceforge.czt.zeves.ast.CaseAnalysisCommand;
import net.sourceforge.czt.zeves.ast.Instantiation;
import net.sourceforge.czt.zeves.ast.InstantiationKind;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.NormalizationCommand;
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
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.ast.ZEvesNote;
import net.sourceforge.czt.zeves.util.ZEvesUtils;
import net.sourceforge.czt.zeves.visitor.ZEvesVisitor;

/**
 * An Circus visitor used for printing.
 *
 * @author Petra Malik, Leo Freitas
 */
public class ZEvesPrintVisitor
        extends net.sourceforge.czt.print.z.ZPrintVisitor
        implements ZEvesVisitor<Object>, RenameExprVisitor<Object>
{

  private final WarningManager warningManager_;

  /**
   * Creates a new Object-Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   * @param printer
   * @param wm
   */
  public ZEvesPrintVisitor(ZPrinter printer, WarningManager wm)
  {
    super(printer);
    warningManager_ = wm;
  }

  public ZEvesPrintVisitor(ZPrinter printer, Properties properties, WarningManager wm)
  {
    super(printer, properties);
    warningManager_ = wm;
  }

  @Override
  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    final boolean braces = renameExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(renameExpr.getExpr());
    print(ZToken.LSQUARE);
    if (renameExpr.getRenameList() instanceof ZRenameList)
      printTermList(renameExpr.getZRenameList());
    else
    {
      currInstKind_ = InstantiationKind.ThmReplacement;
      printTermList(ZEvesUtils.getInstantiationListFromExpr(renameExpr));
      currInstKind_ = null;
    }
    print(ZToken.RSQUARE);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  @Override
  public Object visitConjPara(ConjPara conjPara)
  {
    print(ZToken.ZED);
    String name = conjPara.getName();
    if (name == null || name.isEmpty())
      throw new PrintException("Z/Eves theorems must have names");

    ZEvesLabel label = ZEvesUtils.getLabel(conjPara);
    if (label != null && label.getAbility().equals(LabelAbility.disabled))
    {
        print(ZEvesProofToken.DISABLEDTHMTAG);
    }
    print(ZKeyword.THEOREM);
    if (label != null)
    {
      switch (label.getUsage())
      {
        case rule:
          print(ZEvesProofKeyword.THMRULE);
          break;
        case grule:
          print(ZEvesProofKeyword.THMGRULE);
          break;
        case frule:
          print(ZEvesProofKeyword.THMFRULE);
          break;
        case axiom:
          print(ZEvesProofKeyword.THMAXIOM);
          break;
        case none:
        default:
          // do nothing
          break;
      }
    }
    print(ZToken.DECORWORD, new Decorword(name));
    printGenericFormals(conjPara.getNameList());
    //no need for print(ZKeyword.CONJECTURE);
    visit(conjPara.getPred());
    print(ZToken.END);
    return null;
  }

  @Override
  public Object visitProofScript(ProofScript term)
  {
    print(ZEvesProofToken.ZPROOF);
    visit(term.getName());
    printTermList(term.getProofCommandList(), ZEvesProofToken.ZPROOFCOMMANDSEP);
    if (!term.getProofCommandList().isEmpty())
      print(ZEvesProofToken.ZPROOFCOMMANDSEP);
    print(ZToken.END);
    return null;
  }

  @Override
  public Object visitProofCommandList(ProofCommandList term)
  {
    throw new PrintException(ZEvesPrintMessage.MSG_PRINTTERMLIST_EXCEPTION.format(term.getClass().getName()));
  }
  
  @Override
  public String visitInstantiationList(InstantiationList term)
  {
    throw new PrintException(ZEvesPrintMessage.MSG_PRINTTERMLIST_EXCEPTION.format(term.getClass().getName()));
  }

  @Override
  public Object visitProofCommandInfoList(ProofCommandInfoList term)
  {
    throw new PrintException(ZEvesPrintMessage.MSG_PRINTTERMLIST_EXCEPTION.format(term.getClass().getName()));
  }


  @Override
  public Object visitNormalizationCommand(NormalizationCommand term)
  {
    switch (term.getKind())
    {
      case Conjunctive:
        print(ZEvesProofKeyword.CONJUNCTIVE);
        break;
      case Disjunctive:
        print(ZEvesProofKeyword.DISJUNCTIVE);
        break;
      case Rearrange:
        print(ZEvesProofKeyword.REARRANGE);
        break;
      case Command:
        print(ZEvesProofKeyword.WITH);
        print(ZEvesProofKeyword.NORMALIZATION);
        visit(term.getProofCommand());
        break;
      default:
        throw new Error();
    }
    return null;
  }

  private InstantiationKind currInstKind_ = null;

  @Override
  public Object visitUseCommand(UseCommand term)
  {
    print(ZEvesProofKeyword.USE);
    visit(term.getTheoremRef());
    if (term.getInstantiationList() != null)
    {
      currInstKind_ = InstantiationKind.ThmReplacement;
      if (!term.getInstantiationList().isEmpty())
      {
        print(ZToken.LSQUARE);
        printTermList(term.getInstantiationList()); // use default COMMA separator
        print(ZToken.RSQUARE);
      }
      currInstKind_ = null;
    }
    return null;
  }

  @Override
  public Object visitWithCommand(WithCommand term)
  {
    print(ZEvesProofKeyword.WITH);
    if(term.getExpr() != null)
    {
      if (term.getPred() != null)
        throw new PrintException("with expression command cannot have pred");
      print(ZEvesProofKeyword.EXPRESSION);
      print(ZToken.LPAREN);
      visit(term.getExpr());
      print(ZToken.RPAREN);
    }
    else if (term.getPred() != null)
    {
      if (term.getExpr() != null)
        throw new PrintException("with predicate command cannot have expr");
      print(ZEvesProofKeyword.PREDICATE);
      print(ZToken.LPAREN);
      visit(term.getPred());
      print(ZToken.RPAREN);
    }
    else if (term.getEnabled() != null)
    {
      if (!(term.getExpr() == null && term.getPred() == null
             && term.getNameList() instanceof ZNameList
             && !term.getZNameList().isEmpty()))
        throw new PrintException("with enabled/disabled command cannot have expr or pred and name list must not be empty");
      print(term.getEnabled() ? ZEvesProofKeyword.ENABLED : ZEvesProofKeyword.DISABLED);
      print(ZToken.LPAREN);
      visit(term.getNameList());
      print(ZToken.RPAREN);
    }
    else
    {
      throw new PrintException("Unknown WithCommand: neither expression, predicate, enabled or disabled.");
    }
    if(term.getProofCommand() == null)
    {
      throw new PrintException("with command must have an inner command");
    }
    visit(term.getProofCommand());
    return null;
  }

  @Override
  public Object visitSubstitutionCommand(SubstitutionCommand term)
  {
    if (!(term.getProofCommand() == null
           && term.getNameList() == null || term.getNameList() instanceof ZNameList))
      throw new PrintException("subst command not must have a subcmd and a Z namelist");
    switch (term.getKind())
    {
      case Invoke:
        if (term.getExpr() != null)
          throw new PrintException("invoke command cannot have an expression");

        print(ZEvesProofKeyword.INVOKE);
        if (term.getPred() != null)
        {
          print(ZEvesProofKeyword.PREDICATE);
          visit(term.getPred());
        }
        else if (term.getNameList() != null)
        {
          if (term.getZNameList().size() != 1)
            throw new PrintException("invoke cmd only on a single name");
          visit(term.getZNameList().get(0));
        }
        break;
      case Equality:
        if (term.getPred() != null)
          throw new PrintException("equality substitute command cannot have a predicate");
        print(ZEvesProofKeyword.EQUALITY);
        print(ZEvesProofKeyword.SUBSTITUTE);
        if (term.getExpr() != null)
        {
          visit(term.getExpr());
        }
        break;
      default:
        throw new Error();
    }
    return null;
  }

  @Override
  public Object visitSimplificationCommand(SimplificationCommand term)
  {
    switch (term.getKind())
    {
      case Reduce:
        switch (term.getPower())
        {
          case None:
            print(ZEvesProofKeyword.REDUCE);
            break;
          case Prove:
            print(ZEvesProofKeyword.PROVE);
            print(ZEvesProofKeyword.BY);
            print(ZEvesProofKeyword.REDUCE);
            break;
          case Trivial:
            throw new PrintException("INVALID(trivial reduce)");
          default:
            throw new PrintException();
        }
        break;
      case Rewrite:
        switch (term.getPower())
        {
          case None:
            print(ZEvesProofKeyword.REWRITE);
            break;
          case Prove:
            print(ZEvesProofKeyword.PROVE);
            print(ZEvesProofKeyword.BY);
            print(ZEvesProofKeyword.REWRITE);
            break;
          case Trivial:
            print(ZEvesProofKeyword.TRIVIAL);
            print(ZEvesProofKeyword.REWRITE);
            break;
          default:
            throw new PrintException();
        }
        break;
      case Simplify:
        switch (term.getPower())
        {
          case None:
            print(ZEvesProofKeyword.SIMPLIFY);
            break;
          case Prove:
            throw new PrintException("INVALID(prove by simplify)");
          case Trivial:
            print(ZEvesProofKeyword.TRIVIAL);
            print(ZEvesProofKeyword.SIMPLIFY);
            break;
          default:
            throw new PrintException();
        }
        break;
      default:
        throw new PrintException();
    }
    return null;
  }

  @Override
  public Object visitCaseAnalysisCommand(CaseAnalysisCommand term)
  {
    switch (term.getKind())
    {
      case Cases:
        print(ZEvesProofKeyword.CASES);
        break;
      case Next:
        print(ZEvesProofKeyword.NEXT);
        break;
      case Split:
        print(ZEvesProofKeyword.SPLIT);
        if (term.getPred() == null)
          throw new PrintException("Invalid split - null predicate");
        visit(term.getPred());
        break;
      default:
        throw new PrintException();
    }
    return null;
  }

  @Override
  public Object visitQuantifiersCommand(QuantifiersCommand term)
  {
    if (term.getInstantiationList() == null || term.getInstantiationList().isEmpty())
    {
      print(ZEvesProofKeyword.PRENEX);
    }
    else
    {
      if (!(term.getInstantiationList() != null && !term.getInstantiationList().isEmpty()))
        throw new PrintException("quantifiers instantiation list cannot be empty");
      print(ZEvesProofKeyword.INSTANTIATE);
      currInstKind_ = InstantiationKind.Quantifier;
      printTermList(term.getInstantiationList());
      currInstKind_ = null;
    }
    return null;
  }

  @Override
  public Object visitApplyCommand(ApplyCommand term)
  {
    if (!(term.getProofCommand() == null
           && term.getNameList() != null
           && term.getNameList() instanceof ZNameList
           && term.getZNameList().size() == 1))
      throw new PrintException("apply command cannot have subcommand and must have a singleton Z namelist");
    print(ZEvesProofKeyword.APPLY);
    visit(term.getZNameList().get(0));
    if (term.getPred() != null)
    {
      if (term.getExpr() != null)
        throw new PrintException("apply to predicate cannot have an expression");
      print(ZEvesProofKeyword.TO);
      print(ZEvesProofKeyword.PREDICATE);
      visit(term.getPred());
    }
    else if (term.getExpr() != null)
    {
      if (term.getPred() != null)
        throw new PrintException("apply to expression cannot have an predicate");
      print(ZEvesProofKeyword.TO);
      print(ZEvesProofKeyword.EXPRESSION);
      visit(term.getExpr());
    }
    return null;
  }

  @Override
  public String visitInstantiation(Instantiation term)
  {
    if (!term.getKind().equals(currInstKind_))
      throw new PrintException("inconsistent instantiation kind. found " + term.getKind() + "; expected " + currInstKind_);
    visit(term.getName());
    print(currInstKind_ == InstantiationKind.Quantifier ? ZKeyword.DEFEQUAL : ZEvesProofKeyword.THMREPLACEMENT);
    visit(term.getExpr());
    return null;
  }

  @Override
  public Object visitProofType(ProofType term)
  {
    print(ZKeyword.COLON);
    printTermList(term.getProofCommandInfoList(), ZToken.NL);
    return null;
  }

  @Override
  public Object visitZEvesLabel(ZEvesLabel term)
  {
    print(ZEvesProofToken.LLABEL);
    switch (term.getAbility())
    {
      case disabled:
        print(ZEvesProofToken.DISABLEDTHMTAG);
        break;
      case enabled:
      case none:
      default:
        break;
    }
    switch (term.getUsage())
    {
      case rule:
        print(ZEvesProofKeyword.THMRULE);
        break;
      case frule:
        print(ZEvesProofKeyword.THMFRULE);
        break;
      case grule:
        print(ZEvesProofKeyword.THMGRULE);
        break;
      case axiom:
        print(ZEvesProofKeyword.THMAXIOM);
        break;
      default:
        break;
    }
    visit(term.getName());
    print(ZEvesProofToken.RLABEL);
    return null;
  }

  @Override
  public Object visitZEvesNote(ZEvesNote term)
  {
    print(ZEvesProofToken.LZNOTE);
    printDecorword(term.getNote());
    print(ZEvesProofToken.RZNOTE);
    return null;
  }

  @Override
  public Object visitProofCommandInfo(ProofCommandInfo term)
  {
    print(ZToken.LPAREN);
    printDecorword(term.getProofStepScope().toString());
    print(ZKeyword.COMMA);
    printDecorword(term.getProofStepKind().toString());
    print(ZKeyword.COMMA);
    printDecorword(term.getProofStepRank().toString());
    print(ZToken.RPAREN);
    return null;
  }
}
