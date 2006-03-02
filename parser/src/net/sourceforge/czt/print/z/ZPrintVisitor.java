/*
  Copyright (C) 2004, 2005, 2006 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.parser.z.Keyword;
import net.sourceforge.czt.parser.z.TokenName;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class ZPrintVisitor
  extends AbstractPrintVisitor
  implements TermVisitor, ListTermVisitor, ZVisitor,
             ApplicationVisitor, OperatorApplicationVisitor,
             PrintParagraphVisitor,
             PrintPredicateVisitor, PrintExpressionVisitor
{
  public static int Z = 0;

  /**
   * Creates a new Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public ZPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }

  protected void zPrint(ZToken token)
  {
    print(token);
  }

  protected void zPrint(Keyword keyword)
  {
    print(keyword);
  }

  protected void zPrint(TokenName tokenName)
  {
    print(new ZToken(tokenName));
  }

  protected void zPrint(TokenName tokenName, Object spelling)
  {
    print(new ZToken(tokenName, spelling));
  }

  public Object visitTerm(Term term)
  {
    throw new CztException("Unexpected term " + term);
  }

  public Object visitListTerm(ListTerm listTerm)
  {
    for (Iterator iter = listTerm.iterator(); iter.hasNext();) {
      Object o = iter.next();
      if (o instanceof Term) {
        Term t = (Term) o;
        visit(t);
      }
    }
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    throw new UnsupportedOperationException("Unexpeced term AndPred");
  }

  public Object visitAndExpr(AndExpr andExpr)
  {
    final boolean braces = andExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(andExpr.getLeftExpr());
    printAnd();
    visit(andExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitAxPara(AxPara axPara)
  {
    throw new UnsupportedOperationException("Unexpeced term AxPara");
  }

  /**
   * Prints the first term followed by the symbol followed by the
   * second term.
   */
  private void print(Term t1, String symbol, Term t2)
  {
    if (symbol == null) throw new CztException();
    visit(t1);
    zPrint(TokenName.DECORWORD, new Decorword(symbol));
    visit(t2);
  }

  /**
   * If the given RefExpr is a reference to a binary operator,
   * the name of the operator (without underscore characters)
   * is returned; otherwise null.
   *
   * TODO: What to do about the expressions in RefExpr?
   */
  private String getBinOperatorName(RefExpr refExpr)
  {
    String result = null;
    String word = refExpr.getZRefName().getWord();
    String[] split = word.split(" ");
    final int expectedLength = 4;
    final int third = 3;
    if (split.length == expectedLength &&
        split[1].equals("_") && split[third].equals("_")) {
      result = split[2];
    }
    if (result == null) {
      String message =
        "ZPrintVisitor: getBinOperatorName of " + word + " failed.";
      message += " split is " + split + " of length " + split.length;
      throw new CztException(message);
    }
    return result;
  }

  public Object visitApplication(Application appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(appl.getLeftExpr());
    visit(appl.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  /**
   * Throws an unsupported operation exception.
   * ApplExpr terms are not part of a print tree.  They are converted
   * to either an OperatorApplication or an Application by the
   * AstToPrintTreeVisitor.
   */
  public Object visitApplExpr(ApplExpr applExpr)
  {
    throw new CztException("Unexpected term " + applExpr);
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    final boolean braces = bindExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    zPrint(TokenName.LBIND);
    printTermList(((ZDeclList) bindExpr.getDeclList()).getDecl());
    zPrint(TokenName.RBIND);
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    final boolean braces = bindSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(bindSelExpr.getExpr());
    printKeyword(ZString.DOT);
    visit(bindSelExpr.getRefName());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitBranch(Branch branch)
  {
    visit(branch.getDeclName());
    if (branch.getExpr() != null) {
      zPrint(TokenName.LDATA);
      visit(branch.getExpr());
      zPrint(TokenName.RDATA);
    }
    return null;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    final boolean braces = compExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(compExpr.getLeftExpr());
    printKeyword(ZString.ZCOMP);
    visit(compExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    final boolean braces = condExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.IF);
    visit(condExpr.getPred());
    printKeyword(ZString.THEN);
    visit(condExpr.getLeftExpr());
    printKeyword(ZString.ELSE);
    visit(condExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    zPrint(TokenName.ZED);
    if (conjPara.getDeclName().size() > 0) {
      zPrint(TokenName.LSQUARE);
      visit(conjPara.getDeclName());
      zPrint(TokenName.RSQUARE);
    }
    printKeyword(ZString.CONJECTURE);
    visit(conjPara.getPred());
    zPrint(TokenName.END);
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    visit(constDecl.getDeclName());
    printKeyword(ZString.DEFEQUAL);
    visit(constDecl.getExpr());
    return null;
  }

  public Object visitZDeclName(ZDeclName declName)
  {
    OperatorName op = declName.getOperatorName();
    if (op == null) {
      zPrint(TokenName.DECORWORD,
            new Decorword(declName.getWord(), declName.getStroke()));
      return null;
    }
    for (Iterator iter = op.iterator(); iter.hasNext();) {
      zPrint(TokenName.DECORWORD, new Decorword((String) iter.next()));
    }
    return null;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    final boolean braces = decorExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitDirective(Directive directive)
  {
    // do nothing for now
    return null;
  }

  public Object visitExists1Expr(Exists1Expr exists1Expr)
  {
    final boolean braces = exists1Expr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.EXIONE);
    visit(exists1Expr.getSchText());
    printKeyword(ZString.SPOT);
    visit(exists1Expr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    final boolean braces = exists1Pred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.EXIONE);
    visit(exists1Pred.getSchText());
    printKeyword(ZString.SPOT);
    visit(exists1Pred.getPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    final boolean braces = existsExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.EXI);
    visit(existsExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(existsExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    final boolean braces = existsPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.EXI);
    visit(existsPred.getSchText());
    printKeyword(ZString.SPOT);
    visit(existsPred.getPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    final boolean braces = exprPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(exprPred.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitFalsePred(FalsePred falsePred)
  {
    printKeyword(ZString.FALSE);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    final boolean braces = forallExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.ALL);
    visit(forallExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(forallExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    final boolean braces = forallPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.ALL);
    visit(forallPred.getSchText());
    printKeyword(ZString.SPOT);
    visit(forallPred.getPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    zPrint(TokenName.ZED);
    printTermList(freePara.getFreetype(), ZString.ANDALSO);
    zPrint(TokenName.END);
    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    visit(freetype.getDeclName());
    printKeyword(ZString.DEFFREE);
    printTermList(freetype.getBranch(), ZString.BAR);
    return null;
  }

  public Object visitGenericType(GenericType genType)
  {
    throw new UnsupportedOperationException("Unexpected term GenType");
  }

  public Object visitGenParamType(GenParamType genType)
  {
    throw new UnsupportedOperationException("Unexpected term GenType");
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    zPrint(TokenName.ZED);
    zPrint(TokenName.LSQUARE);
    printTermList(givenPara.getDeclName());
    zPrint(TokenName.RSQUARE);
    zPrint(TokenName.END);
    return null;
  }

  public Object visitGivenType(GivenType givenType)
  {
    throw new UnsupportedOperationException("Unexpected term GenType");
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    final boolean braces = hideExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(hideExpr.getExpr());
    printKeyword(ZString.ZHIDE);
    zPrint(TokenName.LPAREN);
    printTermList(hideExpr.getZRefNameList());
    zPrint(TokenName.RPAREN);
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    final boolean braces = iffExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(iffExpr.getLeftExpr());
    printKeyword(ZString.IFF);
    visit(iffExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    final boolean braces = iffPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(iffPred.getLeftPred());
    printKeyword(ZString.IFF);
    visit(iffPred.getRightPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    final boolean braces = impliesExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(impliesExpr.getLeftExpr());
    printKeyword(ZString.IMP);
    visit(impliesExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    final boolean braces = impliesPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(impliesPred.getLeftPred());
    printKeyword(ZString.IMP);
    visit(impliesPred.getRightPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    visit(inclDecl.getExpr());
    return null;
  }

  public Object visitInStroke(InStroke inStroke)
  {
    zPrint(TokenName.INSTROKE);
    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    final boolean braces = lambdaExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.LAMBDA);
    visit(lambdaExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(lambdaExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    final boolean braces = letExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.LET);
    visit(letExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(letExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitLatexMarkupPara(LatexMarkupPara latexMarkupPara)
  {
    // TODO: what now?
    return null;
  }

  public Object visitLocAnn(LocAnn locAnn)
  {
    throw new UnsupportedOperationException("Unexpeced term LocAnn");
  }

  public Object visitMemPred(MemPred memPred)
  {
    throw new UnsupportedOperationException("Unexpeced term MemPred");
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    if (muExpr.getExpr() != null) {
      final boolean braces = muExpr.getAnn(ParenAnn.class) != null;
      if (braces) zPrint(TokenName.LPAREN);
      printKeyword(ZString.MU);
      visit(muExpr.getSchText());
      printKeyword(ZString.SPOT);
      visit(muExpr.getExpr());
      if (braces) zPrint(TokenName.RPAREN);
    }
    else {
      zPrint(TokenName.LPAREN);
      printKeyword(ZString.MU);
      visit(muExpr.getSchText());
      zPrint(TokenName.RPAREN);
    }
    return null;
  }

  public Object visitNewOldPair(NewOldPair pair)
  {
    visit(pair.getNewName());
    printKeyword(ZString.SLASH);
    visit(pair.getOldName());
    return null;
  }

  public Object visitNameSectTypeTriple(NameSectTypeTriple triple)
  {
    String message = "Unexpected term NameSectTypeTriple.";
    throw new UnsupportedOperationException(message);
  }

  public Object visitNameTypePair(NameTypePair pair)
  {
    String message = "Unexpected term NameTypePair.";
    throw new UnsupportedOperationException(message);
  }

  public Object visitNarrPara(NarrPara narrPara)
  {
    printNarrText(narrPara.getContent());
    return null;
  }

  public Object visitNarrSect(NarrSect narrSect)
  {
    printNarrText(narrSect.getContent());
    return null;
  }

  private void printNarrText(List list)
  {
    StringBuffer txt = new StringBuffer();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      txt.append((String) iter.next());
    }
    zPrint(TokenName.TEXT, txt.toString());
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    final boolean braces = negExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.NOT);
    visit(negExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    final boolean braces = negPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.NOT);
    visit(negPred.getPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    zPrint(TokenName.NEXTSTROKE);
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    final boolean braces = numExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(numExpr.getNumeral());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitZNumeral(ZNumeral zNumeral)
  {
    zPrint(TokenName.NUMERAL, Integer.valueOf(zNumeral.getValue().toString()));
    return null;
  }

  public Object visitNumStroke(NumStroke numStroke)
  {
    zPrint(TokenName.NUMSTROKE, numStroke.getDigit());
    return null;
  }

  public Object visitOperand(Operand operand)
  {
    if (operand.getList().booleanValue()) {
      printKeyword(ZString.LISTARG);
    }
    else {
      printKeyword(ZString.ARG);
    }
    return null;
  }

  public Object visitOperator(Operator operator)
  {
    zPrint(TokenName.DECORWORD, new Decorword(operator.getWord()));
    return null;
  }

  public Object visitOperatorApplication(OperatorApplication appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    String message =
      printOperator(appl.getOperatorName(), appl.getArgs());
    if (message != null) {
      throw new CztException("Cannot print appl");
    }
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    zPrint(TokenName.ZED);
    final Cat cat = optempPara.getCat();
    if (Cat.Function.equals(cat)) {
      printKeyword(ZString.FUNCTION);
    }
    else if (Cat.Generic.equals(cat)) {
      printKeyword(ZString.GENERIC);
    }
    else if (Cat.Relation.equals(cat)) {
      printKeyword(ZString.RELATION);
    }
    if (optempPara.getPrec() != null) {
      zPrint(TokenName.NUMERAL, optempPara.getPrec());
    }
    final Assoc assoc = optempPara.getAssoc();
    if (Assoc.Left.equals(assoc)) {
      printKeyword(ZString.LEFTASSOC);
    }
    else if (Assoc.Right.equals(assoc)) {
      printKeyword(ZString.RIGHTASSOC);
    }
    zPrint(TokenName.LPAREN);
    List list = optempPara.getOper();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
    }
    zPrint(TokenName.RPAREN);
    zPrint(TokenName.END);
    return null;
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    final boolean braces = orExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(orExpr.getLeftExpr());
    printKeyword(ZString.OR);
    visit(orExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    final boolean braces = orPred.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(orPred.getLeftPred());
    printKeyword(ZString.OR);
    visit(orPred.getRightPred());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitOutStroke(OutStroke outStroke)
  {
    zPrint(TokenName.OUTSTROKE);
    return null;
  }

  public Object visitParenAnn(ParenAnn parenAnn)
  {
    throw new UnsupportedOperationException("Unexpected term ParenAnn.");
  }

  public Object visitParent(Parent parent)
  {
    String word = parent.getWord();
    if (word == null) throw new CztException();
    zPrint(TokenName.DECORWORD, new Decorword(word));
    return null;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    final boolean braces = pipeExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(pipeExpr.getLeftExpr());
    printKeyword(ZString.ZPIPE);
    visit(pipeExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    final boolean braces = powerExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.POWER);
    visit(powerExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new UnsupportedOperationException("Unexpected term PowerType.");
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    final boolean braces = preExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.PRE);
    visit(preExpr.getExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitPrintParagraph(PrintParagraph printParagraph)
  {
    Object[] array = printParagraph.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof String) {
        String string = (String) object;
        if (string.equals(ZString.ZED)) {
          zPrint(TokenName.ZED);
        }
        else if (string.equals(ZString.AX)) {
          zPrint(TokenName.AX);
        }
        else if (string.equals(ZString.GENAX)) {
          zPrint(TokenName.GENAX);
        }
        else if (string.equals(ZString.SCH)) {
          zPrint(TokenName.SCH);
        }
        else if (string.equals(ZString.GENSCH)) {
          zPrint(TokenName.GENSCH);
        }
        else if (string.equals(ZString.LSQUARE)) {
          zPrint(TokenName.LSQUARE);
        }
        else if (string.equals(ZString.RSQUARE)) {
          zPrint(TokenName.RSQUARE);
        }
        else if (string.equals(ZString.BAR)) {
          zPrint(TokenName.DECORWORD, new WhereWord());
        }
        else if (string.equals(ZString.NL)) {
          zPrint(TokenName.NL);
        }
        else if (string.equals(ZString.END)) {
          zPrint(TokenName.END);
        }
        else {
          zPrint(TokenName.DECORWORD, new Decorword((String) object));
        }
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    return null;
  }

  public Object visitPrintPredicate(PrintPredicate printPredicate)
  {
    final boolean braces = printPredicate.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    Object[] array = printPredicate.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof String) {
        String string = (String) object;
        if (string.equals(ZString.NL)) {
          zPrint(TokenName.NL);
        }
        else {
          zPrint(TokenName.DECORWORD, new Decorword((String) object));
        }
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitPrintExpression(PrintExpression printExpression)
  {
    final boolean braces = printExpression.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    Object[] array = printExpression.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof String) {
        zPrint(TokenName.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    final boolean braces = prodExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printTermList(prodExpr.getZExprList(), ZString.CROSS);
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new UnsupportedOperationException("Unexpected term ProdType.");
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    final boolean braces = projExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(projExpr.getLeftExpr());
    printKeyword(ZString.ZPROJ);
    visit(projExpr.getRightExpr());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    final boolean braces = refExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    if (refExpr.getMixfix().booleanValue()) {
      String message = "RefExpr with Mixfix set to true are not contained " +
        "in print trees; did you run the AstToPrintTreeVisitor before " +
        "calling this ZPrintVisitor?";
      throw new CztException(message);
    }
    else { // Mixfix == false
      visit(refExpr.getRefName());
      if (refExpr.getZExprList().size() > 0) {
        zPrint(TokenName.LSQUARE);
        printTermList(refExpr.getZExprList());
        zPrint(TokenName.RSQUARE);
      }
    }
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitZExprList(ZExprList zExprList)
  {
    printTermList(zExprList.getExpr());
    return null;
  }

  public Object visitZRenameList(ZRenameList zRenameList)
  {
    printTermList(zRenameList.getNewOldPair());
    return null;
  }

  public Object visitZRefNameList(ZRefNameList zRefNameList)
  {
    printTermList(zRefNameList.getRefName());
    return null;
  }

  public Object visitZRefName(ZRefName refName)
  {
    OperatorName op = refName.getOperatorName();
    if (op == null) {
      zPrint(TokenName.DECORWORD,
             new Decorword(refName.getWord(), refName.getStroke()));
      return null;
    }
    zPrint(TokenName.LPAREN);
    for (Iterator iter = op.iterator(); iter.hasNext(); ) {
      zPrint(TokenName.DECORWORD, new Decorword((String) iter.next()));
    }
    zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    final boolean braces = renameExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(renameExpr.getExpr());
    zPrint(TokenName.LSQUARE);
    printTermList(renameExpr.getZRenameList());
    zPrint(TokenName.RSQUARE);
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    throw new UnsupportedOperationException("Unexpected term SchemaType.");
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    zPrint(TokenName.LSQUARE);
    visit(schExpr.getSchText());
    zPrint(TokenName.RSQUARE);
    return null;
  }

  public Object visitZSchText(ZSchText schText)
  {
    visit(schText.getDeclList());
    if (schText.getPred() != null) {
      printKeyword(ZString.BAR);
      visit(schText.getPred());
    }
    return null;
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    printTermList(zDeclList.getDecl(), ZString.SEMICOLON);
    return null;
  }

  public Object visitSectTypeEnvAnn(SectTypeEnvAnn ann)
  {
    throw new UnsupportedOperationException("Unexpected term SectTypeEnvAnn.");
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    zPrint(TokenName.LBRACE);
    visit(setCompExpr.getSchText());
    if (setCompExpr.getExpr() != null) {
      printKeyword(ZString.SPOT);
      visit(setCompExpr.getExpr());
    }
    zPrint(TokenName.RBRACE);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    zPrint(TokenName.LBRACE);
    printTermList(setExpr.getZExprList());
    zPrint(TokenName.RBRACE);
    return null;
  }

  public Object visitSignature(Signature s)
  {
    throw new UnsupportedOperationException("Unexpected term Signature.");
  }

  public Object visitSpec(Spec spec)
  {
    visit(spec.getSect());
    return null;
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    final boolean braces = thetaExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    printKeyword(ZString.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStroke());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitTruePred(TruePred truePred)
  {
    printKeyword(ZString.TRUE);
    return null;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    zPrint(TokenName.LPAREN);
    printTermList(tupleExpr.getZExprList());
    zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    final boolean braces = tupleSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) zPrint(TokenName.LPAREN);
    visit(tupleSelExpr.getExpr());
    printKeyword(ZString.DOT);
    visit(tupleSelExpr.getNumeral());
    if (braces) zPrint(TokenName.RPAREN);
    return null;
  }

  public Object visitSignatureAnn(SignatureAnn typeAnn)
  {
    throw new UnsupportedOperationException("Unexpected term SignatureAnn.");
  }

  public Object visitTypeAnn(TypeAnn typeAnn)
  {
    throw new UnsupportedOperationException("Unexpected term TypeAnn.");
  }

  public Object visitTypeEnvAnn(TypeEnvAnn typeEnvAnn)
  {
    throw new UnsupportedOperationException("Unexpected term TypeEnvAnn.");
  }

  public Object visitUnparsedPara(UnparsedPara unparsedPara)
  {
    // TODO: What to do with UnparsedPara?
    return null;
  }

  public Object visitUnparsedZSect(UnparsedZSect unparsedZSect)
  {
    // TODO: What to do with UnparsedZSect?
    return null;
  }

  public Object visitVarDecl(VarDecl varDecl)
  {
    printTermList(varDecl.getDeclName());
    printKeyword(ZString.COLON);
    visit(varDecl.getExpr());
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    final List parents = zSect.getParent();
    final boolean nameIsSpecification = "Specification".equals(name);
    final boolean isAnonymous =
      "Specification".equals(name) &&
      parents.size() == 1 &&
      "standard_toolkit".equals(((Parent) parents.get(0)).getWord());

    if (! isAnonymous) {
      zPrint(TokenName.ZED);
      zPrint(Keyword.SECTION);
      if (name == null) throw new CztException();
      zPrint(TokenName.DECORWORD, new Decorword(name));
      if (parents.size() > 0) {
        zPrint(Keyword.PARENTS);
        printTermList(parents);
      }
      zPrint(TokenName.END);
    }
    visit(zSect.getPara());
    return null;
  }

  protected void visit(Term t)
  {
    if (t != null) {
      t.accept(this);
    }
  }

  private void printAnd()
  {
    printKeyword(ZString.AND);
  }

  /**
   * @return <code>null</code> if all went well, or an
   *         error message in case of an error.
   */
  private String printOperator(Expr operator, Object arguments)
  {
    if (! (operator instanceof RefExpr)) {
      return operator.toString() + " not instance of RefExpr.";
    }
    RefExpr ref = (RefExpr) operator;
    OperatorName op = null;
    try {
      op = new OperatorName(ref.getZRefName());
    }
    catch (OperatorName.OperatorNameException e) {
      return "Unexpected operator " + ref.getZRefName().getWord();
    }
    assert op != null;
    return printOperator(op, arguments);
  }

  private String printOperator(OperatorName op, Object arguments)
  {
    List args = new ArrayList();
    if (arguments instanceof List) {
      args = (List) arguments;
    }
    else {
      if (op.isUnary()) {
        args.add(arguments);
      }
      else {
        if (! (arguments instanceof TupleExpr)) {
          return arguments.toString() + " not instance of TupleExpr";
        }
        TupleExpr tuple = (TupleExpr) arguments;
        args = tuple.getZExprList();
      }
    }
    int pos = 0;
    for (Iterator iter = op.iterator(); iter.hasNext();) {
      final String opPart = (String) iter.next();
      if (opPart.equals(ZString.ARG)) {
        visit((Term) args.get(pos));
        pos++;
      }
      else if (opPart.equals(ZString.LISTARG)) {
        Object arg = args.get(pos);
        if (! (arg instanceof SetExpr)) {
          return "Expected SetExpr but got " + arg;
        }
        SetExpr setExpr = (SetExpr) arg;
        List<Expr> sequence = setExpr.getZExprList();
        for (Iterator<Expr> i = sequence.iterator(); i.hasNext();) {
          Expr o = i.next();
          if (! (o instanceof TupleExpr)) {
            return "Expected TupleExpr but got " + o;
          }
          TupleExpr tuple = (TupleExpr) o;
          List<Expr> tupleContents = tuple.getZExprList();
          if (tupleContents.size() != 2) {
            return "Expected tuple of size 2 but was " + tupleContents.size();
          }
          visit(tupleContents.get(1));
          if (i.hasNext()) printKeyword(ZString.COMMA);
        }
        pos++;
      }
      else {
        zPrint(TokenName.DECORWORD, new Decorword(opPart));
        //              opPart + strokeListToString(op.getStroke()));
      }
    }
    return null;
  }

  /**
   * Transforms a list of strokes into a (unicode) string.
   */
  private String strokeListToString(List strokes)
  {
    StringBuffer result = new StringBuffer();
    for (Iterator iter = strokes.iterator(); iter.hasNext();)
    {
      Stroke stroke = (Stroke) iter.next();
      result.append(stroke.toString());
    }
    return result.toString();
  }

  protected void printTermList(List list)
  {
    printTermList(list, ZString.COMMA);
  }

  /*
  protected void printTermList(List list, int separator)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext()) {
        print(separator);
      }
    }
  }
  */

  /**
   * @throws NullPointerException if separator is <code>null</code>.
   */
  protected void printTermList(List list, String separator)
  {
    if (separator == null) throw new NullPointerException();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext()) {
        printKeyword(separator);
      }
    }
  }

  protected void printKeyword(String keyword)
  {
    zPrint(TokenName.DECORWORD, new Decorword(keyword));
  }
}
