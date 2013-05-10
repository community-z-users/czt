/*
  Copyright (C) 2004, 2005, 2006, 2007, 2008 Petra Malik
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
import java.util.Properties;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZOpToken;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * If Z/EVES output is selected,
 * <ul>
 *  <li>constant declarations are translated into
 *      variable declarations, and</li>
 *  <li>LambdaExpr, MuExpr, and LetExpr are parenthesised.</li>
 * </ul>
 *
 * @author Petra Malik
 */
public class ZPrintVisitor
  extends AbstractPrintVisitor<Object>
  implements TermVisitor<Object>,
             ListTermVisitor<Object>,
             ZVisitor<Object>,
             ApplicationVisitor<Object>,
             OperatorApplicationVisitor<Object>,
             PrintParagraphVisitor<Object>,
             PrintPredicateVisitor<Object>,
             PrintExpressionVisitor<Object>,
             PrintPropertiesKeys
{
  protected boolean ref_ = false;
  private final Properties properties_;
  private final Utils utils_ = new UtilsImpl();
  private Visitor<Object> visitor_ = this;

  /**
   * Creates a new Z print visitor.
   */
  public ZPrintVisitor(SectionInfo si, ZPrinter printer)
  {
    this(si, printer, null);
  }

  public ZPrintVisitor(SectionInfo si, ZPrinter printer, Properties properties)
  {
    super(si, printer);
    properties_ = properties;
  }

  public void setVisitor(Visitor<Object> visitor)
  {
    visitor_ = visitor;
  }

  private boolean getBooleanProperty(String propertyKey)
  {
    if (properties_ == null) {
      return false;
    }
    return "true".equals(properties_.getProperty(propertyKey));
  }

  private boolean eves()
  {
    return getBooleanProperty(PROP_PRINT_ZEVES);
  }

  private boolean ids()
  {
    return getBooleanProperty(PROP_PRINT_NAME_IDS);
  }

  protected void printGenericFormals(NameList term)
  {
    if (term != null && ! utils_.isEmpty(term)) {
      print(ZToken.LSQUARE);
      visit(term);
      print(ZToken.RSQUARE);
    }
  }
  
  protected void print(Token tokenName, Object spelling)
  {
    print(new TokenImpl(tokenName, spelling));
  }

  protected void printDecorword(Decorword dw)
  {
    print(ZToken.DECORWORD, dw);
  }

  protected void printDecorword(String name)
  {
    printDecorword(new Decorword(name));
  }

  protected void printLPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
  }

  protected void printRPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.RPAREN);
  }

  public Object visitTerm(Term term)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term " + term));
  }

  public Object visitListTerm(ListTerm<?> listTerm)
  {
    for (Object o : listTerm) {
      if (o instanceof Term) {
        visit((Term) o);
      }
    }
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpeced term AndPred"));
  }

  public Object visitAndExpr(AndExpr andExpr)
  {
    final boolean braces = andExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(andExpr.getLeftExpr());
    printAnd();
    visit(andExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  /* NOTE:
   * AxParas are appropriately transformed by the AstToPrintTreeVisitor
   * to a PrintParagraphs, which is handled by the ZPrintVisitor.
   */
  public Object visitAxPara(AxPara axPara)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpeced term AxPara"));
  }

   public Object visitApplication(Application appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(appl.getLeftExpr());
    visit(appl.getRightExpr());
    if (braces) print(ZToken.RPAREN);
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
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term " + applExpr));
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    final boolean braces = bindExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZToken.LBIND);
    printTermList(((ZDeclList) bindExpr.getDeclList()).getDecl());
    print(ZToken.RBIND);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    final boolean braces = bindSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(bindSelExpr.getExpr());
    print(ZKeyword.DOT);
    ref_ = true;
    visit(bindSelExpr.getName());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitBranch(Branch branch)
  {
    ref_ = false;
    visit(branch.getName());
    if (branch.getExpr() != null) {
      print(ZToken.LDATA);
      visit(branch.getExpr());
      print(ZToken.RDATA);
    }
    return null;
  }

  public Object visitZBranchList(ZBranchList zBranchList)
  {
    printTermList(zBranchList, ZKeyword.BAR);
    return null;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    final boolean braces = compExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(compExpr.getLeftExpr());
    print(ZKeyword.ZCOMP);
    visit(compExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    final boolean braces = condExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.IF);
    visit(condExpr.getPred());
    print(ZKeyword.THEN);
    visit(condExpr.getLeftExpr());
    print(ZKeyword.ELSE);
    visit(condExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    print(ZToken.ZED);
    if (conjPara.getName() != null) {
      print(ZKeyword.THEOREM);
      print(ZToken.DECORWORD, new Decorword(conjPara.getName()));
    }
    printGenericFormals(conjPara.getNameList());
    print(ZKeyword.CONJECTURE);
    visit(conjPara.getPred());
    print(ZToken.END);
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    ref_ = false;
    if (eves()) {
      visit(constDecl.getName());
      print(ZKeyword.COLON);
      print(ZToken.LBRACE);
      visit(constDecl.getExpr());
      print(ZToken.RBRACE);
    }
    else {
      visit(constDecl.getName());
      print(ZKeyword.DEFEQUAL);
      visit(constDecl.getExpr());
    }
    return null;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    final boolean braces = decorExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    if (braces) print(ZToken.RPAREN);
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
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.EXIONE);
    visit(exists1Expr.getSchText());
    print(ZKeyword.SPOT);
    visit(exists1Expr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    final boolean braces = exists1Pred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.EXIONE);
    visit(exists1Pred.getSchText());
    print(ZKeyword.SPOT);
    visit(exists1Pred.getPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    final boolean braces = existsExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.EXI);
    visit(existsExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(existsExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    final boolean braces = existsPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.EXI);
    visit(existsPred.getSchText());
    print(ZKeyword.SPOT);
    visit(existsPred.getPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    final boolean braces = exprPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(exprPred.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitFalsePred(FalsePred falsePred)
  {
    final boolean braces = falsePred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.FALSE);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    final boolean braces = forallExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.ALL);
    visit(forallExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(forallExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    final boolean braces = forallPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.ALL);
    visit(forallPred.getSchText());
    print(ZKeyword.SPOT);
    visit(forallPred.getPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    print(ZToken.ZED);
    visit(freePara.getFreetypeList());
    print(ZToken.END);
    return null;
  }

  public Object visitZFreetypeList(ZFreetypeList zFreetypeList)
  {
    printTermList(zFreetypeList, ZKeyword.ANDALSO);
    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    ref_ = false;
    visit(freetype.getName());
    print(ZKeyword.DEFFREE);
    visit(freetype.getBranchList());
    return null;
  }

  public Object visitGenericType(GenericType genType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term GenType"));
  }

  public Object visitGenParamType(GenParamType genType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term GenType"));
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    ref_ = false;
    print(ZToken.ZED);
    print(ZToken.LSQUARE);
    printTermList(givenPara.getNames());
    print(ZToken.RSQUARE);
    print(ZToken.END);
    return null;
  }

  public Object visitGivenType(GivenType givenType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term GenType"));
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    final boolean braces = hideExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(hideExpr.getExpr());
    print(ZKeyword.ZHIDE);
    print(ZToken.LPAREN);
    ref_ = false;
    printTermList(hideExpr.getZNameList());
    print(ZToken.RPAREN);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  private void visitIffExprChild(Expr expr)
  {
    if (expr instanceof IffExpr &&
        expr.getAnn(ParenAnn.class) == null) {
      visitIffExpr((IffExpr) expr);
    }
    else {
      visit(expr);
    }
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    final boolean braces = iffExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visitIffExprChild(iffExpr.getLeftExpr());
    print(ZKeyword.IFF);
    visitIffExprChild(iffExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  private void visitIffPredChild(Pred pred)
  {
    if (pred instanceof ExprPred) {
      visitIffExprChild(((ExprPred) pred).getExpr());
    }
    else if (pred instanceof IffPred &&
        pred.getAnn(ParenAnn.class) == null) {
      visitIffPred((IffPred) pred);
    }
    else {
      visit(pred);
    }
  }

  public Object visitIffPred(IffPred iffPred)
  {
    final boolean braces = iffPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visitIffPredChild(iffPred.getLeftPred());
    print(ZKeyword.IFF);
    visitIffPredChild(iffPred.getRightPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    final boolean braces = impliesExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(impliesExpr.getLeftExpr());
    print(ZKeyword.IMP);
    visit(impliesExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    final boolean braces = impliesPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(impliesPred.getLeftPred());
    print(ZKeyword.IMP);
    visit(impliesPred.getRightPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    visit(inclDecl.getExpr());
    return null;
  }

  public Object visitInStroke(InStroke inStroke)
  {
    print(ZToken.INSTROKE);
    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    final boolean braces = eves() || lambdaExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.LAMBDA);
    visit(lambdaExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(lambdaExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    final boolean braces = eves() || letExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.LET);
    visit(letExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(letExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitLatexMarkupPara(LatexMarkupPara latexMarkupPara)
  {
    // TODO: what now?
    return null;
  }

  public Object visitLocAnn(LocAnn locAnn)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpeced term LocAnn"));
  }

  public Object visitMemPred(MemPred memPred)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpeced term MemPred"));
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    if (muExpr.getExpr() != null) {
      final boolean braces = eves() || muExpr.getAnn(ParenAnn.class) != null;
      if (braces) print(ZToken.LPAREN);
      print(ZKeyword.MU);
      visit(muExpr.getSchText());
      print(ZKeyword.SPOT);
      visit(muExpr.getExpr());
      if (braces) print(ZToken.RPAREN);
    }
    else {
      print(ZToken.LPAREN);
      print(ZKeyword.MU);
      visit(muExpr.getSchText());
      print(ZToken.RPAREN);
    }
    return null;
  }

  public Object visitNewOldPair(NewOldPair pair)
  {
    visit(pair.getNewName());
    print(ZKeyword.SLASH);
    visit(pair.getOldName());
    return null;
  }

  public Object visitNameSectTypeTriple(NameSectTypeTriple triple)
  {
    String message = "Unexpected term NameSectTypeTriple.";
    throw new CztException(new PrintException(getSectionInfo().getDialect(), message));
  }

  public Object visitNameTypePair(NameTypePair pair)
  {
    String message = "Unexpected term NameTypePair.";
    throw new CztException(new PrintException(getSectionInfo().getDialect(), message));
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

  private void printNarrText(List<? extends Object> list)
  {
    StringBuffer txt = new StringBuffer();
    for (Object o : list) {
      txt.append(o.toString());
    }
    print(ZToken.TEXT, new LocString(txt.toString(), null));
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    final boolean braces = negExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.NOT);
    visit(negExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    final boolean braces = negPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.NOT);
    visit(negPred.getPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    print(ZToken.NEXTSTROKE);
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    final boolean braces = numExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(numExpr.getNumeral());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitZNumeral(ZNumeral zNumeral)
  {
    print(ZToken.NUMERAL, new LocInt(zNumeral.getValue(), null));
    return null;
  }

  public Object visitNumStroke(NumStroke numStroke)
  {
    print(ZToken.NUMSTROKE,
          new LocInt(numStroke.getDigit().getValue(), null));
    return null;
  }

  public Object visitOperand(Operand operand)
  {
    if (operand.getList().booleanValue()) {
      print(ZKeyword.LISTARG);
    }
    else {
      print(ZKeyword.ARG);
    }
    return null;
  }

  public Object visitOperator(Operator operator)
  {
    print(ZToken.DECORWORD, new Decorword(operator.getWord()));
    return null;
  }

  public Object visitOperatorApplication(OperatorApplication appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    String message =
      printOperator(appl.getOperatorName(), appl.getArgs());
    if (message != null) {
      throw new CztException(new PrintException(getSectionInfo().getDialect(), "Cannot print appl"));
    }
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    print(ZToken.ZED);
    final Cat cat = optempPara.getCat();
    if (Cat.Function.equals(cat)) {
      print(ZKeyword.FUNCTION);
    }
    else if (Cat.Generic.equals(cat)) {
      print(ZKeyword.GENERIC);
    }
    else if (Cat.Relation.equals(cat)) {
      print(ZKeyword.RELATION);
    }
    if (optempPara.getPrec() != null) {
      print(ZToken.NUMERAL, new LocInt(optempPara.getPrec(), null));
    }
    final Assoc assoc = optempPara.getAssoc();
    if (Assoc.Left.equals(assoc)) {
      print(ZKeyword.LEFTASSOC);
    }
    else if (Assoc.Right.equals(assoc)) {
      print(ZKeyword.RIGHTASSOC);
    }
    print(ZToken.LPAREN);
    for (Oper oper : optempPara.getOper()) {
      visit(oper);
    }
    print(ZToken.RPAREN);
    print(ZToken.END);
    return null;
  }

  private void visitOrExprChild(Expr expr)
  {
    if (expr instanceof OrExpr &&
        expr.getAnn(ParenAnn.class) == null) {
      visitOrExpr((OrExpr) expr);
    }
    else {
      visit(expr);
    }
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    final boolean braces = orExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visitOrExprChild(orExpr.getLeftExpr());
    print(ZKeyword.OR);
    visitOrExprChild(orExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  private void visitOrPredChild(Pred pred)
  {
    if (pred instanceof ExprPred) {
      visitOrExprChild(((ExprPred) pred).getExpr());
    }
    else if (pred instanceof OrPred &&
        pred.getAnn(ParenAnn.class) == null) {
      visitOrPred((OrPred) pred);
    }
    else {
      visit(pred);
    }
  }

  public Object visitOrPred(OrPred orPred)
  {
    final boolean braces = orPred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visitOrPredChild(orPred.getLeftPred());
    print(ZKeyword.OR);
    visitOrPredChild(orPred.getRightPred());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitOutStroke(OutStroke outStroke)
  {
    print(ZToken.OUTSTROKE);
    return null;
  }

  public Object visitParenAnn(ParenAnn parenAnn)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term ParenAnn."));
  }

  public Object visitParent(Parent parent)
  {
    String word = parent.getWord();
    if (word == null) throw new CztException(new PrintException(getSectionInfo().getDialect(), "Invalid (null) parent"));
    print(ZToken.DECORWORD, new Decorword(word));
    return null;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    final boolean braces = pipeExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(pipeExpr.getLeftExpr());
    print(ZKeyword.ZPIPE);
    visit(pipeExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    final boolean braces = powerExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.POWER);
    visit(powerExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term PowerType."));
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    final boolean braces = preExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.ZPRE);
    visit(preExpr.getExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitPrintParagraph(PrintParagraph printParagraph)
  {
    for (Object o : printParagraph.getAnns()) {
      if (o instanceof PrintParagraph) {
        visitPrintParagraph((PrintParagraph) o);
      }
    }
    ref_ = false;
    Object[] array = printParagraph.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof Token) {
        print((Token) object);
      }
      else if (object instanceof String) {
        print(ZToken.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    array = null;
    return null;
  }

  public Object visitPrintPredicate(PrintPredicate printPredicate)
  {
    final boolean braces = printPredicate.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    Object[] array = printPredicate.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof Token) {
        print((Token) object);
      }
      else if (object instanceof String) {
        print(ZToken.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) print(ZToken.RPAREN);
    array = null;
    return null;
  }

  public Object visitPrintExpression(PrintExpression printExpression)
  {
    final boolean braces = printExpression.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    Object[] array = printExpression.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof String) {
        print(ZToken.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) print(ZToken.RPAREN);
    array = null;
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    final boolean braces = prodExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    printTermList(prodExpr.getZExprList(), ZKeyword.CROSS);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term ProdType."));
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    final boolean braces = projExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(projExpr.getLeftExpr());
    print(ZKeyword.ZPROJ);
    visit(projExpr.getRightExpr());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    final boolean braces = refExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    if (refExpr.getMixfix().booleanValue()) {
      String message = "RefExpr with Mixfix set to true are not contained " +
        "in print trees; did you run the AstToPrintTreeVisitor before " +
        "calling this ZPrintVisitor?";
      throw new CztException(new PrintException(getSectionInfo().getDialect(), message));
    }
    else { // Mixfix == false
      ref_ = true;
      visit(refExpr.getName());
      if (refExpr.getZExprList().size() > 0 && refExpr.getExplicit()) {
        print(ZToken.LSQUARE);
        printTermList(refExpr.getZExprList());
        print(ZToken.RSQUARE);
      }
    }
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitZExprList(ZExprList zExprList)
  {
    printTermList(zExprList.getExpr());
    return null;
  }

  public Object visitZRenameList(ZRenameList zRenameList)
  {
    ref_ = false;
    printTermList(zRenameList.getNewOldPair());
    return null;
  }

  public Object visitZNameList(ZNameList nameList)
  {
    printTermList(nameList);
    return null;
  }

  public Object visitZName(ZName name)
  {
    final boolean braces = name.getAnn(ParenAnn.class) != null;
    OperatorName op = name.getOperatorName();
    if (op == null) {
      String word = name.getWord();
      if (ids() && name.getId() != null) {
        word += ZString.LL + name.getId();
      }
      print(ZToken.DECORWORD,
            new Decorword(word, name.getZStrokeList()));
      return null;
    }
    if (braces || ref_) print(ZToken.LPAREN);
    for (String wordPart : op.getWords()) {
      if (wordPart.equals(ZString.LISTARG) || wordPart.equals(ZString.ARG)) {
        printDecorword(wordPart);
      }
      else {
        printDecorword(new Decorword(wordPart, (ZStrokeList) op.getStrokes()));
      }
    }
    if (braces || ref_) print(ZToken.RPAREN);
    return null;
  }

  public Object visitZStrokeList(ZStrokeList zStrokeList)
  {
    for (Stroke stroke : zStrokeList) visit(stroke);
    return null;
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    final boolean braces = renameExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(renameExpr.getExpr());
    print(ZToken.LSQUARE);
    printTermList(renameExpr.getZRenameList());
    print(ZToken.RSQUARE);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term SchemaType."));
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    String name = (String) schExpr.getAnn(String.class);
    if (name != null) {
      print(ZToken.DECORWORD, new Decorword(name));
    }
    else {
      print(ZToken.LSQUARE);
      visit(schExpr.getSchText());
      print(ZToken.RSQUARE);
    }
    return null;
  }

  public Object visitZSchText(ZSchText schText)
  {
    visit(schText.getDeclList());
    if (schText.getPred() != null) {
      print(ZKeyword.BAR);
      visit(schText.getPred());
    }
    return null;
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    printTermList(zDeclList.getDecl(), ZKeyword.SEMICOLON);
    return null;
  }

  public Object visitSectTypeEnvAnn(SectTypeEnvAnn ann)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term SectTypeEnvAnn."));
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    print(ZToken.LBRACE);
    visit(setCompExpr.getSchText());
    if (setCompExpr.getExpr() != null) {
      print(ZKeyword.SPOT);
      visit(setCompExpr.getExpr());
    }
    print(ZToken.RBRACE);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    print(ZToken.LBRACE);
    printTermList(setExpr.getZExprList());
    print(ZToken.RBRACE);
    return null;
  }

  public Object visitSignature(Signature s)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term Signature."));
  }

  public Object visitSpec(Spec spec)
  {
    visit(spec.getSect());
    return null;
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    final boolean braces = thetaExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStrokeList());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitTruePred(TruePred truePred)
  {
    final boolean braces = truePred.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    print(ZKeyword.TRUE);
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    print(ZToken.LPAREN);
    printTermList(tupleExpr.getZExprList());
    print(ZToken.RPAREN);
    return null;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    final boolean braces = tupleSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
    visit(tupleSelExpr.getExpr());
    print(ZKeyword.DOT);
    visit(tupleSelExpr.getNumeral());
    if (braces) print(ZToken.RPAREN);
    return null;
  }

  public Object visitSignatureAnn(SignatureAnn signatureAnn)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term SignatureAnn."));
  }

  public Object visitTypeAnn(TypeAnn typeAnn)
  {
    throw new CztException(new PrintException(getSectionInfo().getDialect(), "Unexpected term TypeAnn."));
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
    ref_ = false;
    printTermList(varDecl.getName());
    print(ZKeyword.COLON);
    visit(varDecl.getExpr());
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    final String name = zSect.getName();
    final List<Parent> parents = zSect.getParent();
    print(ZToken.ZED);
    print(ZKeyword.SECTION);
    if (name == null) throw new CztException(new PrintException(getSectionInfo().getDialect(), "Invalid section name."));
    print(ZToken.DECORWORD, new Decorword(name));
    if (parents.size() > 0) {
      print(ZKeyword.PARENTS);
      printTermList(parents);
    }
    print(ZToken.END);
    visit(zSect.getParaList());
    return null;
  }

  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) visit(p);
    return null;
  }

  protected void visit(Term t)
  {
    if (t != null) {
      t.accept(visitor_);
    }
  }

  private void printAnd()
  {
    print(ZKeyword.AND);
  }

  /**
   * This contains a very crude hack to get the PrettyPrinter working.
   * Used OpTokens are currently only I, PRE, and POST, even though
   * they might be in fact different ones (with the same newline
   * category).
   */
@SuppressWarnings("unchecked")
private String printOperator(OperatorName op, Object arguments)
  {
    List<Object> args = new ArrayList<Object>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    if (arguments instanceof List) {
      args = (List<Object>) arguments; // unchecked warning 
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
        args.addAll(tuple.getZExprList());
      }
    }
    int pos = 0;
    String[] opArray = op.getWords();
    for (int opArrayPos = 0; opArrayPos < opArray.length; opArrayPos++) {
      String opPart = opArray[opArrayPos];
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
        Iterator<Expr> i = sequence.iterator();
        while (i.hasNext()) {
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
          if (i.hasNext()) print(ZKeyword.COMMA);
        }
        i = null;
        pos++;
      }
      else {
        final Decorword decorword =
          new Decorword(opPart, (ZStrokeList) op.getStrokes());
        if (opArrayPos > 0 && opArrayPos < opArray.length - 1) {
          print(new TokenImpl(ZOpToken.I, decorword));
        }
        else if (opArrayPos > 0) {
          print(new TokenImpl(ZOpToken.POST, decorword));
        }
        else if (opArrayPos < opArray.length - 1) {
          print(new TokenImpl(ZOpToken.PRE, decorword));
        }
        else {
          return "An OperatorWord cannot contain of just one part";
        }
      }
    }
    return null;
  }

  protected void printTermList(List<? extends Term> list)
  {
    printTermList(list, ZKeyword.COMMA);
  }

  /**
   * @throws NullPointerException if separator is <code>null</code>.
   */
  protected void printTermList(List<? extends Term> list, Token separator)
  {
    if (separator == null) throw new NullPointerException();
    Iterator<? extends Term> iter = list.iterator();
    while (iter.hasNext()) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext()) {
        print(separator);
      }
    }
    iter = null;
  }

  protected void printTermList(List<? extends Term> list, List<? extends Token> separators)
  {
    if (separators == null || separators.isEmpty()) throw new NullPointerException();
    Iterator<? extends Term> iter = list.iterator();
    while (iter.hasNext()) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext())
      {
        Iterator<? extends Token> sepit = separators.iterator();
        while (sepit.hasNext())
        {
          Token separator = sepit.next();
          print(separator);
        }
        sepit = null;
      }
    }
    iter = null;
  }

  /**
   * @throws NullPointerException if separator is <code>null</code>.
   */
  protected void printTermList(List<? extends Term> list, String separator)
  {
    if (separator == null) throw new NullPointerException();
    Iterator<? extends Term> iter = list.iterator();
    while (iter.hasNext()) {
      Term term = iter.next();
      visit(term);
      if (iter.hasNext()) {
        printDecorword(separator);
      }
    }
    iter = null;
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
}
