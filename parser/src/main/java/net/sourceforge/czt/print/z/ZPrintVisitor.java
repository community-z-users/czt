/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik
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
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.Keyword;
import net.sourceforge.czt.parser.z.TokenName;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
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
  extends AbstractPrintVisitor
  implements TermVisitor, ListTermVisitor, ZVisitor,
             ApplicationVisitor, OperatorApplicationVisitor,
             PrintParagraphVisitor,
             PrintPredicateVisitor, PrintExpressionVisitor,
             PrintPropertiesKeys
{
  protected boolean ref_ = false;
  private Properties properties_;
  private Utils utils_ = new UtilsImpl();
  private Factory factory_ = new Factory();

  /**
   * Creates a new Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public ZPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }

  public ZPrintVisitor(ZPrinter printer, Properties properties)
  {
    super(printer);
    properties_ = properties;
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
    return getBooleanProperty(PROP_Z_EVES);
  }

  private boolean ids()
  {
    return getBooleanProperty(PROP_PRINT_NAME_IDS);
  }

  protected void printGenericFormals(NameList term)
  {
    if (term != null && ! utils_.isEmpty(term)) {
      print(TokenName.LSQUARE);
      visit(term);
      print(TokenName.RSQUARE);
    }
  }
  
  protected void print(TokenName tokenName, Object spelling)
  {
    print(new TokenImpl(tokenName, spelling));
  }

  protected void print(Keyword keyword)
  {
    if (Keyword.SECTION.equals(keyword) ||
        Keyword.PARENTS.equals(keyword)) {
      print((Token) keyword);
      return;
    }
    printDecorword(keyword.spelling());
  }

  protected void printDecorword(Decorword dw)
  {
    print(TokenName.DECORWORD, dw);
  }

  protected void printDecorword(String name)
  {
    printDecorword(new Decorword(name));
  }

  protected void printLPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
  }

  protected void printRPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.RPAREN);
  }

  /**
   * Prints the first term followed by the symbol followed by the
   * second term.
   */
  private void print(Term t1, String symbol, Term t2)
  {
    if (symbol == null) throw new NullPointerException();
    visit(t1);
    printDecorword(symbol);
    visit(t2);
  }

  public Object visitTerm(Term term)
  {
    throw new PrintException("Unexpected term " + term);
  }

  public Object visitListTerm(ListTerm listTerm)
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
    throw new PrintException("Unexpeced term AndPred");
  }

  public Object visitAndExpr(AndExpr andExpr)
  {
    final boolean braces = andExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(andExpr.getLeftExpr());
    printAnd();
    visit(andExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  /* NOTE:
   * AxParas are appropriately transformed by the AstToPrintTreeVisitor
   * to a PrintParagraphs, which is handled by the ZPrintVisitor.
   */
  public Object visitAxPara(AxPara axPara)
  {
    throw new PrintException("Unexpeced term AxPara");
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
    String word = refExpr.getZName().getWord();
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
      throw new PrintException(message);
    }
    return result;
  }

  public Object visitApplication(Application appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(appl.getLeftExpr());
    visit(appl.getRightExpr());
    if (braces) print(TokenName.RPAREN);
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
    throw new PrintException("Unexpected term " + applExpr);
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    final boolean braces = bindExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(TokenName.LBIND);
    printTermList(((ZDeclList) bindExpr.getDeclList()).getDecl());
    print(TokenName.RBIND);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    final boolean braces = bindSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(bindSelExpr.getExpr());
    print(Keyword.DOT);
    ref_ = true;
    visit(bindSelExpr.getName());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitBranch(Branch branch)
  {
    ref_ = false;
    visit(branch.getName());
    if (branch.getExpr() != null) {
      print(TokenName.LDATA);
      visit(branch.getExpr());
      print(TokenName.RDATA);
    }
    return null;
  }

  public Object visitZBranchList(ZBranchList zBranchList)
  {
    printTermList(zBranchList, Keyword.BAR);
    return null;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    final boolean braces = compExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(compExpr.getLeftExpr());
    print(Keyword.ZCOMP);
    visit(compExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    final boolean braces = condExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.IF);
    visit(condExpr.getPred());
    print(Keyword.THEN);
    visit(condExpr.getLeftExpr());
    print(Keyword.ELSE);
    visit(condExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    print(TokenName.ZED);
    printGenericFormals(conjPara.getNameList());
    print(Keyword.CONJECTURE);
    visit(conjPara.getPred());
    print(TokenName.END);
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    ref_ = false;
    if (eves()) {
      visit(constDecl.getName());
      print(Keyword.COLON);
      print(TokenName.LBRACE);
      visit(constDecl.getExpr());
      print(TokenName.RBRACE);
    }
    else {
      visit(constDecl.getName());
      print(Keyword.DEFEQUAL);
      visit(constDecl.getExpr());
    }
    return null;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    final boolean braces = decorExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    if (braces) print(TokenName.RPAREN);
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
    if (braces) print(TokenName.LPAREN);
    print(Keyword.EXIONE);
    visit(exists1Expr.getSchText());
    print(Keyword.SPOT);
    visit(exists1Expr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    final boolean braces = exists1Pred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.EXIONE);
    visit(exists1Pred.getSchText());
    print(Keyword.SPOT);
    visit(exists1Pred.getPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    final boolean braces = existsExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.EXI);
    visit(existsExpr.getSchText());
    print(Keyword.SPOT);
    visit(existsExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    final boolean braces = existsPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.EXI);
    visit(existsPred.getSchText());
    print(Keyword.SPOT);
    visit(existsPred.getPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    final boolean braces = exprPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(exprPred.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitFalsePred(FalsePred falsePred)
  {
    final boolean braces = falsePred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.FALSE);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    final boolean braces = forallExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.ALL);
    visit(forallExpr.getSchText());
    print(Keyword.SPOT);
    visit(forallExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    final boolean braces = forallPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.ALL);
    visit(forallPred.getSchText());
    print(Keyword.SPOT);
    visit(forallPred.getPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    print(TokenName.ZED);
    visit(freePara.getFreetypeList());
    print(TokenName.END);
    return null;
  }

  public Object visitZFreetypeList(ZFreetypeList zFreetypeList)
  {
    printTermList(zFreetypeList, Keyword.ANDALSO);
    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    ref_ = false;
    visit(freetype.getName());
    print(Keyword.DEFFREE);
    visit(freetype.getBranchList());
    return null;
  }

  public Object visitGenericType(GenericType genType)
  {
    throw new PrintException("Unexpected term GenType");
  }

  public Object visitGenParamType(GenParamType genType)
  {
    throw new PrintException("Unexpected term GenType");
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    ref_ = false;
    print(TokenName.ZED);
    print(TokenName.LSQUARE);
    printTermList(givenPara.getNames());
    print(TokenName.RSQUARE);
    print(TokenName.END);
    return null;
  }

  public Object visitGivenType(GivenType givenType)
  {
    throw new PrintException("Unexpected term GenType");
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    final boolean braces = hideExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(hideExpr.getExpr());
    print(Keyword.ZHIDE);
    print(TokenName.LPAREN);
    ref_ = false;
    printTermList(hideExpr.getZNameList());
    print(TokenName.RPAREN);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    final boolean braces = iffExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(iffExpr.getLeftExpr());
    print(Keyword.IFF);
    visit(iffExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    final boolean braces = iffPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(iffPred.getLeftPred());
    print(Keyword.IFF);
    visit(iffPred.getRightPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    final boolean braces = impliesExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(impliesExpr.getLeftExpr());
    print(Keyword.IMP);
    visit(impliesExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    final boolean braces = impliesPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(impliesPred.getLeftPred());
    print(Keyword.IMP);
    visit(impliesPred.getRightPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    visit(inclDecl.getExpr());
    return null;
  }

  public Object visitInStroke(InStroke inStroke)
  {
    print(TokenName.INSTROKE);
    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    final boolean braces = eves() || lambdaExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.LAMBDA);
    visit(lambdaExpr.getSchText());
    print(Keyword.SPOT);
    visit(lambdaExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    final boolean braces = eves() || letExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.LET);
    visit(letExpr.getSchText());
    print(Keyword.SPOT);
    visit(letExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitLatexMarkupPara(LatexMarkupPara latexMarkupPara)
  {
    // TODO: what now?
    return null;
  }

  public Object visitLocAnn(LocAnn locAnn)
  {
    throw new PrintException("Unexpeced term LocAnn");
  }

  public Object visitMemPred(MemPred memPred)
  {
    throw new PrintException("Unexpeced term MemPred");
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    if (muExpr.getExpr() != null) {
      final boolean braces = eves() || muExpr.getAnn(ParenAnn.class) != null;
      if (braces) print(TokenName.LPAREN);
      print(Keyword.MU);
      visit(muExpr.getSchText());
      print(Keyword.SPOT);
      visit(muExpr.getExpr());
      if (braces) print(TokenName.RPAREN);
    }
    else {
      print(TokenName.LPAREN);
      print(Keyword.MU);
      visit(muExpr.getSchText());
      print(TokenName.RPAREN);
    }
    return null;
  }

  public Object visitNewOldPair(NewOldPair pair)
  {
    visit(pair.getNewName());
    print(Keyword.SLASH);
    visit(pair.getOldName());
    return null;
  }

  public Object visitNameSectTypeTriple(NameSectTypeTriple triple)
  {
    String message = "Unexpected term NameSectTypeTriple.";
    throw new PrintException(message);
  }

  public Object visitNameTypePair(NameTypePair pair)
  {
    String message = "Unexpected term NameTypePair.";
    throw new PrintException(message);
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
      txt.append(iter.next().toString());
    }
    print(TokenName.TEXT, new LocString(txt.toString(), null));
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    final boolean braces = negExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.NOT);
    visit(negExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    final boolean braces = negPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.NOT);
    visit(negPred.getPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    print(TokenName.NEXTSTROKE);
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    final boolean braces = numExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(numExpr.getNumeral());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitZNumeral(ZNumeral zNumeral)
  {
    print(TokenName.NUMERAL, new LocInt(zNumeral.getValue(), null));
    return null;
  }

  public Object visitNumStroke(NumStroke numStroke)
  {
    print(TokenName.NUMSTROKE,
          new LocInt(numStroke.getDigit().getValue(), null));
    return null;
  }

  public Object visitOperand(Operand operand)
  {
    if (operand.getList().booleanValue()) {
      print(Keyword.LISTARG);
    }
    else {
      print(Keyword.ARG);
    }
    return null;
  }

  public Object visitOperator(Operator operator)
  {
    print(TokenName.DECORWORD, new Decorword(operator.getWord()));
    return null;
  }

  public Object visitOperatorApplication(OperatorApplication appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    String message =
      printOperator(appl.getOperatorName(), appl.getArgs());
    if (message != null) {
      throw new PrintException("Cannot print appl");
    }
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    print(TokenName.ZED);
    final Cat cat = optempPara.getCat();
    if (Cat.Function.equals(cat)) {
      print(Keyword.FUNCTION);
    }
    else if (Cat.Generic.equals(cat)) {
      print(Keyword.GENERIC);
    }
    else if (Cat.Relation.equals(cat)) {
      print(Keyword.RELATION);
    }
    if (optempPara.getPrec() != null) {
      print(TokenName.NUMERAL, new LocInt(optempPara.getPrec(), null));
    }
    final Assoc assoc = optempPara.getAssoc();
    if (Assoc.Left.equals(assoc)) {
      print(Keyword.LEFTASSOC);
    }
    else if (Assoc.Right.equals(assoc)) {
      print(Keyword.RIGHTASSOC);
    }
    print(TokenName.LPAREN);
    List list = optempPara.getOper();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
    }
    print(TokenName.RPAREN);
    print(TokenName.END);
    return null;
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    final boolean braces = orExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(orExpr.getLeftExpr());
    print(Keyword.OR);
    visit(orExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    final boolean braces = orPred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(orPred.getLeftPred());
    print(Keyword.OR);
    visit(orPred.getRightPred());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitOutStroke(OutStroke outStroke)
  {
    print(TokenName.OUTSTROKE);
    return null;
  }

  public Object visitParenAnn(ParenAnn parenAnn)
  {
    throw new PrintException("Unexpected term ParenAnn.");
  }

  public Object visitParent(Parent parent)
  {
    String word = parent.getWord();
    if (word == null) throw new PrintException("Invalid (null) parent");
    print(TokenName.DECORWORD, new Decorword(word));
    return null;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    final boolean braces = pipeExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(pipeExpr.getLeftExpr());
    print(Keyword.ZPIPE);
    visit(pipeExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    final boolean braces = powerExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.POWER);
    visit(powerExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new PrintException("Unexpected term PowerType.");
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    final boolean braces = preExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.ZPRE);
    visit(preExpr.getExpr());
    if (braces) print(TokenName.RPAREN);
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
        print(TokenName.DECORWORD, new Decorword((String) object));
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
    if (braces) print(TokenName.LPAREN);
    Object[] array = printPredicate.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof Token) {
        print((Token) object);
      }
      else if (object instanceof String) {
        print(TokenName.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitPrintExpression(PrintExpression printExpression)
  {
    final boolean braces = printExpression.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    Object[] array = printExpression.getChildren();
    for (int i = 0; i < array.length; i++) {
      Object object = array[i];
      if (object instanceof String) {
        print(TokenName.DECORWORD, new Decorword((String) object));
      }
      else if (object instanceof Term) {
        visit((Term) object);
      }
    }
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    final boolean braces = prodExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    printTermList(prodExpr.getZExprList(), Keyword.CROSS);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new PrintException("Unexpected term ProdType.");
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    final boolean braces = projExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(projExpr.getLeftExpr());
    print(Keyword.ZPROJ);
    visit(projExpr.getRightExpr());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    final boolean braces = refExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    if (refExpr.getMixfix().booleanValue()) {
      String message = "RefExpr with Mixfix set to true are not contained " +
        "in print trees; did you run the AstToPrintTreeVisitor before " +
        "calling this ZPrintVisitor?";
      throw new PrintException(message);
    }
    else { // Mixfix == false
      ref_ = true;
      visit(refExpr.getName());
      if (refExpr.getZExprList().size() > 0 && refExpr.getExplicit()) {
        print(TokenName.LSQUARE);
        printTermList(refExpr.getZExprList());
        print(TokenName.RSQUARE);
      }
    }
    if (braces) print(TokenName.RPAREN);
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
      print(TokenName.DECORWORD,
            new Decorword(word, name.getZStrokeList()));
      return null;
    }
    if (braces || ref_) print(TokenName.LPAREN);
    for (String wordPart : op.getWords()) {
      if (wordPart.equals(ZString.LISTARG) || wordPart.equals(ZString.ARG)) {
        printDecorword(wordPart);
      }
      else {
        printDecorword(new Decorword(wordPart, (ZStrokeList) op.getStrokes()));
      }
    }
    if (braces || ref_) print(TokenName.RPAREN);
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
    if (braces) print(TokenName.LPAREN);
    visit(renameExpr.getExpr());
    print(TokenName.LSQUARE);
    printTermList(renameExpr.getZRenameList());
    print(TokenName.RSQUARE);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    throw new PrintException("Unexpected term SchemaType.");
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    String name = (String) schExpr.getAnn(String.class);
    if (name != null) {
      print(TokenName.DECORWORD, new Decorword(name));
    }
    else {
      print(TokenName.LSQUARE);
      visit(schExpr.getSchText());
      print(TokenName.RSQUARE);
    }
    return null;
  }

  public Object visitZSchText(ZSchText schText)
  {
    visit(schText.getDeclList());
    if (schText.getPred() != null) {
      print(Keyword.BAR);
      visit(schText.getPred());
    }
    return null;
  }

  public Object visitZDeclList(ZDeclList zDeclList)
  {
    printTermList(zDeclList.getDecl(), Keyword.SEMICOLON);
    return null;
  }

  public Object visitSectTypeEnvAnn(SectTypeEnvAnn ann)
  {
    throw new PrintException("Unexpected term SectTypeEnvAnn.");
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    print(TokenName.LBRACE);
    visit(setCompExpr.getSchText());
    if (setCompExpr.getExpr() != null) {
      print(Keyword.SPOT);
      visit(setCompExpr.getExpr());
    }
    print(TokenName.RBRACE);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    print(TokenName.LBRACE);
    printTermList(setExpr.getZExprList());
    print(TokenName.RBRACE);
    return null;
  }

  public Object visitSignature(Signature s)
  {
    throw new PrintException("Unexpected term Signature.");
  }

  public Object visitSpec(Spec spec)
  {
    visit(spec.getSect());
    return null;
  }

  public Object visitThetaExpr(ThetaExpr thetaExpr)
  {
    final boolean braces = thetaExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStrokeList());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitTruePred(TruePred truePred)
  {
    final boolean braces = truePred.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    print(Keyword.TRUE);
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    print(TokenName.LPAREN);
    printTermList(tupleExpr.getZExprList());
    print(TokenName.RPAREN);
    return null;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    final boolean braces = tupleSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(TokenName.LPAREN);
    visit(tupleSelExpr.getExpr());
    print(Keyword.DOT);
    visit(tupleSelExpr.getNumeral());
    if (braces) print(TokenName.RPAREN);
    return null;
  }

  public Object visitSignatureAnn(SignatureAnn typeAnn)
  {
    throw new PrintException("Unexpected term SignatureAnn.");
  }

  public Object visitTypeAnn(TypeAnn typeAnn)
  {
    throw new PrintException("Unexpected term TypeAnn.");
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
    print(Keyword.COLON);
    visit(varDecl.getExpr());
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    if (! ZUtils.isAnonymous(zSect)) {
      final String name = zSect.getName();
      final List parents = zSect.getParent();
      print(TokenName.ZED);
      print(Keyword.SECTION);
      if (name == null) throw new PrintException("Invalid section name.");
      print(TokenName.DECORWORD, new Decorword(name));
      if (parents.size() > 0) {
        print(Keyword.PARENTS);
        printTermList(parents);
      }
      print(TokenName.END);
    }
    visit(zSect.getParaList());
    return null;
  }

  public Object visitZParaList(ZParaList list)
  {
    for (Para p : list) {
      visit(p);
    }
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
    print(Keyword.AND);
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
      op = new OperatorName(ref.getZName());
    }
    catch (OperatorName.OperatorNameException e) {
      return "Unexpected operator " + ref.getZName().getWord();
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
    for (String opPart : op.getWords()) {
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
          if (i.hasNext()) print(Keyword.COMMA);
        }
        pos++;
      }
      else {
        final Decorword decorword =
          new Decorword(opPart, (ZStrokeList) op.getStrokes());
        print(TokenName.DECORWORD, decorword);
      }
    }
    return null;
  }

  protected void printTermList(List list)
  {
    printTermList(list, Keyword.COMMA);
  }

  /**
   * @throws NullPointerException if separator is <code>null</code>.
   */
  protected void printTermList(List list, Keyword separator)
  {
    if (separator == null) throw new NullPointerException();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext()) {
        print(separator);
      }
    }
  }

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
        printDecorword(separator);
      }
    }
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
