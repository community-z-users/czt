/**
Copyright (C) 2004 Petra Malik
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
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.util.Visitor;
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
             ApplicationVisitor, OperatorApplicationVisitor
{
  private SectionInfo sectInfo_;
  private OpTable opTable_;

  /**
   * Creates a new Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public ZPrintVisitor(ZPrinter printer, SectionInfo sectInfo)
  {
    super(printer);
    sectInfo_ = sectInfo;
  }

  /**
   * Visit all children of a term.
   */
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

  public Object visitAndExpr(AndExpr andExpr)
  {
    final boolean braces = andExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(andExpr.getLeftExpr());
    printAnd();
    visit(andExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    final boolean braces = andPred.getAnn(ParenAnn.class) != null;
    Pred pred1 = andPred.getLeftPred();
    Pred pred2 = andPred.getRightPred();

    if (braces) print(Sym.LPAREN);
    if (Op.And.equals(andPred.getOp())) {
      print(pred1, ZString.AND, pred2);
    }
    else if (Op.Chain.equals(andPred.getOp())) {
      try {
        MemPred memPred1 = (MemPred) pred1;
        MemPred memPred2 = (MemPred) pred2;
        TupleExpr tuple1 = (TupleExpr) memPred1.getLeftExpr();
        RefExpr op1 = (RefExpr) memPred1.getRightExpr();
        TupleExpr tuple2 = (TupleExpr) memPred2.getLeftExpr();
        RefExpr op2 = (RefExpr) memPred2.getRightExpr();
        List list1 = tuple1.getExpr();
        List list2 = tuple2.getExpr();
        if (list1.size() == 2 && list2.size() == 2 &&
            list1.get(1).equals(list2.get(0))) {
          String opName1 = getBinOperatorName(op1);
          String opName2 = getBinOperatorName(op2);
          visit((Term) list1.get(0));
          print(Sym.DECORWORD, opName1);
          visit((Term) list1.get(1));
          print(Sym.DECORWORD, opName2);
          visit((Term) list2.get(1));
          return null;
        }
        String message = "Unexpected Op == 'CHAIN' within AndPred.";
        System.err.println(message);
        print(pred1, ZString.AND, pred2);
      }
      catch (ClassCastException e) {
        String message = "Unexpected Op == 'CHAIN' within AndPred.";
        System.err.println(message);
        print(pred1, ZString.AND, pred2);
      }
      catch (NullPointerException e) {
        String message = "Unexpected Op == 'CHAIN' within AndPred.";
        System.err.println(message);
        print(pred1, ZString.AND, pred2);
      }
    }
    else if (Op.NL.equals(andPred.getOp())) {
      print(pred1, Sym.NL, pred2);
    }
    else if (Op.Semi.equals(andPred.getOp())) {
      print(pred1, ZString.SEMICOLON, pred2);
    }
    else {
      throw new CztException("Unexpected Op");
    }
    if (braces) print(Sym.RPAREN);
    return null;
  }

  /**
   * Prints the first term followed by the symbol followed by the
   * second term.
   */
  private void print(Term t1, int symbol, Term t2)
  {
    visit(t1);
    print(symbol);
    visit(t2);
  }

  /**
   * Prints the first term followed by the symbol followed by the
   * second term.
   */
  private void print(Term t1, String symbol, Term t2)
  {
    if (symbol == null) throw new CztException();
    visit(t1);
    print(Sym.DECORWORD, symbol);
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
    String word = refExpr.getRefName().getWord();
    String[] split = word.split(" ");
    final int expectedLength = 4;
    if (split.length == expectedLength &&
        split[1].equals("_") && split[3].equals("_")) {
      result = split[2];
    }
    if (result == null) {
      String message = "ZPrintVisitor: getBinOperatorName of " + word + " failed.";
      message += " split is " + split + " of length " + split.length;
      throw new CztException(message);
    }
    return result;
  }

  public Object visitApplication(Application appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(appl.getLeftExpr());
    visit(appl.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    throw new CztException("Unexpected term " + applExpr);
    /*
    final boolean braces = applExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    if (applExpr.getMixfix().booleanValue()) { // Mixfix == true
      String message =
        printOperator(applExpr.getLeftExpr(), applExpr.getRightExpr());
      if (message != null) {
        System.err.println(message);
        visit(applExpr.getLeftExpr());
        visit(applExpr.getRightExpr());
      }
    }
    else { // Mixfix == false
      visit(applExpr.getLeftExpr());
      visit(applExpr.getRightExpr());
    }
    if (braces) print(Sym.RPAREN);
    return null;
    */
  }

  public Object visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if (box == null || Box.AxBox.equals(box)) {
      if (axPara.getDeclName().isEmpty()) {
        print(Sym.AX);
      }
      else {
        print(Sym.GENAX);
        print(Sym.LSQUARE);
        printTermList(axPara.getDeclName());
        print(Sym.RSQUARE);
      }
      SchText schText = axPara.getSchText();
      printTermList(schText.getDecl(), Sym.NL);
      if (schText.getPred() != null) {
        print(Sym.WHERE);
        visit(schText.getPred());
      }
      print(Sym.END);
    }
    else if (Box.OmitBox.equals(box)) {
      print(Sym.ZED);
      List declNameList = axPara.getDeclName();
      if (declNameList.size() > 0) {
        final SchText schText = axPara.getSchText();
        final List decls = axPara.getSchText().getDecl();
        final ConstDecl constDecl = (ConstDecl) decls.get(0);
        final DeclName declName = constDecl.getDeclName();
        final OperatorName operatorName = declName.getOperatorName();
        final OpTable.OpInfo opInfo = operatorName == null ? null :
          opTable_.lookup(operatorName);

        if (opInfo != null && Cat.Generic.equals(opInfo.getCat())) {
          // generic operator definition
          printOperator(operatorName, axPara.getDeclName());
          print(Sym.DECORWORD, ZString.DEFEQUAL);
          visit(constDecl.getExpr());
        }
        else { // generic horizontal definition
          visit(declName);
          print(Sym.LSQUARE);
          printTermList(declNameList);
          print(Sym.RSQUARE);
          print(Sym.DECORWORD, ZString.DEFEQUAL);
          visit(constDecl.getExpr());
        }
      }
      else { // horizontal definition
        visit(axPara.getSchText());
      }
      print(Sym.END);
    }
    else if (Box.SchBox.equals(box)) {
      print(Sym.SCH);
      List decls = axPara.getSchText().getDecl();
      ConstDecl cdecl = (ConstDecl) decls.get(0);
      String declName = cdecl.getDeclName().getWord();
      if (declName == null) throw new CztException();
      print(Sym.DECORWORD, declName);
      SchExpr schExpr = (SchExpr) cdecl.getExpr();
      SchText schText = schExpr.getSchText();
      printTermList(schText.getDecl(), Sym.NL);
      if (schText.getPred() != null) {
        print(Sym.WHERE);
        visit(schText.getPred());
      }
      print(Sym.END);
    }
    else {
      throw new CztException("Unexpected Box " + box);
    }
    return null;
  }

  public Object visitBindExpr(BindExpr bindExpr)
  {
    final boolean braces = bindExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.LBIND);
    printTermList(bindExpr.getNameExprPair());
    print(Sym.RBIND);
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    final boolean braces = bindSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(bindSelExpr.getExpr());
    print(Sym.DECORWORD, ZString.DOT);
    visit(bindSelExpr.getName());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitBranch(Branch branch)
  {
    visit(branch.getDeclName());
    if (branch.getExpr() != null) {
      print(Sym.LDATA);
      visit(branch.getExpr());
      print(Sym.RDATA);
    }
    return null;
  }

  public Object visitCompExpr(CompExpr compExpr)
  {
    final boolean braces = compExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(compExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZCOMP);
    visit(compExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    final boolean braces = condExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.IF);
    visit(condExpr.getPred());
    print(Sym.DECORWORD, ZString.THEN);
    visit(condExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ELSE);
    visit(condExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitConjPara(ConjPara conjPara)
  {
    print(Sym.ZED);
    if (conjPara.getDeclName().size() > 0) {
      print(Sym.LSQUARE);
      visit(conjPara.getDeclName());
      print(Sym.RSQUARE);
    }
    print(Sym.DECORWORD, ZString.CONJECTURE);
    visit(conjPara.getPred());
    print(Sym.END);
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    visit(constDecl.getDeclName());
    print(Sym.DECORWORD, ZString.DEFEQUAL);
    visit(constDecl.getExpr());
    return null;
  }

  public Object visitDeclName(DeclName declName)
  {
    OperatorName op = declName.getOperatorName();
    if (op == null) {
      return visitName(declName);
    }
    for (Iterator iter = op.iterator(); iter.hasNext();) {
      print(Sym.DECORWORD, (String) iter.next());
    }
    return null;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    final boolean braces = decorExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    if (braces) print(Sym.RPAREN);
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
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.EXIONE);
    visit(exists1Expr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(exists1Expr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    final boolean braces = exists1Pred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.EXIONE);
    visit(exists1Pred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(exists1Pred.getPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    final boolean braces = existsExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.EXI);
    visit(existsExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(existsExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    final boolean braces = existsPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.EXI);
    visit(existsPred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(existsPred.getPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    final boolean braces = exprPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(exprPred.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitFalsePred(FalsePred falsePred)
  {
    print(Sym.DECORWORD, ZString.FALSE);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    final boolean braces = forallExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.ALL);
    visit(forallExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(forallExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    final boolean braces = forallPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.ALL);
    visit(forallPred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(forallPred.getPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    print(Sym.ZED);
    printTermList(freePara.getFreetype(), ZString.ANDALSO);
    print(Sym.END);
    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    visit(freetype.getDeclName());
    print(Sym.DECORWORD, ZString.DEFFREE);
    printTermList(freetype.getBranch(), ZString.BAR);
    return null;
  }

  public Object visitGenType(GenType genType)
  {
    throw new UnsupportedOperationException("Unexpected term GenType");
  }

  public Object visitGivenPara(GivenPara givenPara)
  {
    print(Sym.ZED);
    print(Sym.LSQUARE);
    printTermList(givenPara.getDeclName());
    print(Sym.RSQUARE);
    print(Sym.END);
    return null;
  }

  public Object visitGivenType(GivenType givenType)
  {
    throw new UnsupportedOperationException("Unexpected term GenType");
  }

  public Object visitHideExpr(HideExpr hideExpr)
  {
    final boolean braces = hideExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(hideExpr.getExpr());
    print(Sym.DECORWORD, ZString.ZHIDE);
    printTermList(hideExpr.getName());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    final boolean braces = iffExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(iffExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.IFF);
    visit(iffExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    final boolean braces = iffPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(iffPred.getLeftPred());
    print(Sym.DECORWORD, ZString.IFF);
    visit(iffPred.getRightPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    final boolean braces = impliesExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(impliesExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.IMP);
    visit(impliesExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    final boolean braces = impliesPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(impliesPred.getLeftPred());
    print(Sym.DECORWORD, ZString.IMP);
    visit(impliesPred.getRightPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitInclDecl(InclDecl inclDecl)
  {
    visit(inclDecl.getExpr());
    return null;
  }

  public Object visitInStroke(InStroke inStroke)
  {
    print(Sym.INSTROKE);
    return null;
  }

  public Object visitLambdaExpr(LambdaExpr lambdaExpr)
  {
    final boolean braces = lambdaExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.LAMBDA);
    visit(lambdaExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(lambdaExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    final boolean braces = letExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.LET);
    visit(letExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(letExpr.getExpr());
    if (braces) print(Sym.RPAREN);
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
    final boolean braces = memPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    if (memPred.getMixfix().booleanValue()) { // Mixfix == true
      Expr operand = memPred.getLeftExpr();
      Expr operator = memPred.getRightExpr();
      String message = printOperator(operator, operand);
      if (message != null) {
        System.err.println(message);
        visit(operand);
        visit(operator);
      }
    }
    else { // Mixfix == false
      visit(memPred.getLeftExpr());
      print(Sym.DECORWORD, ZString.MEM);
      visit(memPred.getRightExpr());
    }
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    if (muExpr.getExpr() != null) {
      final boolean braces = muExpr.getAnn(ParenAnn.class) != null;
      if (braces) print(Sym.LPAREN);
      print(Sym.DECORWORD, ZString.MU);
      visit(muExpr.getSchText());
      print(Sym.DECORWORD, ZString.SPOT);
      visit(muExpr.getExpr());
      if (braces) print(Sym.RPAREN);
    }
    else {
      print(Sym.LPAREN);
      print(Sym.DECORWORD, ZString.MU);
      visit(muExpr.getSchText());
      print(Sym.RPAREN);
    }
    return null;
  }

  public Object visitName(Name name)
  {
    String decorword = name.toString();
    if (decorword == null) {
      Logger logger = CztLogger.getLogger(ZPrintVisitor.class);
      logger.warning("Found empty name!");
    }
    print(Sym.DECORWORD, decorword);
    return null;
  }

  public Object visitNameExprPair(NameExprPair pair)
  {
    visit(pair.getName());
    print(Sym.DECORWORD, ZString.DEFEQUAL);
    visit(pair.getExpr());
    return null;
  }

  public Object visitNameNamePair(NameNamePair pair)
  {
    visit(pair.getNewName());
    print(Sym.DECORWORD, ZString.SLASH);
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
    print(Sym.TEXT, txt.toString());
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    final boolean braces = negExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.NOT);
    visit(negExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    final boolean braces = negPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.NOT);
    visit(negPred.getPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    print(Sym.NEXTSTROKE);
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    final boolean braces = numExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.NUMERAL, Integer.valueOf(numExpr.getValue().toString()));
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitNumStroke(NumStroke numStroke)
  {
    print(Sym.NUMSTROKE, numStroke.getNumber());
    return null;
  }

  public Object visitOperand(Operand operand)
  {
    if (operand.getList().booleanValue()) {
      print(Sym.DECORWORD, ZString.LISTARG);
    }
    else {
      print(Sym.DECORWORD, ZString.ARG);
    }
    return null;
  }

  public Object visitOperator(Operator operator)
  {
    String word = operator.getWord();
    if (word == null) throw new CztException();
    print(Sym.DECORWORD, word);
    return null;
  }

  public Object visitOperatorApplication(OperatorApplication appl)
  {
    final boolean braces = appl.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    String message =
      printOperator(appl.getOperatorName(), appl.getArgs());
    if (message != null) {
      throw new CztException("Cannot print appl");
    }
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    print(Sym.ZED);
    final Cat cat = optempPara.getCat();
    if (Cat.Function.equals(cat)) {
      print(Sym.DECORWORD, ZString.FUNCTION);
    }
    else if (Cat.Generic.equals(cat)) {
      print(Sym.DECORWORD, ZString.GENERIC);
    }
    else if (Cat.Relation.equals(cat)) {
      print(Sym.DECORWORD, ZString.RELATION);
    }
    if (optempPara.getPrec() != null) {
      print(Sym.NUMERAL, optempPara.getPrec());
    }
    final Assoc assoc = optempPara.getAssoc();
    if (Assoc.Left.equals(assoc)) {
      print(Sym.DECORWORD, ZString.LEFTASSOC);
    }
    else if (Assoc.Right.equals(assoc)) {
      print(Sym.DECORWORD, ZString.RIGHTASSOC);
    }
    print(Sym.LPAREN);
    List list = optempPara.getOper();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
    }
    print(Sym.RPAREN);
    print(Sym.END);
    return null;
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    final boolean braces = orExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(orExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.OR);
    visit(orExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    final boolean braces = orPred.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(orPred.getLeftPred());
    print(Sym.DECORWORD, ZString.OR);
    visit(orPred.getRightPred());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitOutStroke(OutStroke outStroke)
  {
    print(Sym.OUTSTROKE);
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
    print(Sym.DECORWORD, word);
    return null;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    final boolean braces = pipeExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(pipeExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZPIPE);
    visit(pipeExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    final boolean braces = powerExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.POWER);
    visit(powerExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new UnsupportedOperationException("Unexpected term PowerType.");
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    final boolean braces = preExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.PRE);
    visit(preExpr.getExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    final boolean braces = prodExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    printTermList(prodExpr.getExpr(), ZString.CROSS);
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new UnsupportedOperationException("Unexpected term ProdType.");
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    final boolean braces = projExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(projExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZPROJ);
    visit(projExpr.getRightExpr());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    final boolean braces = refExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    if (refExpr.getMixfix().booleanValue()) {
      String message = printOperator(refExpr, refExpr.getExpr());
      if (message != null) {
        System.err.println(message);
        visit(refExpr.getRefName());
        printTermList(refExpr.getExpr());
      }
    }
    else { // Mixfix == false
      visit(refExpr.getRefName());
      if (refExpr.getExpr().size() > 0) {
        print(Sym.LSQUARE);
        printTermList(refExpr.getExpr());
        print(Sym.RSQUARE);
      }
    }
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitRefName(RefName refName)
  {
    OperatorName op = refName.getOperatorName();
    if (op == null) {
      return visitName(refName);
    }
    print(Sym.LPAREN);
    for (Iterator iter = op.iterator(); iter.hasNext(); ) {
      print(Sym.DECORWORD, (String) iter.next());
    }
    print(Sym.RPAREN);
    return null;
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    final boolean braces = renameExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(renameExpr.getExpr());
    print(Sym.LSQUARE);
    printTermList(renameExpr.getNameNamePair());
    print(Sym.RSQUARE);
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitSchemaType(SchemaType schemaType)
  {
    throw new UnsupportedOperationException("Unexpected term SchemaType.");
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
    print(Sym.LSQUARE);
    visit(schExpr.getSchText());
    print(Sym.RSQUARE);
    return null;
  }

  public Object visitSchText(SchText schText)
  {
    printTermList(schText.getDecl(), ZString.SEMICOLON);
    if (schText.getPred() != null) {
      print(Sym.DECORWORD, ZString.BAR);
      visit(schText.getPred());
    }
    return null;
  }

  public Object visitSectTypeEnvAnn(SectTypeEnvAnn ann)
  {
    throw new UnsupportedOperationException("Unexpected term SectTypeEnvAnn.");
  }

  public Object visitSetCompExpr(SetCompExpr setCompExpr)
  {
    print(Sym.LBRACE);
    visit(setCompExpr.getSchText());
    if (setCompExpr.getExpr() != null) {
      print(Sym.DECORWORD, ZString.SPOT);
      visit(setCompExpr.getExpr());
    }
    print(Sym.RBRACE);
    return null;
  }

  public Object visitSetExpr(SetExpr setExpr)
  {
    print(Sym.LBRACE);
    printTermList(setExpr.getExpr());
    print(Sym.RBRACE);
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
    if (braces) print(Sym.LPAREN);
    print(Sym.DECORWORD, ZString.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStroke());
    if (braces) print(Sym.RPAREN);
    return null;
  }

  public Object visitTruePred(TruePred truePred)
  {
    print(Sym.DECORWORD, ZString.TRUE);
    return null;
  }

  public Object visitTupleExpr(TupleExpr tupleExpr)
  {
    print(Sym.LPAREN);
    printTermList(tupleExpr.getExpr());
    print(Sym.RPAREN);
    return null;
  }

  public Object visitTupleSelExpr(TupleSelExpr tupleSelExpr)
  {
    final boolean braces = tupleSelExpr.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
    visit(tupleSelExpr.getExpr());
    print(Sym.DECORWORD, ZString.DOT);
    print(Sym.NUMERAL, tupleSelExpr.getSelect());
    if (braces) print(Sym.RPAREN);
    return null;
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
    print(Sym.DECORWORD, ZString.COLON);
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

    opTable_ = (OpTable) sectInfo_.getInfo(name, OpTable.class);

    if (! isAnonymous) {
      print(Sym.ZED);
      print(Sym.SECTION);
      if (name == null) throw new CztException();
      print(Sym.DECORWORD, name);
      if (parents.size() > 0) {
        print(Sym.PARENTS);
        printTermList(parents);
      }
      print(Sym.END);
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
    print(Sym.DECORWORD, ZString.AND);
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
      op = new OperatorName(ref.getRefName());
    }
    catch (OperatorName.OperatorNameException e) {
      return "Unexpected operator " + ref.getRefName().getWord();
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
        args = tuple.getExpr();
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
        List sequence = setExpr.getExpr();
        for (Iterator i = sequence.iterator(); i.hasNext();) {
          Object o = i.next();
          if (! (o instanceof TupleExpr)) {
            return "Expected TupleExpr but got " + o;
          }
          TupleExpr tuple = (TupleExpr) o;
          List tupleContents = tuple.getExpr();
          if (tupleContents.size() != 2) {
            return "Expected tuple of size 2 but was " + tupleContents.size();
          }
          visit((Expr) tupleContents.get(1));
          if (i.hasNext()) print(Sym.DECORWORD, ZString.COMMA);
        }
        pos++;
      }
      else {
        print(Sym.DECORWORD, opPart);
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

  private void printTermList(List list)
  {
    printTermList(list, ZString.COMMA);
  }

  private void printTermList(List list, int separator)
  {
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
  private void printTermList(List list, String separator)
  {
    if (separator == null) throw new NullPointerException();
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      visit(term);
      if (iter.hasNext()) {
        print(Sym.DECORWORD, separator);
      }
    }
  }
}
