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


import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.parser.util.OpName;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class ZPrintVisitor
  extends AbstractPrintVisitor
  implements Visitor, ZVisitor
{
  public ZPrintVisitor(ZPrinter printer)
  {
    super(printer);
    AbstractPrintVisitor bracketsVisitor = new BracketsVisitor(printer);
    bracketsVisitor.setVisitor(this);
    setVisitor(bracketsVisitor);
  }

  /**
   * Visit all children of a term.
   */
  public Object visitTerm(Term term)
  {
    VisitorUtils.visitArray(this, term.getChildren());
    return null;
  }

  public Object visitAndExpr(AndExpr andExpr)
  {
    visit(andExpr.getLeftExpr());
    printAnd();
    visit(andExpr.getRightExpr());
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    Pred pred1 = andPred.getLeftPred();
    Pred pred2 = andPred.getRightPred();

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
          String opName1 = getBinOpName(op1);
          String opName2 = getBinOpName(op2);
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
  private String getBinOpName(RefExpr refExpr)
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
      String message = "ZPrintVisitor: getBinOpName of " + word + " failed.";
      message += " split is " + split + " of length " + split.length;
      throw new CztException(message);
    }
    return result;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
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
    return null;
  }

  public Object visitAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if (box == null || Box.AxBox.equals(box)) {
      print(Sym.AX);
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
      visit(axPara.getSchText());
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
    print(Sym.LBIND);
    printTermList(bindExpr.getNameExprPair());
    print(Sym.RBIND);
    return null;
  }

  public Object visitBindSelExpr(BindSelExpr bindSelExpr)
  {
    visit(bindSelExpr.getExpr());
    print(Sym.DECORWORD, ZString.DOT);
    visit(bindSelExpr.getName());
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
    visit(compExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZCOMP);
    visit(compExpr.getRightExpr());
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    print(Sym.DECORWORD, ZString.IF);
    visit(condExpr.getPred());
    print(Sym.DECORWORD, ZString.THEN);
    visit(condExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ELSE);
    visit(condExpr.getRightExpr());
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
    String name = declName.getWord();
    if (OpName.isOpName(name)) {
      try {
        OpName op = new OpName(name);
        assert declName.getStroke().size() == 0;
        for (Iterator iter = op.iterator(); iter.hasNext();) {
          print(Sym.DECORWORD, (String) iter.next());
        }
      }
      catch (OpName.OpNameException e) {
        print(Sym.DECORWORD, name);
        System.err.println("WARNING: Unexpected Operator " + name);
      }
      return null;
    }
    return visitName(declName);
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    return null;
  }

  public Object visitDirective(Directive directive)
  {
    // do nothing for now
    return null;
  }

  public Object visitExists1Expr(Exists1Expr exists1Expr)
  {
    print(Sym.DECORWORD, ZString.EXIONE);
    visit(exists1Expr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(exists1Expr.getExpr());
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    print(Sym.DECORWORD, ZString.EXIONE);
    visit(exists1Pred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(exists1Pred.getPred());
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    print(Sym.DECORWORD, ZString.EXI);
    visit(existsExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(existsExpr.getExpr());
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    print(Sym.DECORWORD, ZString.EXI);
    visit(existsPred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(existsPred.getPred());
    return null;
  }

  public Object visitExprPred(ExprPred exprPred)
  {
    visit(exprPred.getExpr());
    return null;
  }

  public Object visitFalsePred(FalsePred falsePred)
  {
    print(Sym.DECORWORD, ZString.FALSE);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    print(Sym.DECORWORD, ZString.ALL);
    visit(forallExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(forallExpr.getExpr());
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    print(Sym.DECORWORD, ZString.ALL);
    visit(forallPred.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(forallPred.getPred());
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
    visit(hideExpr.getExpr());
    print(Sym.DECORWORD, ZString.ZHIDE);
    printTermList(hideExpr.getName());
    return null;
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    visit(iffExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.IFF);
    visit(iffExpr.getRightExpr());
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    visit(iffPred.getLeftPred());
    print(Sym.DECORWORD, ZString.IFF);
    visit(iffPred.getRightPred());
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    visit(impliesExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.IMP);
    visit(impliesExpr.getRightExpr());
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    visit(impliesPred.getLeftPred());
    print(Sym.DECORWORD, ZString.IMP);
    visit(impliesPred.getRightPred());
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
    print(Sym.DECORWORD, ZString.LAMBDA);
    visit(lambdaExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(lambdaExpr.getExpr());
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    print(Sym.DECORWORD, ZString.LET);
    visit(letExpr.getSchText());
    print(Sym.DECORWORD, ZString.SPOT);
    visit(letExpr.getExpr());
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
    return null;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    print(Sym.DECORWORD, ZString.MU);
    visit(muExpr.getSchText());
    if (muExpr.getExpr() != null) {
      print(Sym.DECORWORD, ZString.SPOT);
      visit(muExpr.getExpr());
    }
    return null;
  }

  public Object visitName(Name name)
  {
    String decorword = name.getWord();
    for (Iterator iter = name.getStroke().iterator(); iter.hasNext();)
    {
      Stroke stroke = (Stroke) iter.next();
      if (stroke instanceof InStroke) decorword += ZString.INSTROKE;
      else if (stroke instanceof OutStroke) decorword += ZString.OUTSTROKE;
      else if (stroke instanceof NextStroke) decorword += ZString.PRIME;
      else if (stroke instanceof NumStroke) {
        NumStroke numStroke = (NumStroke) stroke;
        decorword += ZString.SE;
        decorword += numStroke.getNumber().toString();
        decorword += ZString.NW;
      }
    }
    if (decorword == null) throw new CztException();
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
    String txt = "";
    for (Iterator iter = narrPara.getContent().iterator(); iter.hasNext();) {
      txt += (String) iter.next();
    }
    print(Sym.TEXT, txt);
    return null;
  }

  public Object visitNarrSect(NarrSect narrSect)
  {
    String txt = "";
    for (Iterator iter = narrSect.getContent().iterator(); iter.hasNext();) {
      txt += (String) iter.next();
    }
    print(Sym.TEXT, txt);
    return null;
  }

  public Object visitNegExpr(NegExpr negExpr)
  {
    print(Sym.DECORWORD, ZString.NOT);
    visit(negExpr.getExpr());
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    print(Sym.DECORWORD, ZString.NOT);
    visit(negPred.getPred());
    return null;
  }

  public Object visitNextStroke(NextStroke nextStroke)
  {
    print(Sym.NEXTSTROKE);
    return null;
  }

  public Object visitNumExpr(NumExpr numExpr)
  {
    print(Sym.NUMERAL, Integer.valueOf(numExpr.getValue().toString()));
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
      term.accept(getVisitor());
    }
    print(Sym.RPAREN);
    print(Sym.END);
    return null;
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    visit(orExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.OR);
    visit(orExpr.getRightExpr());
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    visit(orPred.getLeftPred());
    print(Sym.DECORWORD, ZString.OR);
    visit(orPred.getRightPred());
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
    visit(pipeExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZPIPE);
    visit(pipeExpr.getRightExpr());
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    print(Sym.DECORWORD, ZString.POWER);
    visit(powerExpr.getExpr());
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new UnsupportedOperationException("Unexpected term PowerType.");
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    print(Sym.DECORWORD, ZString.PRE);
    visit(preExpr.getExpr());
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    printTermList(prodExpr.getExpr(), ZString.CROSS);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new UnsupportedOperationException("Unexpected term ProdType.");
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    visit(projExpr.getLeftExpr());
    print(Sym.DECORWORD, ZString.ZPROJ);
    visit(projExpr.getRightExpr());
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
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
    return null;
  }

  public Object visitRefName(RefName refName)
  {
    String name = refName.getWord();
    if (OpName.isOpName(name)) {
      try {
        OpName op = new OpName(name);
        assert refName.getStroke().size() == 0;
        print(Sym.LPAREN);
        for (Iterator iter = op.iterator(); iter.hasNext(); ) {
          print(Sym.DECORWORD, (String) iter.next());
        }
        print(Sym.RPAREN);
      }
      catch (OpName.OpNameException e) {
        print(Sym.DECORWORD, name);
        System.err.println("WARNING: Unexpected Operator " + name);
      }
      return null;
    }
    return visitName(refName);
  }

  public Object visitRenameExpr(RenameExpr renameExpr)
  {
    visit(renameExpr.getExpr());
    print(Sym.LSQUARE);
    printTermList(renameExpr.getNameNamePair());
    print(Sym.RSQUARE);
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
    printTermList(schText.getDecl(), Sym.NL);
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
    print(Sym.DECORWORD, ZString.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStroke());
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
    visit(tupleSelExpr.getExpr());
    print(Sym.DECORWORD, ZString.DOT);
    print(Sym.NUMERAL, tupleSelExpr.getSelect());
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
    if (! isAnonymous) {
      print(Sym.ZED);
      print(Sym.SECTION);
      if (name == null) throw new CztException();
      print(Sym.DECORWORD, name);
      if (parents.size() > 0) {
        print(Sym.PARENTS);
        visit(zSect.getParent());
      }
      print(Sym.END);
    }
    visit(zSect.getPara());
    return null;
  }

  private void visit(List list)
  {
    VisitorUtils.visitList(this, list);
  }

  private void visit(Term t)
  {
    if (t != null) {
      t.accept(getVisitor());
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
    OpName op = null;
    try {
      op = new OpName(ref.getRefName().getWord());
    }
    catch (OpName.OpNameException e) {
      return "Unexpected operator " + op.toString();
    }
    assert op != null;
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
        visit((Expr) args.get(pos));
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
      }
    }
    return null;
  }

  private void printTermList(List list)
  {
    printTermList(list, ZString.COMMA);
  }

  private void printTermList(List list, int separator)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      term.accept(getVisitor());
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
      term.accept(getVisitor());
      if (iter.hasNext()) {
        print(Sym.DECORWORD, separator);
      }
    }
  }
}
