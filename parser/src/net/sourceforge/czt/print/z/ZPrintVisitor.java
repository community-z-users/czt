/**
Copyright 2004 Petra Malik
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

import java.util.Iterator;
import java.util.List;

import java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;

import net.sourceforge.czt.util.CztException;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;

/**
 * A Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class ZPrintVisitor
  implements ZVisitor
{
  private ZPrinter printer_;

  public ZPrintVisitor(ZPrinter printer)
  {
    printer_ = printer;
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
    print(Sym.AND);
    visit(andExpr.getRightExpr());
    return null;
  }

  public Object visitAndPred(AndPred andPred)
  {
    visit(andPred.getLeftPred());
    if (Op.And.equals(andPred.getOp())) {
      print(Sym.AND);
    }
    else if (Op.Chain.equals(andPred.getOp())) {
      // TODO: Find out how to handle AndPred with Op == Chain.
      print(Sym.AND);
    }
    else if (Op.NL.equals(andPred.getOp())) {
      print(Sym.NL);
    }
    else if (Op.Semi.equals(andPred.getOp())) {
      print(Sym.SEMICOLON);
    }
    else {
      throw new CztException("Unexpected Op");
    }
    visit(andPred.getRightPred());
    return null;
  }

  public Object visitApplExpr(ApplExpr applExpr)
  {
    if (applExpr.getMixfix().booleanValue()) {
      // TODO: ApplExpr with Mixfix == true
      visit(applExpr.getLeftExpr());
      visit(applExpr.getRightExpr());
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
      visit(axPara.getSchText());
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
      print(Sym.DECORWORD, declName);
      SchExpr schExpr = (SchExpr) cdecl.getExpr();
      visit(schExpr.getSchText());
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
    print(Sym.DOT);
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
    print(Sym.ZCOMP);
    visit(compExpr.getRightExpr());
    return null;
  }

  public Object visitCondExpr(CondExpr condExpr)
  {
    print(Sym.IF);
    visit(condExpr.getPred());
    print(Sym.THEN);
    visit(condExpr.getLeftExpr());
    print(Sym.ELSE);
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
    print(Sym.CONJECTURE);
    visit(conjPara.getPred());
    print(Sym.END);
    return null;
  }

  public Object visitConstDecl(ConstDecl constDecl)
  {
    visit(constDecl.getDeclName());
    print(Sym.DEFEQUAL);
    visit(constDecl.getExpr());
    return null;
  }

  public Object visitDeclName(DeclName declName)
  {
    print(Sym.DECORWORD, declName.getWord());
    return null;
  }

  public Object visitDecorExpr(DecorExpr decorExpr)
  {
    visit(decorExpr.getExpr());
    visit(decorExpr.getStroke());
    return null;
  }

  public Object visitExists1Expr(Exists1Expr exists1Expr)
  {
    print(Sym.EXI);
    visit(exists1Expr.getSchText());
    print(Sym.DOT);
    visit(exists1Expr.getExpr());
    return null;
  }

  public Object visitExists1Pred(Exists1Pred exists1Pred)
  {
    print(Sym.EXI);
    visit(exists1Pred.getSchText());
    print(Sym.DOT);
    visit(exists1Pred.getPred());
    return null;
  }

  public Object visitExistsExpr(ExistsExpr existsExpr)
  {
    print(Sym.EXIONE);
    visit(existsExpr.getSchText());
    print(Sym.DOT);
    visit(existsExpr.getExpr());
    return null;
  }

  public Object visitExistsPred(ExistsPred existsPred)
  {
    print(Sym.EXIONE);
    visit(existsPred.getSchText());
    print(Sym.DOT);
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
    print(Sym.FALSE);
    return null;
  }

  public Object visitForallExpr(ForallExpr forallExpr)
  {
    print(Sym.ALL);
    visit(forallExpr.getSchText());
    print(Sym.DOT);
    visit(forallExpr.getExpr());
    return null;
  }

  public Object visitForallPred(ForallPred forallPred)
  {
    print(Sym.ALL);
    visit(forallPred.getSchText());
    print(Sym.DOT);
    visit(forallPred.getPred());
    return null;
  }

  public Object visitFreePara(FreePara freePara)
  {
    print(Sym.ZED);
    printTermList(freePara.getFreetype(), Sym.ANDALSO);
    print(Sym.END);
    return null;
  }

  public Object visitFreetype(Freetype freetype)
  {
    visit(freetype.getDeclName());
    print(Sym.DEFFREE);
    printTermList(freetype.getBranch(), Sym.BAR);
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
    print(Sym.ZHIDE);
    printTermList(hideExpr.getName());
    return null;
  }

  public Object visitIffExpr(IffExpr iffExpr)
  {
    visit(iffExpr.getLeftExpr());
    print(Sym.IFF);
    visit(iffExpr.getRightExpr());
    return null;
  }

  public Object visitIffPred(IffPred iffPred)
  {
    visit(iffPred.getLeftPred());
    print(Sym.IFF);
    visit(iffPred.getRightPred());
    return null;
  }

  public Object visitImpliesExpr(ImpliesExpr impliesExpr)
  {
    visit(impliesExpr.getLeftExpr());
    print(Sym.IMP);
    visit(impliesExpr.getRightExpr());
    return null;
  }

  public Object visitImpliesPred(ImpliesPred impliesPred)
  {
    visit(impliesPred.getLeftPred());
    print(Sym.IMP);
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
    print(Sym.LAMBDA);
    visit(lambdaExpr.getSchText());
    print(Sym.DOT);
    visit(lambdaExpr.getExpr());
    return null;
  }

  public Object visitLetExpr(LetExpr letExpr)
  {
    print(Sym.LET);
    visit(letExpr.getSchText());
    print(Sym.DOT);
    visit(letExpr.getExpr());
    return null;
  }

  public Object visitLocAnn(LocAnn locAnn)
  {
    throw new UnsupportedOperationException("Unexpeced term LocAnn");
  }

  public Object visitMemPred(MemPred memPred)
  {
    if (memPred.getMixfix().booleanValue()) {
      // Mixfix == true
      Expr operand = memPred.getLeftExpr();
      Expr operator = memPred.getRightExpr();
      visit(operand);
      visit(operator);
    }
    else { // Mixfix == false
      visit(memPred.getLeftExpr());
      print(Sym.MEM);
      visit(memPred.getRightExpr());
    }
    return null;
  }

  public Object visitMuExpr(MuExpr muExpr)
  {
    print(Sym.MU);
    visit(muExpr.getSchText());
    print(Sym.DOT);
    visit(muExpr.getExpr());
    return null;
  }

  public Object visitName(Name name)
  {
    print(Sym.DECORWORD, name.getWord());
    visit(name.getStroke());
    return null;
  }

  public Object visitNameExprPair(NameExprPair pair)
  {
    visit(pair.getName());
    print(Sym.DEFEQUAL);
    visit(pair.getExpr());
    return null;
  }

  public Object visitNameNamePair(NameNamePair pair)
  {
    visit(pair.getNewName());
    print(Sym.SLASH);
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
    print(Sym.NOT);
    visit(negExpr.getExpr());
    return null;
  }

  public Object visitNegPred(NegPred negPred)
  {
    print(Sym.NOT);
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
    // TODO: Find out how to handle Operand in OptempPara.
    return null;
  }

  public Object visitOperator(Operator operator)
  {
    print(Sym.DECORWORD, operator.getWord());
    return null;
  }

  public Object visitOptempPara(OptempPara optempPara)
  {
    print(Sym.ZED);
    Cat cat = optempPara.getCat();
    if (Cat.Function.equals(cat)) {
      print(Sym.FUNCTION);
    }
    else if (Cat.Generic.equals(cat)) {
      print(Sym.GENERIC);
    }
    else if (Cat.Relation.equals(cat)) {
      print(Sym.RELATION);
    }
    if (optempPara.getPrec() != null) {
      print(Sym.NUMERAL, optempPara.getPrec());
    }
    Assoc assoc = optempPara.getAssoc();
    if (Assoc.Left.equals(assoc)) {
      print(Sym.LEFTASSOC);
    }
    else if (Assoc.Right.equals(assoc)) {
      print(Sym.RIGHTASSOC);
    }
    printTermList(optempPara.getOper());
    print(Sym.END);
    return null;
  }

  public Object visitOrExpr(OrExpr orExpr)
  {
    visit(orExpr.getLeftExpr());
    print(Sym.OR);
    visit(orExpr.getRightExpr());
    return null;
  }

  public Object visitOrPred(OrPred orPred)
  {
    visit(orPred.getLeftPred());
    print(Sym.OR);
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
    print(Sym.DECORWORD, parent.getWord());
    return null;
  }

  public Object visitPipeExpr(PipeExpr pipeExpr)
  {
    visit(pipeExpr.getLeftExpr());
    print(Sym.ZPIPE);
    visit(pipeExpr.getRightExpr());
    return null;
  }

  public Object visitPowerExpr(PowerExpr powerExpr)
  {
    print(Sym.POWER);
    visit(powerExpr.getExpr());
    return null;
  }

  public Object visitPowerType(PowerType powerType)
  {
    throw new UnsupportedOperationException("Unexpected term PowerType.");
  }

  public Object visitPreExpr(PreExpr preExpr)
  {
    print(Sym.ZPRE);
    visit(preExpr.getExpr());
    return null;
  }

  public Object visitProdExpr(ProdExpr prodExpr)
  {
    printTermList(prodExpr.getExpr(), Sym.CROSS);
    return null;
  }

  public Object visitProdType(ProdType prodType)
  {
    throw new UnsupportedOperationException("Unexpected term ProdType.");
  }

  public Object visitProjExpr(ProjExpr projExpr)
  {
    visit(projExpr.getLeftExpr());
    print(Sym.ZPROJ);
    visit(projExpr.getRightExpr());
    return null;
  }

  public Object visitRefExpr(RefExpr refExpr)
  {
    if (refExpr.getMixfix().booleanValue()) {
      // TODO: RefExpr with Mixfix == true
      visit(refExpr.getRefName());
      printTermList(refExpr.getExpr());
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
    print(Sym.DECORWORD, refName.getWord());
    visit(refName.getStroke());
    return null;
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
      print(Sym.BAR);
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
    print(Sym.SPOT);
    visit(setCompExpr.getExpr());
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
    print(Sym.THETA);
    visit(thetaExpr.getExpr());
    visit(thetaExpr.getStroke());
    return null;
  }

  public Object visitTruePred(TruePred truePred)
  {
    print(Sym.TRUE);
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
    print(Sym.DOT);
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
    print(Sym.COLON);
    visit(varDecl.getExpr());
    return null;
  }

  public Object visitZSect(ZSect zSect)
  {
    List parents = zSect.getParent();
    print(Sym.ZED);
    print(Sym.SECTION);
    print(Sym.DECORWORD, zSect.getName());
    if (parents.size() > 0) {
      print(Sym.PARENTS);
      visit(zSect.getParent());
    }
    print(Sym.END);
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
      t.accept(this);
    }
  }

  private void printTermList(List list)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      term.accept(this);
      if (iter.hasNext()) {
        print(Sym.COMMA);
      }
    }
  }

  private void printTermList(List list, int separator)
  {
    for (Iterator iter = list.iterator(); iter.hasNext();) {
      Term term = (Term) iter.next();
      term.accept(this);
      if (iter.hasNext()) {
        print(separator);
      }
    }
  }

  private void print(int type)
  {
    printer_.printSymbol(new Symbol(type));
  }

  private void print(int type, Object value)
  {
    printer_.printSymbol(new Symbol(type, value));
  }

  /**
   * A printer that can print Z symbols.
   */
  interface ZPrinter
  {
    void printSymbol(Symbol symbol);
  }
}
