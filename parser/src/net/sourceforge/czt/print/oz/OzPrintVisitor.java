/*
  Copyright (C) 2004, 2005 Petra Malik
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

package net.sourceforge.czt.print.oz;

import java.util.List;

import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;
import net.sourceforge.czt.oz.visitor.*;
import net.sourceforge.czt.print.z.*;

/**
 * An Object-Z visitor used for printing.
 *
 * @author Petra Malik
 */
public class OzPrintVisitor
  extends ZPrintVisitor
  implements OzVisitor
{
  /**
   * Creates a new Object-Z print visitor.
   * The section information should be able to provide information of
   * type <code>net.sourceforge.czt.parser.util.OpTable.class</code>.
   */
  public OzPrintVisitor(ZPrinter printer)
  {
    super(printer);
  }

  public Object visitClassPara(ClassPara classPara)
  {
    throw new UnsupportedOperationException();
  }

  public Object visitVisibilityList(VisibilityList visibilityList)
  {
    if (visibilityList != null) {
      printKeyword(ZString.ZPROJ);
      print(Sym.LPAREN);
      printTermList(visibilityList.getRefName());
      print(Sym.RPAREN);
    }
    return null;
  }

  public Object visitInitialState(InitialState initialState)
  {
    throw new UnsupportedOperationException();
  }

  public Object visitState(State state)
  {
    if (Box.SchBox.equals(state.getBox())) {
      print(net.sourceforge.czt.parser.oz.Sym.STATE);
    }
    else {
      print(Sym.LSQUARE);
    }

    visit(state.getPrimaryDecl());
    visit(state.getSecondaryDecl());
    visit(state.getPred());

    if (Box.SchBox.equals(state.getBox())) {
      print(Sym.END);
    }
    else {
      print(Sym.RSQUARE);
    }
    return null;
  }

  public Object visitPrimaryDecl(PrimaryDecl primaryDecl)
  {
    visit(primaryDecl.getDecl());
    return null;
  }

  public Object visitSecondaryDecl(SecondaryDecl secondaryDecl)
  {
    visit(secondaryDecl.getDecl());
    return null;
  }

  public Object visitOperation(Operation operation)
  {
    throw new UnsupportedOperationException();
  }


  public Object visitOpText(OpText opText)
  {
    visit(opText.getDeltaList());
    visit(opText.getSchText());
    return null;
  }

  public Object visitDeltaList(DeltaList deltaList)
  {
    printKeyword(ZString.DELTA);
    print(Sym.LPAREN);
    printTermList(deltaList.getRefName());
    print(Sym.RPAREN);
    return null;
  }

  public Object visitPredExpr(PredExpr predExpr)
  {
    printLPAREN(predExpr);
    visit(predExpr.getPred());
    printRPAREN(predExpr);
    return null;
  }

  public Object visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    printLPAREN(classUnionExpr);
    visit(classUnionExpr.getLeftExpr());
    printKeyword(OzString.CLASSUNION);
    visit(classUnionExpr.getRightExpr());
    printRPAREN(classUnionExpr);
    return null;
  }

  public Object visitPolyExpr(PolyExpr polyExpr)
  {
    printLPAREN(polyExpr);
    printKeyword(OzString.POLY);
    visit(polyExpr.getExpr());
    printRPAREN(polyExpr);
    return null;
  }

  public Object visitContainmentExpr(ContainmentExpr containmentExpr)
  {
    printLPAREN(containmentExpr);
    visit(containmentExpr.getExpr());
    printKeyword(OzString.CONTAINMENT);
    printRPAREN(containmentExpr);
    return null;
  }

  public Object visitOpPromotionExpr(OpPromotionExpr opPromotionExpr)
  {
    printLPAREN(opPromotionExpr);
    if (opPromotionExpr.getExpr() != null) {
      visit(opPromotionExpr.getExpr());
      printKeyword(ZString.DOT);
    }
    visit(opPromotionExpr.getName());
    printRPAREN(opPromotionExpr);
    return null;
  }

  public Object visitDistConjOpExpr(DistConjOpExpr distConjOpExpr)
  {
    printLPAREN(distConjOpExpr);
    printKeyword(OzString.DCNJ);
    visit(distConjOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distConjOpExpr.getOpExpr());
    printRPAREN(distConjOpExpr);
    return null;
  }

  public Object visitDistSeqOpExpr(DistSeqOpExpr distSeqOpExpr)
  {
    printLPAREN(distSeqOpExpr);
    printKeyword(ZString.ZCOMP);
    visit(distSeqOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distSeqOpExpr.getOpExpr());
    printRPAREN(distSeqOpExpr);
    return null;
  }

  public Object visitDistChoiceOpExpr(DistChoiceOpExpr distChoiceOpExpr)
  {
    printLPAREN(distChoiceOpExpr);
    printKeyword(OzString.DGCH);
    visit(distChoiceOpExpr.getSchText());
    printKeyword(ZString.SPOT);
    visit(distChoiceOpExpr.getOpExpr());
    printRPAREN(distChoiceOpExpr);
    return null;
  }

  public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    printLPAREN(anonOpExpr);
    print(Sym.LSQUARE);
    visit(anonOpExpr.getOpText());
    print(Sym.RSQUARE);
    printRPAREN(anonOpExpr);
    return null;
  }

  public Object visitConjOpExpr(ConjOpExpr conjOpExpr)
  {
    printLPAREN(conjOpExpr);
    visit(conjOpExpr.getLeftOpExpr());
    printKeyword(ZString.AND);
    visit(conjOpExpr.getRightOpExpr());
    printRPAREN(conjOpExpr);
    return null;
  }

  public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    printLPAREN(parallelOpExpr);
    visit(parallelOpExpr.getLeftOpExpr());
    printKeyword(OzString.PARALLEL);
    visit(parallelOpExpr.getRightOpExpr());
    printRPAREN(parallelOpExpr);
    return null;
  }

  public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    printLPAREN(assoParallelOpExpr);
    visit(assoParallelOpExpr.getLeftOpExpr());
    printKeyword(OzString.ASSOPARALLEL);
    visit(assoParallelOpExpr.getRightOpExpr());
    printRPAREN(assoParallelOpExpr);
    return null;
  }

  public Object visitExChoiceOpExpr(ExChoiceOpExpr exChoiceOpExpr)
  {
    printLPAREN(exChoiceOpExpr);
    visit(exChoiceOpExpr.getLeftOpExpr());
    printKeyword(OzString.GCH);
    visit(exChoiceOpExpr.getRightOpExpr());
    printRPAREN(exChoiceOpExpr);
    return null;
  }

  public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    printLPAREN(seqOpExpr);
    visit(seqOpExpr.getLeftOpExpr());
    printKeyword(ZString.ZCOMP);
    visit(seqOpExpr.getRightOpExpr());
    printRPAREN(seqOpExpr);
    return null;
  }

  public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichExpr)
  {
    printLPAREN(scopeEnrichExpr);
    visit(scopeEnrichExpr.getLeftOpExpr());
    printKeyword(ZString.SPOT);
    visit(scopeEnrichExpr.getRightOpExpr());
    printRPAREN(scopeEnrichExpr);
    return null;
  }

  public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    printLPAREN(hideOpExpr);
    visit(hideOpExpr.getOpExpr());
    printKeyword(ZString.ZHIDE);
    print(Sym.LPAREN);
    printTermList(hideOpExpr.getName());
    print(Sym.RPAREN);
    printRPAREN(hideOpExpr);
    return null;
  }

  public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    printLPAREN(renameOpExpr);
    visit(renameOpExpr.getOpExpr());
    print(Sym.LSQUARE);
    printTermList(renameOpExpr.getNewOldPair());
    print(Sym.RSQUARE);
    printRPAREN(renameOpExpr);
    return null;
  }

  public Object visitClassRefType(ClassRefType classRefType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRefType.");
  }

  public Object visitClassPolyType(ClassPolyType classPolyType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassPolyType.");
  }

  public Object visitClassUnionType(ClassUnionType classUnionType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassUnionType.");
  }

  public Object visitClassRef(ClassRef classRef)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRef.");
  }

  public Object visitNameSignaturePair(NameSignaturePair nameSignaturePair)
  {
    throw new UnsupportedOperationException("Unexpected term NameSignaturePair.");
  }

  public Object visitClassSig(ClassSig classSig)
  {
    throw new UnsupportedOperationException("Unexpected term ClassSig.");
  }

  protected void printLPAREN(TermA termA)
  {
    final boolean braces = termA.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.LPAREN);
  }

  protected void printRPAREN(TermA termA)
  {
    final boolean braces = termA.getAnn(ParenAnn.class) != null;
    if (braces) print(Sym.RPAREN);
  }
}
