/*
  Copyright (C) 2004, 2005, 2006, 2007 Petra Malik, Tim Miller
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

import java.util.Iterator;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.oz.ast.AnonOpExpr;
import net.sourceforge.czt.oz.ast.AssoParallelOpExpr;
import net.sourceforge.czt.oz.ast.ClassPara;
import net.sourceforge.czt.oz.ast.ClassPolyType;
import net.sourceforge.czt.oz.ast.ClassRef;
import net.sourceforge.czt.oz.ast.ClassRefList;
import net.sourceforge.czt.oz.ast.ClassRefType;
import net.sourceforge.czt.oz.ast.ClassUnionExpr;
import net.sourceforge.czt.oz.ast.ClassUnionType;
import net.sourceforge.czt.oz.ast.ConjOpExpr;
import net.sourceforge.czt.oz.ast.ContainmentExpr;
import net.sourceforge.czt.oz.ast.DeltaList;
import net.sourceforge.czt.oz.ast.DistChoiceOpExpr;
import net.sourceforge.czt.oz.ast.DistConjOpExpr;
import net.sourceforge.czt.oz.ast.DistSeqOpExpr;
import net.sourceforge.czt.oz.ast.ExChoiceOpExpr;
import net.sourceforge.czt.oz.ast.HideOpExpr;
import net.sourceforge.czt.oz.ast.InitialState;
import net.sourceforge.czt.oz.ast.NameSignaturePair;
import net.sourceforge.czt.oz.ast.OpPromotionExpr;
import net.sourceforge.czt.oz.ast.OpText;
import net.sourceforge.czt.oz.ast.Operation;
import net.sourceforge.czt.oz.ast.ParallelOpExpr;
import net.sourceforge.czt.oz.ast.PolyExpr;
import net.sourceforge.czt.oz.ast.PredExpr;
import net.sourceforge.czt.oz.ast.PrimaryDecl;
import net.sourceforge.czt.oz.ast.RenameOpExpr;
import net.sourceforge.czt.oz.ast.ScopeEnrichOpExpr;
import net.sourceforge.czt.oz.ast.SecondaryDecl;
import net.sourceforge.czt.oz.ast.SeqOpExpr;
import net.sourceforge.czt.oz.ast.State;
import net.sourceforge.czt.oz.ast.VisibilityList;
import net.sourceforge.czt.oz.util.OzString;
import net.sourceforge.czt.oz.visitor.OzVisitor;
import net.sourceforge.czt.parser.oz.OzToken;
import net.sourceforge.czt.parser.z.ZKeyword;
import net.sourceforge.czt.parser.z.ZToken;
import net.sourceforge.czt.print.z.WhereWord;
import net.sourceforge.czt.print.z.ZPrinter;
import net.sourceforge.czt.session.SectionInfo;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.DeclList;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.ParenAnn;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.ZString;

/**
 * An Object-Z visitor used for printing.
 *
 * @author Petra Malik, Tim Miller
 */
public class OzPrintVisitor
  extends net.sourceforge.czt.print.z.ZPrintVisitor
  implements OzVisitor<Object>
{
  /**
   * Creates a new Object-Z print visitor.
   */
  public OzPrintVisitor(SectionInfo si, ZPrinter printer)
  {
    super(si, printer);
  }

  public OzPrintVisitor(SectionInfo si, ZPrinter printer, Properties props)
  {
    super(si, printer, props);
  }

  @Override
public Object visitClassPara(ClassPara classPara)
  {
    //print the header information
    ref_ = false;
    if (((ZNameList)classPara.getNameList()).size() == 0) {
      print(OzToken.CLASS);
      visit(classPara.getName());
    }
    else {
      print(OzToken.GENCLASS);
      visit(classPara.getName());
      print(ZToken.LSQUARE);
      printTermList((ZNameList)classPara.getNameList());
      print(ZToken.RSQUARE);
    }
    print(ZToken.NL);

    visit(classPara.getVisibilityList());

    //visit each inherited class, putting a NL between them
    if (classPara.getInheritedClass() instanceof ZExprList) {
      ZExprList inheritedClass = (ZExprList) classPara.getInheritedClass();
      for (Expr expr : inheritedClass) {
        visit(expr);
        print(ZToken.NL);
      }
    }
    else {
      throw new
        UnsupportedOperationException("Non-ZExprList as Inherited Class");
    }

    //visit each inner paragraph, putting a NL between them
    for (Para para : classPara.getLocalDef()) {
      if (para instanceof AxPara) {
        AxPara axPara = (AxPara) para;
        visitInnerAxPara(axPara);
      }
      else if (para instanceof FreePara) {
        FreePara freePara = (FreePara) para;
        visitInnerFreePara(freePara);
      }
      else {
        visit(para);
        print(ZToken.NL);
      }
    }

    //visit the state and inital predicate
    visit(classPara.getState());
    visit(classPara.getInitialState());

    //visit each operation, putting a NL between them
    for (Iterator<Operation> iter = classPara.getOperation().iterator();
         iter.hasNext(); ) {
      Operation operation = iter.next();
      visit(operation);
      if (iter.hasNext()) {
        print(ZToken.NL);
      }
    }
    print(ZToken.END);
    return null;
  }

  protected Object visitInnerAxPara(AxPara axPara)
  {
    Box box = axPara.getBox();
    if (Box.OmitBox.equals(box)) {
      visit(axPara.getSchText());
    }
    else {
      assert false : "Inner AxPara with OmitBox";
    }
    return null;
  }

  protected Object visitInnerFreePara(FreePara freePara)
  {
    visit(freePara.getFreetypeList());
    print(ZToken.NL);
    return null;
  }

  @Override
public Object visitVisibilityList(VisibilityList visibilityList)
  {
    if (visibilityList != null) {
      print(ZKeyword.ZPROJ);
      print(ZToken.LPAREN);
      printTermList(visibilityList.getZName());
      print(ZToken.RPAREN);
      print(ZToken.NL);
    }
    return null;
  }

  @Override
public Object visitInitialState(InitialState initialState)
  {
    if (initialState != null) {
      boolean isBox = Box.SchBox.equals(initialState.getBox());
      if (isBox) {
        print(OzToken.INIT);
        print(ZToken.NL);
        visit(initialState.getPred());
        print(ZToken.END);
      }
      else {
        printDecorword(OzString.INITWORD + ZString.SPACE +
                       OzString.SDEF + ZString.SPACE);
        print(ZToken.LSQUARE);
        visit(initialState.getPred());
        print(ZToken.RSQUARE);
      }
      print(ZToken.NL);
    }
    return null;
  }

  @Override
public Object visitState(State state)
  {
    if (state != null) {
      boolean isBox = Box.SchBox.equals(state.getBox());
      if (isBox) {
        print(OzToken.STATE);
        print(ZToken.NL);
      }
      else {
        print(ZToken.LSQUARE);
      }

      DeclList pDeclList = state.getPrimaryDecl().getDeclList();
      if (pDeclList instanceof ZDeclList) {
        ZDeclList zDeclList = (ZDeclList) pDeclList;
        if (zDeclList.size() > 0) {
          visit(state.getPrimaryDecl());
        }
      }
      else {
        throw new
          UnsupportedOperationException("Non-ZDeclList in PrimaryDecl");
      }

      DeclList sDeclList = state.getSecondaryDecl().getDeclList();
      if (sDeclList instanceof ZDeclList) {
        ZDeclList zDeclList = (ZDeclList) sDeclList;
        if (zDeclList.size() > 0) {
          print(ZToken.NL);
          printDecorword(OzString.DELTA);
          print(ZToken.NL);
          visit(state.getSecondaryDecl());
        }
      }
      else {
        throw new
          UnsupportedOperationException("Non-ZDeclList in SecondayDecl");
      }

      if (state.getPred() != null) {
        if (isBox) {
          print(ZToken.DECORWORD, new WhereWord());
          visit(state.getPred());
        }
        else {
          print(ZKeyword.BAR);
          visit(state.getPred());
          print(ZToken.RSQUARE);
        }
      }

      if (isBox) {
        print(ZToken.END);
      }
      print(ZToken.NL);
    }
    return null;
  }

  @Override
public Object visitPrimaryDecl(PrimaryDecl primaryDecl)
  {
    visit(primaryDecl.getDeclList());
    return null;
  }

  @Override
public Object visitSecondaryDecl(SecondaryDecl secondaryDecl)
  {
    visit(secondaryDecl.getDeclList());
    return null;
  }

  @Override
public Object visitOperation(Operation operation)
  {
    boolean isBox = Box.SchBox.equals(operation.getBox());
    if (isBox) {
      print(OzToken.OPSCH);
      visit(operation.getName());
      print(ZToken.NL);

      assert operation.getOpExpr() instanceof AnonOpExpr;
      AnonOpExpr anonOpExpr = (AnonOpExpr) operation.getOpExpr();
      OpText opText = anonOpExpr.getOpText();

      visit(opText.getDeltaList());

      if (opText.getSchText() instanceof ZSchText) {
        ZSchText zSchText = (ZSchText) opText.getSchText();
        visit(zSchText.getDeclList());
        if (zSchText.getPred() != null) {
          print(ZToken.DECORWORD, new WhereWord());
          visit(zSchText.getPred());
        }
      }
      else {
        throw new UnsupportedOperationException("Non-ZSchText in Operation");
      }
      print(ZToken.END);
    }
    else {
      visit(operation.getName());
      print(OzToken.SDEF);
      visit(operation.getOpExpr());
    }
    return null;
  }

  @Override
public Object visitOpText(OpText opText)
  {
    visit(opText.getDeltaList());
    visit(opText.getSchText());
    return null;
  }

  @Override
public Object visitDeltaList(DeltaList deltaList)
  {
    printDecorword(OzString.DELTA);
    print(ZToken.LPAREN);
    ref_ = true;
    printTermList(deltaList.getName());
    print(ZToken.RPAREN);
    print(ZToken.NL);
    return null;
  }

  @Override
public Object visitPredExpr(PredExpr predExpr)
  {
    printLPAREN(predExpr);
    visit(predExpr.getPred());
    printRPAREN(predExpr);
    return null;
  }

  @Override
public Object visitClassUnionExpr(ClassUnionExpr classUnionExpr)
  {
    printLPAREN(classUnionExpr);
    printTermList(classUnionExpr.getExpr(), OzString.CLASSUNION);
    printRPAREN(classUnionExpr);
    return null;
  }

  @Override
public Object visitPolyExpr(PolyExpr polyExpr)
  {
    printLPAREN(polyExpr);
    printDecorword(OzString.POLY);
    visit(polyExpr.getExpr());
    printRPAREN(polyExpr);
    return null;
  }

  @Override
public Object visitContainmentExpr(ContainmentExpr containmentExpr)
  {
    printLPAREN(containmentExpr);
    visit(containmentExpr.getExpr());
    printDecorword(OzString.CONTAINMENT);
    printRPAREN(containmentExpr);
    return null;
  }

  @Override
public Object visitOpPromotionExpr(OpPromotionExpr opPromotionExpr)
  {
    printLPAREN(opPromotionExpr);
    if (opPromotionExpr.getExpr() != null) {
      visit(opPromotionExpr.getExpr());
      print(ZKeyword.DOT);
    }
    ref_ = true;
    visit(opPromotionExpr.getName());
    printRPAREN(opPromotionExpr);
    return null;
  }

  @Override
public Object visitDistConjOpExpr(DistConjOpExpr distConjOpExpr)
  {
    printLPAREN(distConjOpExpr);
    printDecorword(OzString.DCNJ);
    visit(distConjOpExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(distConjOpExpr.getOpExpr());
    printRPAREN(distConjOpExpr);
    return null;
  }

  @Override
public Object visitDistSeqOpExpr(DistSeqOpExpr distSeqOpExpr)
  {
    printLPAREN(distSeqOpExpr);
    print(ZKeyword.ZCOMP);
    visit(distSeqOpExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(distSeqOpExpr.getOpExpr());
    printRPAREN(distSeqOpExpr);
    return null;
  }

  @Override
public Object visitDistChoiceOpExpr(DistChoiceOpExpr distChoiceOpExpr)
  {
    printLPAREN(distChoiceOpExpr);
    printDecorword(OzString.DGCH);
    visit(distChoiceOpExpr.getSchText());
    print(ZKeyword.SPOT);
    visit(distChoiceOpExpr.getOpExpr());
    printRPAREN(distChoiceOpExpr);
    return null;
  }

  @Override
public Object visitAnonOpExpr(AnonOpExpr anonOpExpr)
  {
    printLPAREN(anonOpExpr);
    print(ZToken.LSQUARE);
    visit(anonOpExpr.getOpText());
    print(ZToken.RSQUARE);
    printRPAREN(anonOpExpr);
    return null;
  }

  @Override
public Object visitConjOpExpr(ConjOpExpr conjOpExpr)
  {
    printLPAREN(conjOpExpr);
    printTermList(conjOpExpr.getOpExpr(), ZKeyword.AND);
    printRPAREN(conjOpExpr);
    return null;
  }

  @Override
public Object visitParallelOpExpr(ParallelOpExpr parallelOpExpr)
  {
    printLPAREN(parallelOpExpr);
    printTermList(parallelOpExpr.getOpExpr(), OzString.PARALLEL);
    printRPAREN(parallelOpExpr);
    return null;
  }

  @Override
public Object visitAssoParallelOpExpr(AssoParallelOpExpr assoParallelOpExpr)
  {
    printLPAREN(assoParallelOpExpr);
    printTermList(assoParallelOpExpr.getOpExpr(), OzString.ASSOPARALLEL);
    printRPAREN(assoParallelOpExpr);
    return null;
  }

  @Override
public Object visitExChoiceOpExpr(ExChoiceOpExpr exChoiceOpExpr)
  {
    printLPAREN(exChoiceOpExpr);
    printTermList(exChoiceOpExpr.getOpExpr(), OzString.GCH);
    printRPAREN(exChoiceOpExpr);
    return null;
  }

  @Override
public Object visitSeqOpExpr(SeqOpExpr seqOpExpr)
  {
    printLPAREN(seqOpExpr);
    printTermList(seqOpExpr.getOpExpr(), ZKeyword.ZCOMP);
    printRPAREN(seqOpExpr);
    return null;
  }

  @Override
public Object visitScopeEnrichOpExpr(ScopeEnrichOpExpr scopeEnrichExpr)
  {
    printLPAREN(scopeEnrichExpr);
    printTermList(scopeEnrichExpr.getOpExpr(), ZKeyword.SPOT);
    printRPAREN(scopeEnrichExpr);
    return null;
  }

  @Override
public Object visitHideOpExpr(HideOpExpr hideOpExpr)
  {
    printLPAREN(hideOpExpr);
    visit(hideOpExpr.getOpExpr());
    print(ZKeyword.ZHIDE);
    print(ZToken.LPAREN);
    ref_ = true;
    visit(hideOpExpr.getNameList());
    print(ZToken.RPAREN);
    printRPAREN(hideOpExpr);
    return null;
  }

  @Override
public Object visitRenameOpExpr(RenameOpExpr renameOpExpr)
  {
    printLPAREN(renameOpExpr);
    visit(renameOpExpr.getOpExpr());
    print(ZToken.LSQUARE);
    visit(renameOpExpr.getRenameList());
    print(ZToken.RSQUARE);
    printRPAREN(renameOpExpr);
    return null;
  }

  @Override
public Object visitClassRefType(ClassRefType classRefType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRefType.");
  }

  @Override
public Object visitClassPolyType(ClassPolyType classPolyType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassPolyType.");
  }

  @Override
public Object visitClassUnionType(ClassUnionType classUnionType)
  {
    throw new UnsupportedOperationException("Unexpected term ClassUnionType.");
  }

  @Override
public Object visitClassRef(ClassRef classRef)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRef.");
  }

  @Override
public Object visitClassRefList(ClassRefList classRefList)
  {
    throw new UnsupportedOperationException("Unexpected term ClassRefList.");
  }

  @Override
public Object visitNameSignaturePair(NameSignaturePair nameSignaturePair)
  {
    throw new UnsupportedOperationException("Unexpected term NameSignaturePair.");
  }

  @Override
protected void printLPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.LPAREN);
  }

  @Override
protected void printRPAREN(Term term)
  {
    final boolean braces = term.getAnn(ParenAnn.class) != null;
    if (braces) print(ZToken.RPAREN);
  }
}
