
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

Copyright 2003 Mark Utting
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

package net.sourceforge.czt.oz.impl;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.oz.ast.*;

/**
 * <p>An implementation of the object factory for constructing
 * concrete Z terms.  Each factory method returns an instance
 * of the corresponding class provided in this package.</p>
 *
 * @author Gnast version 0.1
 */
public class OzFactoryImpl
  extends net.sourceforge.czt.z.impl.ZFactoryImpl
  implements net.sourceforge.czt.oz.ast.OzFactory
{
  public RefNameList createRefNameList()
  {
    RefNameList zedObject = new RefNameListImpl();
    return zedObject;
  }

  public RefNameList createRefNameList(java.util.List name)
  {
    RefNameList zedObject = createRefNameList();
    if (name != null) {
      zedObject.getName().addAll(name);
    }
    return zedObject;
  }

  public PromotedAttrExpr createPromotedAttrExpr()
  {
    PromotedAttrExpr zedObject = new PromotedAttrExprImpl();
    return zedObject;
  }

  public PromotedAttrExpr createPromotedAttrExpr(Expr expr, net.sourceforge.czt.z.ast.RefName refName)
  {
    PromotedAttrExpr zedObject = createPromotedAttrExpr();
    zedObject.setExpr(expr);
    zedObject.setRefName(refName);
    return zedObject;
  }

  public RenameList createRenameList()
  {
    RenameList zedObject = new RenameListImpl();
    return zedObject;
  }

  public RenameList createRenameList(java.util.List nameNamePair)
  {
    RenameList zedObject = createRenameList();
    if (nameNamePair != null) {
      zedObject.getNameNamePair().addAll(nameNamePair);
    }
    return zedObject;
  }

  public ActualParameters createActualParameters()
  {
    ActualParameters zedObject = new ActualParametersImpl();
    return zedObject;
  }

  public ActualParameters createActualParameters(java.util.List expr)
  {
    ActualParameters zedObject = createActualParameters();
    if (expr != null) {
      zedObject.getExpr().addAll(expr);
    }
    return zedObject;
  }

  public DistConjOpExpr createDistConjOpExpr()
  {
    DistConjOpExpr zedObject = new DistConjOpExprImpl();
    return zedObject;
  }

  public DistConjOpExpr createDistConjOpExpr(MainOpExpr mainOpExpr)
  {
    DistConjOpExpr zedObject = createDistConjOpExpr();
    zedObject.setMainOpExpr(mainOpExpr);
    return zedObject;
  }

  public BasicOpExpr createBasicOpExpr()
  {
    BasicOpExpr zedObject = new BasicOpExprImpl();
    return zedObject;
  }

  public BasicOpExpr createBasicOpExpr(RefNameList deltaList, net.sourceforge.czt.z.ast.SchText schText)
  {
    BasicOpExpr zedObject = createBasicOpExpr();
    zedObject.setDeltaList(deltaList);
    zedObject.setSchText(schText);
    return zedObject;
  }

  public MainOpExpr createMainOpExpr()
  {
    MainOpExpr zedObject = new MainOpExprImpl();
    return zedObject;
  }

  public MainOpExpr createMainOpExpr(net.sourceforge.czt.z.ast.SchText schText, OperationExpr operationExpr)
  {
    MainOpExpr zedObject = createMainOpExpr();
    zedObject.setSchText(schText);
    zedObject.setOperationExpr(operationExpr);
    return zedObject;
  }

  public PolyExpr createPolyExpr()
  {
    PolyExpr zedObject = new PolyExprImpl();
    return zedObject;
  }

  public PolyExpr createPolyExpr(Expr expr)
  {
    PolyExpr zedObject = createPolyExpr();
    zedObject.setExpr(expr);
    return zedObject;
  }

  public HideOpExpr createHideOpExpr()
  {
    HideOpExpr zedObject = new HideOpExprImpl();
    return zedObject;
  }

  public HideOpExpr createHideOpExpr(OperationExpr operationExpr, java.util.List hideName)
  {
    HideOpExpr zedObject = createHideOpExpr();
    zedObject.setOperationExpr(operationExpr);
    if (hideName != null) {
      zedObject.getHideName().addAll(hideName);
    }
    return zedObject;
  }

  public SeqOpExpr createSeqOpExpr()
  {
    SeqOpExpr zedObject = new SeqOpExprImpl();
    return zedObject;
  }

  public SeqOpExpr createSeqOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    SeqOpExpr zedObject = createSeqOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public SelfExpr createSelfExpr()
  {
    SelfExpr zedObject = new SelfExprImpl();
    return zedObject;
  }

  public InheritedClass createInheritedClass()
  {
    InheritedClass zedObject = new InheritedClassImpl();
    return zedObject;
  }

  public InheritedClass createInheritedClass(net.sourceforge.czt.z.ast.RefName name, ActualParameters actualParameters, RenameList renameList)
  {
    InheritedClass zedObject = createInheritedClass();
    zedObject.setName(name);
    zedObject.setActualParameters(actualParameters);
    zedObject.setRenameList(renameList);
    return zedObject;
  }

  public DistChoiceOpExpr createDistChoiceOpExpr()
  {
    DistChoiceOpExpr zedObject = new DistChoiceOpExprImpl();
    return zedObject;
  }

  public DistChoiceOpExpr createDistChoiceOpExpr(MainOpExpr mainOpExpr)
  {
    DistChoiceOpExpr zedObject = createDistChoiceOpExpr();
    zedObject.setMainOpExpr(mainOpExpr);
    return zedObject;
  }

  public AssoParallelOpExpr createAssoParallelOpExpr()
  {
    AssoParallelOpExpr zedObject = new AssoParallelOpExprImpl();
    return zedObject;
  }

  public AssoParallelOpExpr createAssoParallelOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    AssoParallelOpExpr zedObject = createAssoParallelOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public State createState()
  {
    State zedObject = new StateImpl();
    return zedObject;
  }

  public State createState(java.util.List decl, SecondaryAttributes secondaryAttributes, java.util.List pred)
  {
    State zedObject = createState();
    if (decl != null) {
      zedObject.getDecl().addAll(decl);
    }
    zedObject.setSecondaryAttributes(secondaryAttributes);
    if (pred != null) {
      zedObject.getPred().addAll(pred);
    }
    return zedObject;
  }

  public PromotedInitPred createPromotedInitPred()
  {
    PromotedInitPred zedObject = new PromotedInitPredImpl();
    return zedObject;
  }

  public PromotedInitPred createPromotedInitPred(net.sourceforge.czt.z.ast.Expr expr)
  {
    PromotedInitPred zedObject = createPromotedInitPred();
    zedObject.setExpr(expr);
    return zedObject;
  }

  public OpPromotionExpr createOpPromotionExpr()
  {
    OpPromotionExpr zedObject = new OpPromotionExprImpl();
    return zedObject;
  }

  public OpPromotionExpr createOpPromotionExpr(net.sourceforge.czt.z.ast.Expr expr, net.sourceforge.czt.z.ast.RefName opName)
  {
    OpPromotionExpr zedObject = createOpPromotionExpr();
    zedObject.setExpr(expr);
    zedObject.setOpName(opName);
    return zedObject;
  }

  public ConjOpExpr createConjOpExpr()
  {
    ConjOpExpr zedObject = new ConjOpExprImpl();
    return zedObject;
  }

  public ConjOpExpr createConjOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    ConjOpExpr zedObject = createConjOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public ClassPara createClassPara()
  {
    ClassPara zedObject = new ClassParaImpl();
    return zedObject;
  }

  public ClassPara createClassPara(net.sourceforge.czt.z.ast.DeclName name, FormalParameters formalParameters, RefNameList visibilityList, java.util.List inheritedClass, LocalDef localDef, State state, InitialState initialState, java.util.List operation)
  {
    ClassPara zedObject = createClassPara();
    zedObject.setName(name);
    zedObject.setFormalParameters(formalParameters);
    zedObject.setVisibilityList(visibilityList);
    if (inheritedClass != null) {
      zedObject.getInheritedClass().addAll(inheritedClass);
    }
    zedObject.setLocalDef(localDef);
    zedObject.setState(state);
    zedObject.setInitialState(initialState);
    if (operation != null) {
      zedObject.getOperation().addAll(operation);
    }
    return zedObject;
  }

  public ParenOpExpr createParenOpExpr()
  {
    ParenOpExpr zedObject = new ParenOpExprImpl();
    return zedObject;
  }

  public Operation createOperation()
  {
    Operation zedObject = new OperationImpl();
    return zedObject;
  }

  public Operation createOperation(net.sourceforge.czt.z.ast.DeclName name, OperationBoxExpr operationBoxExpr)
  {
    Operation zedObject = createOperation();
    zedObject.setName(name);
    zedObject.setOperationBoxExpr(operationBoxExpr);
    return zedObject;
  }

  public LocalDef createLocalDef()
  {
    LocalDef zedObject = new LocalDefImpl();
    return zedObject;
  }

  public LocalDef createLocalDef(java.util.List givenPara, java.util.List axPara, java.util.List freePara)
  {
    LocalDef zedObject = createLocalDef();
    if (givenPara != null) {
      zedObject.getGivenPara().addAll(givenPara);
    }
    if (axPara != null) {
      zedObject.getAxPara().addAll(axPara);
    }
    if (freePara != null) {
      zedObject.getFreePara().addAll(freePara);
    }
    return zedObject;
  }

  public ContainmentExpr createContainmentExpr()
  {
    ContainmentExpr zedObject = new ContainmentExprImpl();
    return zedObject;
  }

  public ContainmentExpr createContainmentExpr(Expr expr)
  {
    ContainmentExpr zedObject = createContainmentExpr();
    zedObject.setExpr(expr);
    return zedObject;
  }

  public InitialState createInitialState()
  {
    InitialState zedObject = new InitialStateImpl();
    return zedObject;
  }

  public InitialState createInitialState(java.util.List pred)
  {
    InitialState zedObject = createInitialState();
    if (pred != null) {
      zedObject.getPred().addAll(pred);
    }
    return zedObject;
  }

  public OperationBox createOperationBox()
  {
    OperationBox zedObject = new OperationBoxImpl();
    return zedObject;
  }

  public OperationBox createOperationBox(RefNameList deltaList, java.util.List decl, java.util.List pred)
  {
    OperationBox zedObject = createOperationBox();
    zedObject.setDeltaList(deltaList);
    if (decl != null) {
      zedObject.getDecl().addAll(decl);
    }
    if (pred != null) {
      zedObject.getPred().addAll(pred);
    }
    return zedObject;
  }

  public DistSeqOpExpr createDistSeqOpExpr()
  {
    DistSeqOpExpr zedObject = new DistSeqOpExprImpl();
    return zedObject;
  }

  public DistSeqOpExpr createDistSeqOpExpr(MainOpExpr mainOpExpr)
  {
    DistSeqOpExpr zedObject = createDistSeqOpExpr();
    zedObject.setMainOpExpr(mainOpExpr);
    return zedObject;
  }

  public ScopeEnrichOpExpr createScopeEnrichOpExpr()
  {
    ScopeEnrichOpExpr zedObject = new ScopeEnrichOpExprImpl();
    return zedObject;
  }

  public ScopeEnrichOpExpr createScopeEnrichOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    ScopeEnrichOpExpr zedObject = createScopeEnrichOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public SecondaryAttributes createSecondaryAttributes()
  {
    SecondaryAttributes zedObject = new SecondaryAttributesImpl();
    return zedObject;
  }

  public SecondaryAttributes createSecondaryAttributes(java.util.List varDecl)
  {
    SecondaryAttributes zedObject = createSecondaryAttributes();
    if (varDecl != null) {
      zedObject.getVarDecl().addAll(varDecl);
    }
    return zedObject;
  }

  public RenameOpExpr createRenameOpExpr()
  {
    RenameOpExpr zedObject = new RenameOpExprImpl();
    return zedObject;
  }

  public RenameOpExpr createRenameOpExpr(OperationExpr operationExpr, java.util.List nameNamePair)
  {
    RenameOpExpr zedObject = createRenameOpExpr();
    zedObject.setOperationExpr(operationExpr);
    if (nameNamePair != null) {
      zedObject.getNameNamePair().addAll(nameNamePair);
    }
    return zedObject;
  }

  public ExChoiceOpExpr createExChoiceOpExpr()
  {
    ExChoiceOpExpr zedObject = new ExChoiceOpExprImpl();
    return zedObject;
  }

  public ExChoiceOpExpr createExChoiceOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    ExChoiceOpExpr zedObject = createExChoiceOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public ParallelOpExpr createParallelOpExpr()
  {
    ParallelOpExpr zedObject = new ParallelOpExprImpl();
    return zedObject;
  }

  public ParallelOpExpr createParallelOpExpr(OperationExpr leftOperationExpr, OperationExpr rightOperationExpr)
  {
    ParallelOpExpr zedObject = createParallelOpExpr();
    zedObject.setLeftOperationExpr(leftOperationExpr);
    zedObject.setRightOperationExpr(rightOperationExpr);
    return zedObject;
  }

  public FormalParameters createFormalParameters()
  {
    FormalParameters zedObject = new FormalParametersImpl();
    return zedObject;
  }

  public FormalParameters createFormalParameters(java.util.List name)
  {
    FormalParameters zedObject = createFormalParameters();
    if (name != null) {
      zedObject.getName().addAll(name);
    }
    return zedObject;
  }

}
