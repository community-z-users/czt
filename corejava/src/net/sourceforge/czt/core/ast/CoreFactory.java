
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

package net.sourceforge.czt.core.ast;

/**
 * <p>The object factory for the AST. 
 * This interface contains factory methods
 * for each concrete Z term.</p>
 *
 * <p>This object factory allows the programmer to programatically
 * construct new instances of concrete Z terms.
 * There is usually a factory method that does not require arguments
 * (called default factory method)
 * and a factory method where all the children (except annotations)
 * of that particular Z term can be provided.
 * However, there is no default factory method for immutable Z terms
 * like {@link net.sourceforge.czt.core.ast.RefName}.</p>
 *
 * @author Gnast version 0.1
 */
public interface CoreFactory
{
    /**
     * Creates an instance of {@link Freetype} with the given children.
     *
     * @return the new instance of Freetype.
     */
    public Freetype createFreetype(DeclName declName, java.util.List branch);

    /**
     * Creates an instance of {@link Exists1Expr}.
     *
     * @return the new instance of Exists1Expr.
     */
    public Exists1Expr createExists1Expr();

    /**
     * Creates an instance of {@link Exists1Expr} with the given children.
     *
     * @return the new instance of Exists1Expr.
     */
    public Exists1Expr createExists1Expr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link ParenAnn}.
     *
     * @return the new instance of ParenAnn.
     */
    public ParenAnn createParenAnn();

    /**
     * Creates an instance of {@link NameNamePair}.
     *
     * @return the new instance of NameNamePair.
     */
    public NameNamePair createNameNamePair();

    /**
     * Creates an instance of {@link NameNamePair} with the given children.
     *
     * @return the new instance of NameNamePair.
     */
    public NameNamePair createNameNamePair(RefName oldName, DeclName newName);

    /**
     * Creates an instance of {@link ApplExpr}.
     *
     * @return the new instance of ApplExpr.
     */
    public ApplExpr createApplExpr();

    /**
     * Creates an instance of {@link ApplExpr} with the given children.
     *
     * @return the new instance of ApplExpr.
     */
    public ApplExpr createApplExpr(Boolean mixfix, Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link LetExpr}.
     *
     * @return the new instance of LetExpr.
     */
    public LetExpr createLetExpr();

    /**
     * Creates an instance of {@link LetExpr} with the given children.
     *
     * @return the new instance of LetExpr.
     */
    public LetExpr createLetExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link Signature}.
     *
     * @return the new instance of Signature.
     */
    public Signature createSignature();

    /**
     * Creates an instance of {@link Signature} with the given children.
     *
     * @return the new instance of Signature.
     */
    public Signature createSignature(java.util.List nameTypePair);

    /**
     * Creates an instance of {@link ConstDecl} with the given children.
     *
     * @return the new instance of ConstDecl.
     */
    public ConstDecl createConstDecl(DeclName declName, Expr expr);

    /**
     * Creates an instance of {@link NextStroke}.
     *
     * @return the new instance of NextStroke.
     */
    public NextStroke createNextStroke();

    /**
     * Creates an instance of {@link InStroke}.
     *
     * @return the new instance of InStroke.
     */
    public InStroke createInStroke();

    /**
     * Creates an instance of {@link RefName}.
     *
     * @return the new instance of RefName.
     */
    public RefName createRefName();

    /**
     * Creates an instance of {@link RefName} with the given children.
     *
     * @return the new instance of RefName.
     */
    public RefName createRefName(DeclName decl, String word, java.util.List stroke);

    /**
     * Creates an instance of {@link MemPred}.
     *
     * @return the new instance of MemPred.
     */
    public MemPred createMemPred();

    /**
     * Creates an instance of {@link MemPred} with the given children.
     *
     * @return the new instance of MemPred.
     */
    public MemPred createMemPred(Expr leftExpr, Expr rightExpr, Boolean mixfix);

    /**
     * Creates an instance of {@link ProdType}.
     *
     * @return the new instance of ProdType.
     */
    public ProdType createProdType();

    /**
     * Creates an instance of {@link ProdType} with the given children.
     *
     * @return the new instance of ProdType.
     */
    public ProdType createProdType(java.util.List type);

    /**
     * Creates an instance of {@link ImpliesExpr}.
     *
     * @return the new instance of ImpliesExpr.
     */
    public ImpliesExpr createImpliesExpr();

    /**
     * Creates an instance of {@link ImpliesExpr} with the given children.
     *
     * @return the new instance of ImpliesExpr.
     */
    public ImpliesExpr createImpliesExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link MuExpr}.
     *
     * @return the new instance of MuExpr.
     */
    public MuExpr createMuExpr();

    /**
     * Creates an instance of {@link MuExpr} with the given children.
     *
     * @return the new instance of MuExpr.
     */
    public MuExpr createMuExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link OrPred}.
     *
     * @return the new instance of OrPred.
     */
    public OrPred createOrPred();

    /**
     * Creates an instance of {@link OrPred} with the given children.
     *
     * @return the new instance of OrPred.
     */
    public OrPred createOrPred(Pred leftPred, Pred rightPred);

    /**
     * Creates an instance of {@link ExistsExpr}.
     *
     * @return the new instance of ExistsExpr.
     */
    public ExistsExpr createExistsExpr();

    /**
     * Creates an instance of {@link ExistsExpr} with the given children.
     *
     * @return the new instance of ExistsExpr.
     */
    public ExistsExpr createExistsExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link VarDecl} with the given children.
     *
     * @return the new instance of VarDecl.
     */
    public VarDecl createVarDecl(java.util.List declName, Expr expr);

    /**
     * Creates an instance of {@link NarrSect}.
     *
     * @return the new instance of NarrSect.
     */
    public NarrSect createNarrSect();

    /**
     * Creates an instance of {@link NarrSect} with the given children.
     *
     * @return the new instance of NarrSect.
     */
    public NarrSect createNarrSect(java.util.List content);

    /**
     * Creates an instance of {@link FreePara}.
     *
     * @return the new instance of FreePara.
     */
    public FreePara createFreePara();

    /**
     * Creates an instance of {@link FreePara} with the given children.
     *
     * @return the new instance of FreePara.
     */
    public FreePara createFreePara(java.util.List freetype);

    /**
     * Creates an instance of {@link CompExpr}.
     *
     * @return the new instance of CompExpr.
     */
    public CompExpr createCompExpr();

    /**
     * Creates an instance of {@link CompExpr} with the given children.
     *
     * @return the new instance of CompExpr.
     */
    public CompExpr createCompExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link BindExpr}.
     *
     * @return the new instance of BindExpr.
     */
    public BindExpr createBindExpr();

    /**
     * Creates an instance of {@link BindExpr} with the given children.
     *
     * @return the new instance of BindExpr.
     */
    public BindExpr createBindExpr(java.util.List nameExprPair);

    /**
     * Creates an instance of {@link CondExpr}.
     *
     * @return the new instance of CondExpr.
     */
    public CondExpr createCondExpr();

    /**
     * Creates an instance of {@link CondExpr} with the given children.
     *
     * @return the new instance of CondExpr.
     */
    public CondExpr createCondExpr(Pred pred, Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link ForallExpr}.
     *
     * @return the new instance of ForallExpr.
     */
    public ForallExpr createForallExpr();

    /**
     * Creates an instance of {@link ForallExpr} with the given children.
     *
     * @return the new instance of ForallExpr.
     */
    public ForallExpr createForallExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link NarrPara}.
     *
     * @return the new instance of NarrPara.
     */
    public NarrPara createNarrPara();

    /**
     * Creates an instance of {@link NarrPara} with the given children.
     *
     * @return the new instance of NarrPara.
     */
    public NarrPara createNarrPara(java.util.List content);

    /**
     * Creates an instance of {@link TruePred}.
     *
     * @return the new instance of TruePred.
     */
    public TruePred createTruePred();

    /**
     * Creates an instance of {@link Name}.
     *
     * @return the new instance of Name.
     */
    public Name createName();

    /**
     * Creates an instance of {@link Name} with the given children.
     *
     * @return the new instance of Name.
     */
    public Name createName(String word, java.util.List stroke);

    /**
     * Creates an instance of {@link NumExpr}.
     *
     * @return the new instance of NumExpr.
     */
    public NumExpr createNumExpr();

    /**
     * Creates an instance of {@link NumExpr} with the given children.
     *
     * @return the new instance of NumExpr.
     */
    public NumExpr createNumExpr(java.math.BigInteger value);

    /**
     * Creates an instance of {@link NameExprPair} with the given children.
     *
     * @return the new instance of NameExprPair.
     */
    public NameExprPair createNameExprPair(DeclName name, Expr expr);

    /**
     * Creates an instance of {@link TupleSelExpr}.
     *
     * @return the new instance of TupleSelExpr.
     */
    public TupleSelExpr createTupleSelExpr();

    /**
     * Creates an instance of {@link TupleSelExpr} with the given children.
     *
     * @return the new instance of TupleSelExpr.
     */
    public TupleSelExpr createTupleSelExpr(Integer select, Expr expr);

    /**
     * Creates an instance of {@link LambdaExpr}.
     *
     * @return the new instance of LambdaExpr.
     */
    public LambdaExpr createLambdaExpr();

    /**
     * Creates an instance of {@link LambdaExpr} with the given children.
     *
     * @return the new instance of LambdaExpr.
     */
    public LambdaExpr createLambdaExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link IffExpr}.
     *
     * @return the new instance of IffExpr.
     */
    public IffExpr createIffExpr();

    /**
     * Creates an instance of {@link IffExpr} with the given children.
     *
     * @return the new instance of IffExpr.
     */
    public IffExpr createIffExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link IffPred}.
     *
     * @return the new instance of IffPred.
     */
    public IffPred createIffPred();

    /**
     * Creates an instance of {@link IffPred} with the given children.
     *
     * @return the new instance of IffPred.
     */
    public IffPred createIffPred(Pred leftPred, Pred rightPred);

    /**
     * Creates an instance of {@link FalsePred}.
     *
     * @return the new instance of FalsePred.
     */
    public FalsePred createFalsePred();

    /**
     * Creates an instance of {@link TypeEnvAnn}.
     *
     * @return the new instance of TypeEnvAnn.
     */
    public TypeEnvAnn createTypeEnvAnn();

    /**
     * Creates an instance of {@link TypeEnvAnn} with the given children.
     *
     * @return the new instance of TypeEnvAnn.
     */
    public TypeEnvAnn createTypeEnvAnn(java.util.List nameTypePair);

    /**
     * Creates an instance of {@link UnparsedZSect}.
     *
     * @return the new instance of UnparsedZSect.
     */
    public UnparsedZSect createUnparsedZSect();

    /**
     * Creates an instance of {@link UnparsedZSect} with the given children.
     *
     * @return the new instance of UnparsedZSect.
     */
    public UnparsedZSect createUnparsedZSect(java.util.List content);

    /**
     * Creates an instance of {@link UnparsedPara}.
     *
     * @return the new instance of UnparsedPara.
     */
    public UnparsedPara createUnparsedPara();

    /**
     * Creates an instance of {@link UnparsedPara} with the given children.
     *
     * @return the new instance of UnparsedPara.
     */
    public UnparsedPara createUnparsedPara(java.util.List content);

    /**
     * Creates an instance of {@link ImpliesPred}.
     *
     * @return the new instance of ImpliesPred.
     */
    public ImpliesPred createImpliesPred();

    /**
     * Creates an instance of {@link ImpliesPred} with the given children.
     *
     * @return the new instance of ImpliesPred.
     */
    public ImpliesPred createImpliesPred(Pred leftPred, Pred rightPred);

    /**
     * Creates an instance of {@link NameTypePair} with the given children.
     *
     * @return the new instance of NameTypePair.
     */
    public NameTypePair createNameTypePair(DeclName name, Type type);

    /**
     * Creates an instance of {@link SchText}.
     *
     * @return the new instance of SchText.
     */
    public SchText createSchText();

    /**
     * Creates an instance of {@link SchText} with the given children.
     *
     * @return the new instance of SchText.
     */
    public SchText createSchText(java.util.List decl, Pred pred);

    /**
     * Creates an instance of {@link Operand}.
     *
     * @return the new instance of Operand.
     */
    public Operand createOperand();

    /**
     * Creates an instance of {@link Operand} with the given children.
     *
     * @return the new instance of Operand.
     */
    public Operand createOperand(Boolean list);

    /**
     * Creates an instance of {@link ProjExpr}.
     *
     * @return the new instance of ProjExpr.
     */
    public ProjExpr createProjExpr();

    /**
     * Creates an instance of {@link ProjExpr} with the given children.
     *
     * @return the new instance of ProjExpr.
     */
    public ProjExpr createProjExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link Branch} with the given children.
     *
     * @return the new instance of Branch.
     */
    public Branch createBranch(DeclName declName, Expr expr);

    /**
     * Creates an instance of {@link TypeAnn}.
     *
     * @return the new instance of TypeAnn.
     */
    public TypeAnn createTypeAnn();

    /**
     * Creates an instance of {@link TypeAnn} with the given children.
     *
     * @return the new instance of TypeAnn.
     */
    public TypeAnn createTypeAnn(Type type);

    /**
     * Creates an instance of {@link GenType} with the given children.
     *
     * @return the new instance of GenType.
     */
    public GenType createGenType(DeclName name);

    /**
     * Creates an instance of {@link OptempPara}.
     *
     * @return the new instance of OptempPara.
     */
    public OptempPara createOptempPara();

    /**
     * Creates an instance of {@link OptempPara} with the given children.
     *
     * @return the new instance of OptempPara.
     */
    public OptempPara createOptempPara(java.util.List wordOrOperand, Cat cat, Assoc assoc, Integer prec);

    /**
     * Creates an instance of {@link ExistsPred}.
     *
     * @return the new instance of ExistsPred.
     */
    public ExistsPred createExistsPred();

    /**
     * Creates an instance of {@link ExistsPred} with the given children.
     *
     * @return the new instance of ExistsPred.
     */
    public ExistsPred createExistsPred(SchText schText, Pred pred);

    /**
     * Creates an instance of {@link NameSectTypeTriple} with the given children.
     *
     * @return the new instance of NameSectTypeTriple.
     */
    public NameSectTypeTriple createNameSectTypeTriple(DeclName name, String sect, Type type);

    /**
     * Creates an instance of {@link NegPred}.
     *
     * @return the new instance of NegPred.
     */
    public NegPred createNegPred();

    /**
     * Creates an instance of {@link NegPred} with the given children.
     *
     * @return the new instance of NegPred.
     */
    public NegPred createNegPred(Pred pred);

    /**
     * Creates an instance of {@link PreExpr}.
     *
     * @return the new instance of PreExpr.
     */
    public PreExpr createPreExpr();

    /**
     * Creates an instance of {@link PreExpr} with the given children.
     *
     * @return the new instance of PreExpr.
     */
    public PreExpr createPreExpr(Expr expr);

    /**
     * Creates an instance of {@link SectTypeEnvAnn}.
     *
     * @return the new instance of SectTypeEnvAnn.
     */
    public SectTypeEnvAnn createSectTypeEnvAnn();

    /**
     * Creates an instance of {@link SectTypeEnvAnn} with the given children.
     *
     * @return the new instance of SectTypeEnvAnn.
     */
    public SectTypeEnvAnn createSectTypeEnvAnn(java.util.List nameSectTypeTriple);

    /**
     * Creates an instance of {@link ExprPred}.
     *
     * @return the new instance of ExprPred.
     */
    public ExprPred createExprPred();

    /**
     * Creates an instance of {@link ExprPred} with the given children.
     *
     * @return the new instance of ExprPred.
     */
    public ExprPred createExprPred(Expr expr);

    /**
     * Creates an instance of {@link GivenType} with the given children.
     *
     * @return the new instance of GivenType.
     */
    public GivenType createGivenType(DeclName name);

    /**
     * Creates an instance of {@link InclDecl}.
     *
     * @return the new instance of InclDecl.
     */
    public InclDecl createInclDecl();

    /**
     * Creates an instance of {@link InclDecl} with the given children.
     *
     * @return the new instance of InclDecl.
     */
    public InclDecl createInclDecl(Expr expr);

    /**
     * Creates an instance of {@link SchemaType}.
     *
     * @return the new instance of SchemaType.
     */
    public SchemaType createSchemaType();

    /**
     * Creates an instance of {@link SchemaType} with the given children.
     *
     * @return the new instance of SchemaType.
     */
    public SchemaType createSchemaType(Signature signature);

    /**
     * Creates an instance of {@link BindSelExpr} with the given children.
     *
     * @return the new instance of BindSelExpr.
     */
    public BindSelExpr createBindSelExpr(RefName name, Expr expr);

    /**
     * Creates an instance of {@link DeclName}.
     *
     * @return the new instance of DeclName.
     */
    public DeclName createDeclName();

    /**
     * Creates an instance of {@link DeclName} with the given children.
     *
     * @return the new instance of DeclName.
     */
    public DeclName createDeclName(String id, String word, java.util.List stroke);

    /**
     * Creates an instance of {@link ForallPred}.
     *
     * @return the new instance of ForallPred.
     */
    public ForallPred createForallPred();

    /**
     * Creates an instance of {@link ForallPred} with the given children.
     *
     * @return the new instance of ForallPred.
     */
    public ForallPred createForallPred(SchText schText, Pred pred);

    /**
     * Creates an instance of {@link OrExpr}.
     *
     * @return the new instance of OrExpr.
     */
    public OrExpr createOrExpr();

    /**
     * Creates an instance of {@link OrExpr} with the given children.
     *
     * @return the new instance of OrExpr.
     */
    public OrExpr createOrExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link Spec}.
     *
     * @return the new instance of Spec.
     */
    public Spec createSpec();

    /**
     * Creates an instance of {@link Spec} with the given children.
     *
     * @return the new instance of Spec.
     */
    public Spec createSpec(java.util.List sect, String version, String author, java.util.Calendar modified, String source);

    /**
     * Creates an instance of {@link LocAnn}.
     *
     * @return the new instance of LocAnn.
     */
    public LocAnn createLocAnn();

    /**
     * Creates an instance of {@link LocAnn} with the given children.
     *
     * @return the new instance of LocAnn.
     */
    public LocAnn createLocAnn(String loc, Integer line, Integer col);

    /**
     * Creates an instance of {@link PowerExpr}.
     *
     * @return the new instance of PowerExpr.
     */
    public PowerExpr createPowerExpr();

    /**
     * Creates an instance of {@link PowerExpr} with the given children.
     *
     * @return the new instance of PowerExpr.
     */
    public PowerExpr createPowerExpr(Expr expr);

    /**
     * Creates an instance of {@link HideExpr} with the given children.
     *
     * @return the new instance of HideExpr.
     */
    public HideExpr createHideExpr(java.util.List name, Expr expr);

    /**
     * Creates an instance of {@link GivenPara} with the given children.
     *
     * @return the new instance of GivenPara.
     */
    public GivenPara createGivenPara(java.util.List declName);

    /**
     * Creates an instance of {@link PowerType}.
     *
     * @return the new instance of PowerType.
     */
    public PowerType createPowerType();

    /**
     * Creates an instance of {@link PowerType} with the given children.
     *
     * @return the new instance of PowerType.
     */
    public PowerType createPowerType(Type type);

    /**
     * Creates an instance of {@link AndExpr}.
     *
     * @return the new instance of AndExpr.
     */
    public AndExpr createAndExpr();

    /**
     * Creates an instance of {@link AndExpr} with the given children.
     *
     * @return the new instance of AndExpr.
     */
    public AndExpr createAndExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link RenameExpr}.
     *
     * @return the new instance of RenameExpr.
     */
    public RenameExpr createRenameExpr();

    /**
     * Creates an instance of {@link RenameExpr} with the given children.
     *
     * @return the new instance of RenameExpr.
     */
    public RenameExpr createRenameExpr(java.util.List nameNamePair, Expr expr);

    /**
     * Creates an instance of {@link AndPred}.
     *
     * @return the new instance of AndPred.
     */
    public AndPred createAndPred();

    /**
     * Creates an instance of {@link AndPred} with the given children.
     *
     * @return the new instance of AndPred.
     */
    public AndPred createAndPred(Op op, Pred leftPred, Pred rightPred);

    /**
     * Creates an instance of {@link ConjPara} with the given children.
     *
     * @return the new instance of ConjPara.
     */
    public ConjPara createConjPara(java.util.List declName, Pred pred);

    /**
     * Creates an instance of {@link NumStroke}.
     *
     * @return the new instance of NumStroke.
     */
    public NumStroke createNumStroke();

    /**
     * Creates an instance of {@link NumStroke} with the given children.
     *
     * @return the new instance of NumStroke.
     */
    public NumStroke createNumStroke(Integer number);

    /**
     * Creates an instance of {@link ZSect} with the given children.
     *
     * @return the new instance of ZSect.
     */
    public ZSect createZSect(String name, java.util.List parent, java.util.List para);

    /**
     * Creates an instance of {@link ThetaExpr}.
     *
     * @return the new instance of ThetaExpr.
     */
    public ThetaExpr createThetaExpr();

    /**
     * Creates an instance of {@link ThetaExpr} with the given children.
     *
     * @return the new instance of ThetaExpr.
     */
    public ThetaExpr createThetaExpr(java.util.List stroke, Expr expr);

    /**
     * Creates an instance of {@link SetExpr}.
     *
     * @return the new instance of SetExpr.
     */
    public SetExpr createSetExpr();

    /**
     * Creates an instance of {@link SetExpr} with the given children.
     *
     * @return the new instance of SetExpr.
     */
    public SetExpr createSetExpr(java.util.List expr);

    /**
     * Creates an instance of {@link SetCompExpr}.
     *
     * @return the new instance of SetCompExpr.
     */
    public SetCompExpr createSetCompExpr();

    /**
     * Creates an instance of {@link SetCompExpr} with the given children.
     *
     * @return the new instance of SetCompExpr.
     */
    public SetCompExpr createSetCompExpr(SchText schText, Expr expr);

    /**
     * Creates an instance of {@link PipeExpr}.
     *
     * @return the new instance of PipeExpr.
     */
    public PipeExpr createPipeExpr();

    /**
     * Creates an instance of {@link PipeExpr} with the given children.
     *
     * @return the new instance of PipeExpr.
     */
    public PipeExpr createPipeExpr(Expr leftExpr, Expr rightExpr);

    /**
     * Creates an instance of {@link RefExpr} with the given children.
     *
     * @return the new instance of RefExpr.
     */
    public RefExpr createRefExpr(RefName refName, java.util.List expr, Boolean mixfix);

    /**
     * Creates an instance of {@link NegExpr}.
     *
     * @return the new instance of NegExpr.
     */
    public NegExpr createNegExpr();

    /**
     * Creates an instance of {@link NegExpr} with the given children.
     *
     * @return the new instance of NegExpr.
     */
    public NegExpr createNegExpr(Expr expr);

    /**
     * Creates an instance of {@link ProdExpr}.
     *
     * @return the new instance of ProdExpr.
     */
    public ProdExpr createProdExpr();

    /**
     * Creates an instance of {@link ProdExpr} with the given children.
     *
     * @return the new instance of ProdExpr.
     */
    public ProdExpr createProdExpr(java.util.List expr);

    /**
     * Creates an instance of {@link DecorExpr}.
     *
     * @return the new instance of DecorExpr.
     */
    public DecorExpr createDecorExpr();

    /**
     * Creates an instance of {@link DecorExpr} with the given children.
     *
     * @return the new instance of DecorExpr.
     */
    public DecorExpr createDecorExpr(Stroke stroke, Expr expr);

    /**
     * Creates an instance of {@link OutStroke}.
     *
     * @return the new instance of OutStroke.
     */
    public OutStroke createOutStroke();

    /**
     * Creates an instance of {@link Parent}.
     *
     * @return the new instance of Parent.
     */
    public Parent createParent();

    /**
     * Creates an instance of {@link Parent} with the given children.
     *
     * @return the new instance of Parent.
     */
    public Parent createParent(String word);

    /**
     * Creates an instance of {@link Exists1Pred}.
     *
     * @return the new instance of Exists1Pred.
     */
    public Exists1Pred createExists1Pred();

    /**
     * Creates an instance of {@link Exists1Pred} with the given children.
     *
     * @return the new instance of Exists1Pred.
     */
    public Exists1Pred createExists1Pred(SchText schText, Pred pred);

    /**
     * Creates an instance of {@link AxPara} with the given children.
     *
     * @return the new instance of AxPara.
     */
    public AxPara createAxPara(java.util.List declName, SchText schText, Box box);

    /**
     * Creates an instance of {@link SchExpr}.
     *
     * @return the new instance of SchExpr.
     */
    public SchExpr createSchExpr();

    /**
     * Creates an instance of {@link SchExpr} with the given children.
     *
     * @return the new instance of SchExpr.
     */
    public SchExpr createSchExpr(SchText schText);

    /**
     * Creates an instance of {@link TupleExpr}.
     *
     * @return the new instance of TupleExpr.
     */
    public TupleExpr createTupleExpr();

    /**
     * Creates an instance of {@link TupleExpr} with the given children.
     *
     * @return the new instance of TupleExpr.
     */
    public TupleExpr createTupleExpr(java.util.List expr);

}
