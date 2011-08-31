/**
Copyright 2007, Leo Freitas
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.vcg.z.feasibility;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.z.ZStateInfo;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.transformer.feasibility.ZPredTransformerFSB;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.util.ZUtils;

import net.sourceforge.czt.z.visitor.AxParaVisitor;

import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;

import net.sourceforge.czt.z.util.ZString;

/**
 *
 * @author leo
 * @since Jan 02, 2011
 */
public class FeasibilityVCCollector extends TrivialFeasibilityVCCollector implements
  GivenParaVisitor<Pred>,
  FreeParaVisitor<Pred>,
  AxParaVisitor<Pred>,
  ZFreetypeListVisitor<Pred>,
  FreetypeVisitor<Pred>,
  ZBranchListVisitor<Pred>,
  BranchVisitor<Pred>,
  FeasibilityPropertyKeys
{

  protected ZPredTransformerFSB predTransformer_;

  private boolean nonEmptyGivenSets_;
  private boolean doCreateZSchemas_;

  private final Stroke dash_;
  private final Stroke output_;
  private final Stroke input_;
  private ZName currentName_;
  private final ZName setInterName_;
  private final ZName freeTypeCtorOpName_;

  private ZName stateSchema_;
  private ZNameList stateSchemaGenParams_;
  private final Map<ZName, AxPara> addedSigSchemas_;
  private final List<AxPara> addedSigSchemasList_;

  /**
   * 
   */
  public FeasibilityVCCollector()
  {
    this(ZUtils.createConsoleFactory());
  }  
  
  /** Creates a new instance of DCTerm
   * @param factory 
   */
  public FeasibilityVCCollector(Factory factory)
  {
    super(factory);
    predTransformer_ = new ZPredTransformerFSB(factory, this);
    predTransformer_.setApplyTransformer(PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT);
    setNonemptyGivenSetVC(PROP_VCG_FEASIBILITY_ADD_GIVENSET_VCS_DEFAULT);
    setCreateZSchemas(PROP_VCG_FEASIBILITY_CREATE_ZSCHEMAS_DEFAULT);
    setZStateName(null);
    currentName_ = null;
    stateSchemaGenParams_ = null;
    output_ = factory_.createOutStroke();
    dash_ = factory_.createNextStroke();
    input_ = factory_.createInStroke();
    setInterName_ = factory_.createZName(ZString.ARG_TOK+ZString.CAP+ZString.ARG_TOK);
    freeTypeCtorOpName_ = factory_.createZName(ZString.ARG_TOK+ZString.INJ+ZString.ARG_TOK);
    addedSigSchemas_ = new TreeMap<ZName, AxPara>(ZUtils.ZNAME_COMPARATOR);
    addedSigSchemasList_ = new ArrayList<AxPara>();
  }

  protected void clearAddedPara()
  {
    addedSigSchemas_.clear();
    addedSigSchemasList_.clear();
    setZStateName(null);
  }

  @Override
  public List<? extends Para> addedPara()
  {
    assert addedSigSchemasList_.size() == addedSigSchemas_.size() &&
            addedSigSchemasList_.containsAll(addedSigSchemas_.values());
    return Collections.unmodifiableList(addedSigSchemasList_);
  }

  protected ZName getStateSchema()
  {
    return stateSchema_;
  }

  protected ZNameList getStateSchemaGenParams()
  {
    return stateSchemaGenParams_;
  }

  protected VCCollectionException createVCCollectionException(final String message)
  {
    return new FeasibilityException(message);
  }
  
  protected VCCollectionException createVCCollectionException(final String message, Throwable e)
  {
    return new FeasibilityException(message, e);
  }

  @Override
  public TermTransformer<Pred> getTransformer()
  {
    return predTransformer_;
  }

  public boolean isAddingNonemptyGivenSetVC()
  {
    return nonEmptyGivenSets_;
  }

  public boolean isCreatingZSchemas()
  {
    return doCreateZSchemas_;
  }

  protected final void setNonemptyGivenSetVC(boolean value)
  {
    nonEmptyGivenSets_ = value;
  }

  protected final void setCreateZSchemas(boolean value)
  {
    doCreateZSchemas_ = value;
  }

  protected final void setZStateName(ZName n)
  {
    stateSchema_ = n;
    stateSchemaGenParams_ = null;
  }

  protected ZName getZStateName()
  {
    return stateSchema_;
  }

  protected ZNameList getZStateGenParams()
  {
    return stateSchemaGenParams_;
  }

  /** VC COLLECTOR METHODS
   * @param vc
   * @return
   * @throws VCCollectionException
   */

  @Override
  protected VCType getVCType(Pred vc) throws VCCollectionException
  {
    VCType result = vc.getAnn(VCType.class);
    if (result == null)
      result = VCType.NONE;
    return result;
  }

  public interface VCNameSuffix
  {
    public String getVCNameSuffix();
  }

  @Override
  public VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    VCNameSuffix ns = term.getAnn(VCNameSuffix.class);
    if (getVCNameFactory() != null)
      if (ns != null)
        return new FeasibilityVC(vcId, term, type, vc, getVCNameFactory(), ns.getVCNameSuffix());
      else
        return new FeasibilityVC(vcId, term, type, vc, getVCNameFactory());
    else
      if (ns != null)
        return new FeasibilityVC(vcId,term, type, vc, ns.getVCNameSuffix());
      else
        return new FeasibilityVC(vcId, term, type, vc);
  }

  @Override
  protected void beforeCalculateVC(Term term, List<? extends InfoTable> tables)
          throws VCCollectionException
  {
    super.beforeCalculateVC(term, tables);
    if (getDefTable() == null)
    {
      throw new VCCollectionException("VCG-FSB-NO-DEFTBL: cannot calulate fsb vcs without DefTbl");
    }
  }

  /** PARAGRAPH VISITING METHODS */

  /**
   * Calculates DC for given term (i.e. visits term). As some Z productions have
   * null terms , like AxPara \begin{axdef} x: \nat \end{axdef} has null predicate,
   * implementations should take care of such situations accordingly. For null terms
   * in this collector, we presume a harmless DC condition (e.g., true).
   * @param term
   * @return
   */
  @Override
  public Pred visit(Term term)
  {
    assert getDefTable() != null;
    if (term == null)
    {
      // for null terms, warn, but assume harmless (E.g., no VCs to be generated)
      getLogger().finest("VCG-FSBCOL-NULL-TERM");
      return predTransformer_.truePred();
    }
    else
    {
      return getTransformer().visit(term);
    }
  }

  /* TERM VISITING METHODS */

  /**
   * [A, B] -->  \lnot A = \{\} \land \lnot B = \{\}
   * @param term
   * @return
   */
  @Override
  public Pred visitGivenPara(GivenPara term)
  {
    if (isAddingNonemptyGivenSetVC())
    {
      Pred result = predTransformer_.truePred();
      for (Name name : term.getNames())
      {
        Pred vc = factory_.createNegPred(factory_.createEquality(
                    factory_.createRefExpr(name),
                    factory_.createSetExpr(factory_.createZExprList())));
        vc.getAnns().add(VCType.AXIOM);
        result = predTransformer_.andPred(result, vc);
      }
      return result;
    }
    else
    {
      return predTransformer_.truePred();
    }
  }

  @Override
  public Pred visitFreePara(FreePara term)
  {
    return visit(term.getFreetypeList());
  }

  @Override
  public Pred visitZFreetypeList(ZFreetypeList term)
  {
    return predTransformer_.andPredList(term);
  }

  /** DC the branch list of each individual Freetype */
  @Override
  public Pred visitFreetype(Freetype term)
  {
    currentName_ = term.getZName();
    Pred result = visit(ZUtils.assertZBranchList(term.getBranchList()));
    currentName_ = null;
    return result;
  }

  /** DC a list of Branch from a Freetype */
  @Override
  public Pred visitZBranchList(ZBranchList term)
  {
    // TODO: hum... maybe split these lemmas into various conjecrtures...
    return predTransformer_.andPredList(term);
  }

  /**  */
  @Override
  public Pred visitBranch(Branch term)
  {
    // constructors: add feasibility lemma to be proved
    if (term.getExpr() != null)
    {
      assert currentName_ != null;
      // E \inj FT
      Expr ftExpr = factory_.createGenOpApp(freeTypeCtorOpName_,
              factory_.list(term.getExpr(), factory_.createRefExpr(currentName_)));
      // FT ::= f \ldata E \rdata ==> add: f \in E \inj FT
      Pred result = factory_.createMemPred(term.getName(), ftExpr);
      result.getAnns().add(VCType.RULE);
      return result;
    }
    else
    {
      return predTransformer_.truePred();
    }
  }

  /**
   * This implements various axiomatic description paragraphs:
   * AxPara (from axdef)    : \begin{axdef} D \where P \end{axdef}
   * AxPara (from gendef)   : \begin{gendef}[X] D \where P \end{gendef}
   * AxPara (from schema)   : \begin{schema} D \where P \end{schema}
   * AxPara (from genschema): \begin{schema}[X] D \where P \end{schema}
   * AxPara (from abbrev.)  : \begin{zed} N[X] == E \end{zed}
   *
   * This covers the Z/Eves domain check rules for:
   *
   * DC(\begin{zed} N[X] == E \end{zed})     \iff DC(E)
   * DC(\begin{xxx}[X] D \where P \end{xxx}) \iff DC(D) \land DC(D) \land (\forall D @ DC(P))
   *
   * The RHS of this equivalence is the result this method returns.
   *
   */
  @Override
  public Pred visitAxPara(AxPara term)
  {
    Pred result = null;
    switch (term.getBox())
    {
      case AxBox:
        result = handleAxiom(term.getZSchText());
        break;

      case OmitBox:
      case SchBox:
        // for OmitBox term might not be a schema
        ZName termName = ((ConstDecl)term.getZSchText().getZDeclList().get(0)).getZName();
        Definition termDef = getDefTable().lookupName(termName);
        if (termDef != null)
        {
        //  Expr termExpr  = ((ConstDecl)term.getZSchText().getZDeclList().get(0)).getExpr();
//          assert termDef.getExpr().equals(termExpr);
          
          if (termDef.getDefinitionKind().isSchemaReference())
          {
            collectStateInfo(term, termDef);
            result = handleSchema(termDef);
          }
          else if (termDef.getDefinitionKind().isAxiom())
          {
            result = handleHorizDef(termDef);
          }
          break;
        }
        else
        {
          throw new CztException(createVCCollectionException("VC-FSB-AXPARA-PROBLEM = " + termName));
        }
      default:
        // this case should never happen, yet we need to return something
        // in the unlikely case the Java compiler messes up with Box Enums
        // (i.e. corrupted byte code classes)!
        throw new AssertionError("Invalid Box for AxPara! " + term.getBox());
    }
    assert result != null;
    return result;
  }

  protected void collectStateInfo(AxPara term, Definition termDef)
  {
    if (term.hasAnn(ZStateInfo.class))
    {
      if (term.getAnn(ZStateInfo.class).equals(ZStateInfo.STATE) ||
          term.getAnn(ZStateInfo.class).equals(ZStateInfo.ASTATE))
      {
        if (stateSchema_ != null)
          throw new CztException(createVCCollectionException(
                  "State schema already set through section manager properties as " + ZUtils.toStringZName(stateSchema_)
                  + ". Cannot change it to " + ZUtils.toStringZName(termDef.getDefName())));
        setZStateName(termDef.getDefName());
        stateSchemaGenParams_ = termDef.getGenericParams();
      }
    }
    else if (stateSchema_ != null && ZUtils.namesEqual(termDef.getDefName(), stateSchema_))
    {
      stateSchemaGenParams_ = termDef.getGenericParams();
    }
  }

  /* VC GENERATION HELPER METHODS */

  // FSB(AX D | P ) => \exists D | true @ P
  protected Pred handleAxiom(ZSchText zSchText)
  {
    Pred pred = zSchText.getPred();
    return predTransformer_.existsPred(zSchText.getZDeclList(), pred == null ? truePred() : pred);
  }

  // FSB(N == E) => \exists N : E | true @ true
  protected Pred handleHorizDef(Definition horizDef)
  {
    assert horizDef != null && horizDef.getDefinitionKind().isAxiom();
    Expr expr = horizDef.getExpr();
    if (expr instanceof NumExpr)
    {
      // N == Number => \exists N: \power \{ Number \} | true @ true (?)
      expr = factory_.createSetExpr(factory_.createZExprList(factory_.list(expr)));
    }
    return predTransformer_.existsPred(factory_.createZDeclList(
            factory_.list(factory_.createVarDecl(factory_.createZNameList(factory_.list(horizDef.getDefName())), expr))), truePred());
  }

  public FSBVCNameFactory getFSBVCNameFactory()
  {
    assert getVCNameFactory() instanceof FSBVCNameFactory;
    return (FSBVCNameFactory)getVCNameFactory();
  }

  protected ZName getSigSchemaName(ZName schName)
  {
    return getFSBVCNameFactory().createNameForSigSchemaOf(schName);
  }

  protected ZExprList createGenericParamsRefExprs(ZNameList genParams)
  {
    ZExprList result = factory_.createZExprList();
    for(Name name : genParams)
    {
      result.add(factory_.createRefExpr(name));
    }
    assert result.size() == genParams.size();
    return result;
  }

  protected RefExpr createSchRef(ZName schName, ZNameList genParams)
  {
    return genParams != null &&
           !genParams.isEmpty() ?
             factory_.createRefExpr(schName,
                createGenericParamsRefExprs(genParams), Boolean.FALSE) :
             factory_.createRefExpr(schName);
    
  }

  // FSB(S == [D | P]) ==> before(D)  = {} XOR after(D) = {} => \exists bindings(S) @ P
  // FSB(S == [D | P]) ==> before(D) != {} &&  after(D)!= {} => \forall before(D) | userPre(Op) @ \exists after(D) @ P
  // FSB(S == [D | P]) ==> before(D)  = {} &&  after(D) = {} => P, where its free variables must be in (type-) context
  protected Pred handleSchema(Definition schDef)
  {
    assert schDef != null && schDef.getDefinitionKind().isSchemaReference();
    // for schemas add
    ZName schName  = schDef.getDefName();
    ZNameList genParams = schDef.getGenericParams();
    //Expr schExpr   = schDef.getExpr();
    RefExpr schRef = createSchRef(schName, genParams);
    try
    {
      Pred result;
      // get the bindings and filter then by category
      SortedSet<Definition> mixedBindings  = getDefTable().bindings(schName);

      //if (mixedBindings.isEmpty())
      //{
      SortedSet<Definition> afterBindings  = filterBindings(mixedBindings, AFTER_FILTER);
      SortedSet<Definition> beforeBindings = filterBindings(mixedBindings, BEFORE_FILTER);
      assert Collections.disjoint(beforeBindings, afterBindings)
                && mixedBindings.containsAll(afterBindings)
                && mixedBindings.containsAll(beforeBindings)
                && (beforeBindings.size() + afterBindings.size() == mixedBindings.size());

      // if either before or after bindings are empty, then this is a existential proof
      // that is, an initialisation proof for the state say.
      boolean existential = beforeBindings.isEmpty() || afterBindings.isEmpty();

      // if both bindings are empty, then this is a degenerate case, and there is nothing todo.
      boolean emptybindings = beforeBindings.isEmpty() && afterBindings.isEmpty();

      // create the zSchText of assumptions and set the precondition to the user-suplied predicate
      // populate the ZDeclList for the before bindings - this create a flat list of decl (e.g., all schemas expanded)
      // we assume this will typecheck. if it doesn't it is up to the user.
      //
      // In case of existential (e.g., either is empty, then put after for before in assumptions: \exists S' @ Init)
      ZSchText fsbAssumptions = factory_.createZSchText(factory_.createZDeclList(), factory_.createTruePred());
      populateDeclList(fsbAssumptions.getZDeclList(), beforeBindings.isEmpty() ? afterBindings : beforeBindings);

      // get any user defined predicates
      fsbAssumptions.setPred(getUserDefinedSchemaPRE(schName, genParams));

      AxPara schNameSigSchema = null;
      ZName schSigName = null;
      RefExpr schSigRef = null;
      ZSchText schSigSchText = null;

      if (isCreatingZSchemas())
      {
        // create a signature schema name + ref expr from current schema, considering its generic params
        schSigName = getSigSchemaName(schName);
        schSigRef = createSchRef(schSigName, genParams);

        // create a ZSchText with the schSigRef (e.g., [ SchNameSig | true ]), as well as an AxPara
        // as SchNameSig == [ before + inputs | P ], where P = getUserDefinedSchemaPRE
        schSigSchText = predTransformer_.createSchemaInclusion(schSigRef);
        schNameSigSchema = predTransformer_.createSchExpr(genParams, schSigName, fsbAssumptions);
      }

      // only consider precondition predicates for schemas with after variables
      // schemas with before variables should have a existential proof!
      //
      // St  == [ x: T | I ]
      // Sch == [ \Delta St; i?, o!: T | P ] ==> \forall [ x: T; i?: T | I \land USER-DEF-PRE ] @ \pre Sch
      //                                         \forall x: T; i?: T @ I \land USER-DEF-PRE \implies \exist x': T; o!: T @ Sch
      if (!existential) // before \neq {} \land after \neq {}
      {
        if (!isCreatingZSchemas())
        {
          // create the zSchText of conclusions as a flat list of decl: [ | true ]
          ZSchText fsbConclusions = factory_.createZSchText(factory_.createZDeclList(), factory_.createTruePred());
          // conclusions = [ d1', ... dn', do!: T | true ]
          populateDeclList(fsbConclusions.getZDeclList(), afterBindings);

          // \forall assumptions @ \exists conclusions @ Sch
          //Pred invariant = getSchemaInvariant(schRef);//, schExpr); // try expanding the schema invariants - if fails, just use the schema reference
          result = factory_.createExprPred(
                  predTransformer_.forAllExpr(fsbAssumptions,
                    predTransformer_.existsExpr(fsbConclusions, schRef)));
        }
        else
        {
          assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
          // create the conclusions as a Z-centric \pre SchRef operator
          // \forall SchSig | true @ \pre Sch
          result = factory_.createExprPred(
                  predTransformer_.forAllExpr(
                    schSigSchText, factory_.createPreExpr(schRef)));
        }
      }
      // no after bindings; if there are any before bindings then create existential proof
      else if (!emptybindings) // before \neq {} XOR after \neq {} and it is existential
      {
        if (!isCreatingZSchemas())
        {
          // fsbAssumptions will have either initialisation or just true
          result = predTransformer_.existsPred(fsbAssumptions, factory_.createTruePred());
        }
        else
        {
          // z centric existential proof
          // \exists SchSig @ true
          assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
          result = predTransformer_.existsPred(schSigSchText, factory_.createTruePred());
        }
      }
      // otherwise, there is nothing to do: just return P
      else // before = after = {}
      {
        result = predTransformer_.truePred(); // TODO: still to return P from ZName (!!!)
      }

      // if anything got created, add them
      if (schNameSigSchema != null)
      {
        int cnt = 0;
        AxPara old = addedSigSchemas_.put(schSigName, schNameSigSchema);
        addedSigSchemasList_.add(schNameSigSchema);
        StringBuilder message = new StringBuilder();
        while (old != null)
        {
          message.append("Duplicated signature schema ").append(schSigName);
          schSigName.setWord(schSigName.getWord() + cnt);
          old = addedSigSchemas_.put(schSigName, schNameSigSchema);
          cnt++;
          message.append(". There is a problem in the name factory; retrying with name ").append(schSigName);
          CztLogger.getLogger(getClass()).warning(message.toString());
        }
        assert addedSigSchemasList_.size() == addedSigSchemas_.size();
      }
      return result;
    }
    catch (DefinitionException ex)
    {
      throw new CztException(createVCCollectionException("VC-FSB-SCHEMA-DEFEXCEPTION for " + schName, ex));
    }
  }

  /**
   * User supplied predicate to be assumed as part of the given schema name
   * @param name
   * @param genParams
   * @return
   */
  protected Pred getUserDefinedSchemaPRE(ZName name, ZNameList genParams)
  {
    ZName nameNoStrokes = factory_.createZName(name.getWord());
    Definition schDef = getDefTable().lookupName(nameNoStrokes);
    Pred result = predTransformer_.truePred();
    if (schDef != null)
    {
      try
      {
        SortedSet<Definition> mixed = getDefTable().bindings(nameNoStrokes);
        SortedSet<Definition> before = filterBindings(mixed, BEFORE_FILTER);
        SortedSet<Definition> after = filterBindings(mixed, AFTER_FILTER);

        // if there are no after bindings on the schema def, then add it as part
        // of the Pred part of assumptions.

        // if there are after variables, but the no before variables, this is
        // like Initialisation or existential quantification case for dashed
        // variables only schemas
        if (after.isEmpty() || before.isEmpty())
        {
          //result = factory_.createExprPred(schDef.getExpr()); ??
          //result = factory_.createExprPred(factory_.createRefExpr(nameNoStrokes));
          result = factory_.createExprPred(createSchRef(nameNoStrokes, genParams));
        }
        // else, if they are indeed mixed, then look for some user given table for any extra predicate
        // for instance the Z State schema as tagged by \zstate or \zastate (e.g., abstract only for now).
        else if (stateSchema_ != null)
        {
          if (stateSchemaGenParams_ != null && genParams != null &&
              !genParams.containsAll(stateSchemaGenParams_))
          {
            final String message = "Included state schema " + ZUtils.toStringZName(stateSchema_) +
                    " depend on generic parameters not given to schema " + ZUtils.toStringZName(name) +
                    "\n\tGiven.....: " + genParams.toString() +
                    "\n\tExpected..: " + stateSchemaGenParams_.toString();
            CztLogger.getLogger(getClass()).warning(message);
          }
          // Keep the state schema as Pred part of "OpSig == [ x, y : T | State ]", for "State = [ x, y: T | inv(x,y) ]".
          // the repetition of bindings is for both clarity of what the VCG is doing and to ensure in odd cases we do not
          // mess up the VC itself (e.g., State having more bindings than we found for OpSig will lead to a type error).
          result = factory_.createExprPred(createSchRef(stateSchema_, stateSchemaGenParams_));
        }
        // else ???? TODO: let the user give schemas as string text and parser ???
      }
      catch(DefinitionException e)
      {
        // ignore and make it just true
        final String message = "Definition exception raised whilst trying to collect user defined preconditions for schema " + ZUtils.toStringZName(name) +
                "\n---------------------------------------" + e.toString() + "\n---------------------------------------\n";
        CztLogger.getLogger(getClass()).warning(message);
      }
    }
    // just true for now.
    return result;
  }

//  protected Pred getSchemaInvariant(Expr expr)
//  {
//    Pred result = factory_.createExprPred(expr);
//    // USE RULES TO CALCULATE
////    if (expr instanceof SchExpr)
////    {
////      SchExpr sexpr = (SchExpr)expr;
////      sexpr.getZSchText().
////    }
//    return result;
//  }

  protected void populateDeclList(ZDeclList zDeclList, SortedSet<Definition> bindings)
  {

    Iterator<Definition> it = bindings.iterator();

    // process the first one
    Definition currentBinding = it.hasNext() ? it.next() : null;
    ZName currentName = currentBinding != null ? currentBinding.getDefName() : null;
    Expr currentExpr;
    VarDecl currentVarDecl = null;
    List<VarDecl> decls = factory_.list();
    if (currentName != null)
    {
      currentExpr = currentBinding.getExpr();
      currentVarDecl = factory_.createVarDecl(factory_.createZNameList(factory_.list(currentName)), currentExpr);
      decls.add(currentVarDecl);
    }
    // if there is more
    while (it.hasNext())
    {
      currentBinding = it.next();
      currentName = currentBinding.getDefName();
      currentExpr = currentBinding.getExpr();
      // if names colide, change known expression -> n : E1, n: E2 ==> n: E1 \cap E2
      if (currentVarDecl != null && currentVarDecl.getZNameList().contains(currentName))
      {
        currentVarDecl.setExpr(factory_.createFunOpAppl(setInterName_, factory_.createTupleExpr(currentVarDecl.getExpr(), currentExpr)));
      }
      // otherwise create a new expression
      else
      {
        currentVarDecl = factory_.createVarDecl(factory_.createZNameList(factory_.list(currentName)), currentExpr);
        decls.add(currentVarDecl);
      }
      
    }
    zDeclList.addAll(decls);
  }

  protected SortedSet<Definition> filterBindings(SortedSet<Definition> bindings, BindingFilter filter)
  {
    SortedSet<Definition> result = new TreeSet<Definition>(bindings);
    if (!result.isEmpty())
    {
      Iterator<Definition> it = result.iterator();
      while (it.hasNext())
      {
        Definition def = it.next();
        // if this name is not to be considered, then remove it
        if (!filter.considerName(def.getDefName()))
        {
          it.remove();
        }
      }
      assert bindings.containsAll(result);
    }
    return result;
  }

  protected interface BindingFilter
  {
    public boolean considerName(ZName name);
  }

  private final BeforeBindings BEFORE_FILTER = new BeforeBindings();
  private final AfterBindings  AFTER_FILTER  = new AfterBindings();

  protected class BeforeBindings implements BindingFilter
  {
    /**
     *
     * @param name
     * @return
     */
    @Override
    public boolean considerName(ZName name)
    {
      return (!name.getZStrokeList().contains(dash_) &&
             !name.getZStrokeList().contains(output_))
             ||
             (name.getZStrokeList().contains(input_));

    }
  }

  protected class AfterBindings implements BindingFilter
  {
    /**
     *
     * @param name
     * @return
     */
    @Override
    public boolean considerName(ZName name)
    {
      return (name.getZStrokeList().contains(dash_) ||
             name.getZStrokeList().contains(output_))
             &&
             (!name.getZStrokeList().contains(input_));

    }
  }
}
