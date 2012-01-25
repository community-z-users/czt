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
import java.util.EnumMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.logging.Level;
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
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.vcg.util.BindingFilter;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.DefinitionComparator;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCConfig;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.vcg.z.VCSource;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.transformer.feasibility.ZPredTransformerFSB;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.util.ZUtils;

import net.sourceforge.czt.z.visitor.AxParaVisitor;

import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZStateAnn;
import net.sourceforge.czt.z.ast.ZStateInfo;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;

import net.sourceforge.czt.z.util.ZString;

import static net.sourceforge.czt.z.ast.ZStateInfo.*;

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

  public static final Map<ZStateInfo, String> ZSTATEINFO_EXPLANATION;

  static {
    ZSTATEINFO_EXPLANATION = new EnumMap<ZStateInfo, String>(ZStateInfo.class);
    ZSTATEINFO_EXPLANATION.put(NONE, "Normal schema");
    ZSTATEINFO_EXPLANATION.put(STATE, "State schema");
    ZSTATEINFO_EXPLANATION.put(STINIT, "State initialisation schema");
    ZSTATEINFO_EXPLANATION.put(ASTATE, "Abstract state schema");
    ZSTATEINFO_EXPLANATION.put(CSTATE, "Concrete state schema");
    ZSTATEINFO_EXPLANATION.put(ASTINIT, "Abstract state initialisation schema");
    ZSTATEINFO_EXPLANATION.put(CSTINIT, "Concrete state initialisation schema");
    ZSTATEINFO_EXPLANATION.put(ASTFIN, "Abstract state finalisation schema");
    ZSTATEINFO_EXPLANATION.put(CSTFIN, "Concrete state finalisation schema");
    ZSTATEINFO_EXPLANATION.put(AINITIN, "Abstract inputs initalisation schema");
    ZSTATEINFO_EXPLANATION.put(AFINOUT, "Abstract output finalisation schema");
    ZSTATEINFO_EXPLANATION.put(CINITIN, "Concrete inputs initialisation schema");
    ZSTATEINFO_EXPLANATION.put(CFINOUT, "Concrete outputs finalisation schema");
    ZSTATEINFO_EXPLANATION.put(RETRIEVE, "Retrieve schema");
    ZSTATEINFO_EXPLANATION.put(RETRIEVEIN, "Retrieve inputs schema");
    ZSTATEINFO_EXPLANATION.put(RETRIEVEOUT, "Retrieve outputs schema");
  }


  protected ZPredTransformerFSB predTransformer_;

  private boolean nonEmptyGivenSets_;
  private boolean doCreateZSchemas_;

  private ZName currentName_;
  private final ZName setInterName_;
  private final ZName freeTypeCtorOpName_;

  protected final Map<ZName, AxPara> addedSigSchemas_;
  protected final Map<ZName, SortedSet<Definition>> computedBindings_;
  
  private final Map<ZStateInfo, ZName> stateSchemaNames_;
  private final Map<ZStateInfo, AxPara> stateSchemas_;
  private final Map<ZStateInfo, ZNameList> stateGenParams_;

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
    currentName_ = null;
    setInterName_ = factory_.createZName(ZString.ARG_TOK+ZString.CAP+ZString.ARG_TOK);
    freeTypeCtorOpName_ = factory_.createZName(ZString.ARG_TOK+ZString.INJ+ZString.ARG_TOK);
    addedSigSchemas_ = new TreeMap<ZName, AxPara>(ZUtils.ZNAME_COMPARATOR);
    computedBindings_ = new TreeMap<ZName, SortedSet<Definition>>(ZUtils.ZNAME_COMPARATOR);
    
    stateSchemaNames_ = new EnumMap<ZStateInfo, ZName>(ZStateInfo.class);
    stateSchemas_ = new EnumMap<ZStateInfo, AxPara>(ZStateInfo.class);
    stateGenParams_ = new EnumMap<ZStateInfo, ZNameList>(ZStateInfo.class);
  }

  protected void clearAddedPara()
  {
    addedSigSchemas_.clear();
    computedBindings_.clear();
    stateSchemaNames_.clear();
    stateSchemas_.clear();
    stateGenParams_.clear();
  }

  @Override
  public List<? extends Para> addedPara()
  {
    return new ArrayList<Para>(addedSigSchemas_.values());
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

  protected final void setStateSchema(ZStateInfo type, ZName n, AxPara para, ZNameList genParams)
  {
    setStateName(type, n);
    this.stateSchemas_.put(type, para);
    setStateGenParams(type, genParams);
  }
  
  protected final void setStateName(ZStateInfo type, ZName n) {
    this.stateSchemaNames_.put(type, n);
  }

  public ZName getState(ZStateInfo type)
  {
    return this.stateSchemaNames_.get(type);
  }
  
  protected AxPara getStateSchema(ZStateInfo type) {
    return this.stateSchemas_.get(type);
  }
  
  protected ZNameList getStateGenParams(ZStateInfo type)
  {
    return this.stateGenParams_.get(type);
  }
  
  protected void setStateGenParams(ZStateInfo type, ZNameList genParams)
  {
    this.stateGenParams_.put(type, genParams);
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
    Pred result;
    
    if (isAddingNonemptyGivenSetVC())
    {
      result = predTransformer_.truePred();
      for (Name name : term.getNames())
      {
        Pred vc = factory_.createNegPred(factory_.createEquality(
                    factory_.createRefExpr(name),
                    factory_.createSetExpr(factory_.createZExprList())));
        vc.getAnns().add(VCType.AXIOM);
        result = predTransformer_.andPred(result, vc);
      }
    }
    else
    {
      result = predTransformer_.truePred();
    }
    
    // the given paragraph VCs go after the definition, to show that the given set is not empty
    result.getAnns().add(createVCConfig(ZFsbVCKind.GIVEN_PARA, Precedence.AFTER));
    
    return result;
  }

  @Override
  public Pred visitFreePara(FreePara term)
  {
    Pred result = visit(term.getFreetypeList());
    
    result.getAnns().add(createVCConfig(ZFsbVCKind.FREE_PARA, Precedence.AFTER));
    return result;
  }
  
  private VCConfig createVCConfig(ZFsbVCKind kind, Precedence prec) {
    return new VCConfig(kind.getTypeId(), prec);
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

          currentName_ = termName;

          if (termDef.getDefinitionKind().isSchemaReference())
          {
            collectStateInfo(term, termDef);
            result = handleSchema(term, termDef);
          }
          else if (termDef.getDefinitionKind().isAxiom())
          {
            result = handleHorizDef(termDef);
          }
          currentName_ = null;
          
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

  /**
   * Collects state information for the given AxPara, if it has one.
   * @param term
   * @param termDef
   * @throws CztException
   */
  protected boolean collectStateInfo(AxPara term, Definition termDef) throws CztException
  {
    boolean result = false;
    ZName termDefName = termDef.getDefName();
    ZNameList termDefGenParams = termDef.getGenericParams();
    if (term.hasAnn(ZStateAnn.class))
    {
      ZStateAnn zsa = term.getAnn(ZStateAnn.class);
      ZStateInfo zsi = zsa.getInfo();
      
      if (zsi != null) {
        
        String prefixMsg = ZSTATEINFO_EXPLANATION.get(zsi);
        
        ZStateInfo type;
        BindingFilter filter;
        
        switch (zsi) {
          case STATE:
          case ASTATE:
            type = STATE;
            filter = BindingUtils.STATE_FILTER;
            break;
          case STINIT:
          case ASTINIT:
            type = STINIT;
            filter = BindingUtils.INIT_FILTER;
            break;
          case STFIN:
          case ASTFIN:
            type = STFIN;
            filter = BindingUtils.FIN_FILTER;
            break;
          default:
            type = null;
            filter = null;
            break;
        }
        
        if (type != null) {
          markStateSchema(term, termDefName, termDefGenParams, prefixMsg, type, filter);
          result = true;
        }
      }

    }
    else if (isState(STATE, termDefName)) {
      setStateGenParams(STATE, termDefGenParams);
    }
    return result;
  }
  
  protected void markStateSchema(AxPara term, ZName termDefName, ZNameList termDefGenParams,
      final String prefixMsg, ZStateInfo type, BindingFilter filter)
  {

    checkPreviousState(prefixMsg, getState(type), termDefName);
    setStateSchema(type, termDefName, term, termDefGenParams);
    checkStateBindings(prefixMsg, termDefName, filter);
  }
  
  protected boolean isState(ZStateInfo type, ZName termDefName)
  {
    ZName stateSchema = getState(type);
    return stateSchema != null && ZUtils.namesEqual(termDefName, stateSchema);
  }
  
  protected void checkPreviousState(String prefix, ZName oldStName, ZName newStName) throws CztException
  {
    if (oldStName != null)
      throw new CztException(createVCCollectionException(
              prefix + " already set through section manager properties as " + ZUtils.toStringZName(oldStName)
              + ". Cannot change it to " + ZUtils.toStringZName(newStName)));
  }

  /**
   * Checks the given schema name in the definition table
   * @param prefix
   * @param stName
   * @param filter
   * @throws CztException
   */
  protected void checkStateBindings(String prefix, ZName stName, BindingFilter filter) throws CztException
  {
    SortedSet<Definition> mixedBindings;
    try
    {
      if (computedBindings_.containsKey(stName))
        throw new DefinitionException("VC-FSB-DUPLICATE-SCHEMA-IN-DEFTBL = " + stName);
      mixedBindings = new TreeSet<Definition>(getBindingsFor(stName));
    }
    catch (DefinitionException ex)
    {
      throw new CztException(createVCCollectionException("VC-FSB-STATE-SCHEMA-DEFEXCEPTION for " + stName, ex));
    }
    SortedSet<Definition> stateBindings = BindingUtils.filterBindings(mixedBindings, filter);
    mixedBindings.removeAll(stateBindings);
    if (!mixedBindings.isEmpty())
    {
      throw new CztException(createVCCollectionException(
             prefix + " '" + stName + "' has inconsistent state bindings.\n\tBindings...: " + mixedBindings.toString()));
    }
  }
  
  /**
   * Check whether bindings were already computed for the given name and return a copy of them if so.
   * Otherwise, return compute them, save them, and return a copy so that the next call can use the originals.
   * This is useful to see whether to populate schema declarations with schema inclusions or not.
   * Ah, actually there is no need to copy the result, providing it's not changed. So return a unmodifiable version then.
   * @param name
   * @return
   * @throws DefinitionException
   */
  protected SortedSet<Definition> getBindingsFor(ZName name) throws DefinitionException
  {
    SortedSet<Definition> result = computedBindings_.get(name);
    if (result == null)
    {
      result = getDefTable().bindings(name);
      computedBindings_.put(name, result);
    }
    assert result != null;
    return Collections.unmodifiableSortedSet(result); //new TreeSet<Definition>(result);
  }


  /* VC GENERATION HELPER METHODS */

  // FSB(AX D | P ) => \exists D | true @ P
  protected Pred handleAxiom(ZSchText zSchText)
  {
    Pred pred = zSchText.getPred();
    Pred result = predTransformer_.existsPred(zSchText.getZDeclList(), pred == null ? truePred() : pred);
    
    // axioms have BEFORE precedence - they need to be proved before the axiom is defined
    // otherwise the axiom may be used to prove the VC
    result.getAnns().add(createVCConfig(ZFsbVCKind.AXIOM, Precedence.BEFORE));
    
    return result;
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
    Pred result = predTransformer_.existsPred(factory_.createZDeclList(
            factory_.list(factory_.createVarDecl(factory_.createZNameList(factory_.list(horizDef.getDefName())), expr))), truePred());
    
    // horizontal definitions have BEFORE precedence - they need to be proved before the 
    // horizontal definition is stated, otherwise it may be used to prove the VC
    result.getAnns().add(createVCConfig(ZFsbVCKind.HORIZ_DEF, Precedence.BEFORE));
    
    return result;
  }

  public FSBVCNameFactory getFSBVCNameFactory()
  {
    assert getVCNameFactory() instanceof FSBVCNameFactory;
    return (FSBVCNameFactory)getVCNameFactory();
  }

  protected ZName getSigSchemaName(ZName schName)
  {
    String sigSchemaName = getFSBVCNameFactory().getSigSchemaName(schName.getWord());
    return ZUtils.FACTORY.createZName(sigSchemaName, schName.getStrokeList());
  }

  // FSB(S == [D | P]) ==> before(D)  = {} XOR after(D) = {} => \exists bindings(S) @ P
  // FSB(S == [D | P]) ==> before(D) != {} &&  after(D)!= {} => \forall before(D) | userPre(Op) @ \exists after(D) @ P
  // FSB(S == [D | P]) ==> before(D)  = {} &&  after(D) = {} => P, where its free variables must be in (type-) context
  protected Pred handleSchema(AxPara para, Definition schDef) throws CztException
  {
    assert schDef != null && schDef.getDefinitionKind().isSchemaReference();
    // for schemas add
    ZName schName  = schDef.getDefName();
    ZNameList genParams = schDef.getGenericParams();
    //Expr schExpr   = schDef.getExpr();
    Expr schRef = predTransformer_.createSchRef(schName, genParams);
    try
    {
      Pred result;
      ZFsbVCKind vcType;
      
      // get the bindings and filter then by category
      SortedSet<Definition> mixedBindings  = getBindingsFor(schName);
      SortedSet<Definition> afterBindings  = BindingUtils.afterBindingsOf(mixedBindings);
      SortedSet<Definition> beforeBindings = BindingUtils.beforeBindingsOf(mixedBindings);
      assert BindingUtils.bindingsInvariant(mixedBindings, beforeBindings, afterBindings);

      SortedSet<Definition> inputBindings = BindingUtils.inputBindingsOf(beforeBindings);
      SortedSet<Definition> outputBindings = BindingUtils.outputBindingsOf(afterBindings);

      // initialisation with non-empty inputs will have both before and after bindings, but it is not mixed.
      // similarly for finalisation with output!
      boolean initWithInput = !afterBindings.isEmpty() && !inputBindings.isEmpty() && inputBindings.equals(beforeBindings);
      boolean finWithOutput = !beforeBindings.isEmpty() && !outputBindings.isEmpty() && outputBindings.equals(afterBindings);

      // if both bindings are empty, then this is a degenerate case, and there is nothing todo.
      boolean emptybindings = beforeBindings.isEmpty() && afterBindings.isEmpty();

      AxPara schNameSigSchema = null;
      ZName schSigName = null;
      Expr schSigRef = null;
      ZSchText schSigSchText = null;
      ZSchText fsbAssumptions = factory_.createZSchText(factory_.createZDeclList(), factory_.createTruePred());

      if (isCreatingZSchemas())
      {
        // create a signature schema name + ref expr from current schema, considering its generic params
        schSigName = getSigSchemaName(schName);
        schSigRef = predTransformer_.createSchRef(schSigName, genParams);

        // create a ZSchText with the schSigRef (e.g., [ SchNameSig | true ]), as well as an AxPara
        // as SchNameSig == [ before + inputs | P ], where P = getUserDefinedSchemaPRE
        schSigSchText = predTransformer_.createSchemaInclusion(schSigRef);
        schNameSigSchema = predTransformer_.createSchExpr(genParams, schSigName, fsbAssumptions);
      }


      if (initWithInput || finWithOutput)
      {
        // e.g., FreeRTOS (and others), where state init is in stages.... might have diff names
        //if ((initWithInput && !ZUtils.namesEqual(schName, stateInitSchema_))
        //     ||
        //   (finWithOutput && !ZUtils.namesEqual(schName, stateFinSchema_)))
        if (!(initWithInput ^ finWithOutput)) // XOR
        {
          final String errorMsg = "Found inconsistent mixed bindings for " + (initWithInput ? "initialisation schema with inputs " + schName :
              finWithOutput ? "finalisation schema with outputs " + schName : "unknown schema kind with possible I/O " + schName);
          handleInclBindingsMismatch(errorMsg);
        }
        //assert !initWithInput || ZUtils.namesEqual(schName, stateInitSchema_);
        //assert !finWithOutput || ZUtils.namesEqual(schName, stateFinSchema_);

        if (initWithInput)
        {
          populateDeclList(fsbAssumptions.getZDeclList(), afterBindings, true);
          populateDeclList(fsbAssumptions.getZDeclList(), inputBindings, false);
        }
        else
        {
          assert finWithOutput;
          populateDeclList(fsbAssumptions.getZDeclList(), beforeBindings, false);
          populateDeclList(fsbAssumptions.getZDeclList(), outputBindings, true);
        }

        // get any user defined predicates - also checks whether the schName given have more than the state schema as declared bindings
        fsbAssumptions.setPred(getUserDefinedSchemaPRE(schName, genParams));

        // always existential
        if (!emptybindings)
        {
          // for the state schema, if there is a init schema, then a vc \exists State' @ StInit is added in the end
          // otherwise, add the whole VC anyway as \exists State' @ true; similarly for init/fin schemas
          if (isState(STINIT, schName) 
              || isState(STFIN, schName) 
              || isState(STATE, schName)
                && (getState(STINIT) != null || getState(STFIN) != null))
          {
            result = predTransformer_.truePred();
          }
          else if (!isCreatingZSchemas())
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
          
          vcType = ZFsbVCKind.STATE;
        }
        // otherwise, there is nothing to do: just return P
        else 
        {
          result = predTransformer_.truePred(); // TODO: still to return P from ZName (!!!)
          vcType = ZFsbVCKind.DEFAULT;
        }
      }
      else
      {
        // if either before or after bindings are empty, then this is a existential proof
        // that is, an initialisation proof for the state say.
        boolean existential = (beforeBindings.isEmpty() || afterBindings.isEmpty());

        // create the zSchText of assumptions and set the precondition to the user-suplied predicate
        // populate the ZDeclList for the before bindings - this create a flat list of decl (e.g., all schemas expanded)
        // we assume this will typecheck. if it doesn't it is up to the user.
        //
        // In case of existential (e.g., either is empty, then put after for before in assumptions: \exists S' @ Init)
        populateDeclList(fsbAssumptions.getZDeclList(), 
                (beforeBindings.isEmpty() ? afterBindings : beforeBindings),
                (beforeBindings.isEmpty() ? true : false));

        // get any user defined predicates
        fsbAssumptions.setPred(getUserDefinedSchemaPRE(schName, genParams));

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
            populateDeclList(fsbConclusions.getZDeclList(), afterBindings, true);

            // \forall assumptions @ \exists conclusions @ Sch
            //Pred invariant = getSchemaInvariant(schRef);//, schExpr); // try expanding the schema invariants - if fails, just use the schema reference
            result = predTransformer_.asPred(
                    predTransformer_.forAllExpr(fsbAssumptions,
                      predTransformer_.existsExpr(fsbConclusions, schRef)));
          }
          else
          {
            assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
            // create the conclusions as a Z-centric \pre SchRef operator
            // \forall SchSig | true @ \pre Sch
            result = predTransformer_.asPred(
                    predTransformer_.forAllExpr(
                      schSigSchText, factory_.createPreExpr(schRef)));
          }
          
          vcType = ZFsbVCKind.PRE;
        }
        // no after bindings; if there are any before bindings then create existential proof
        else if (!emptybindings) // before \neq {} XOR after \neq {} and it is existential
        {
          // for the state schema, if there is a init schema, then a vc \exists State' @ StInit is added in the end
          // otherwise, add the whole VC anyway as \exists State' @ true; similarly for init/fin schemas
          if (isState(STINIT, schName) 
              || isState(STFIN, schName) 
              || isState(STATE, schName)
                && (getState(STINIT) != null || getState(STFIN) != null))
          {
            result = predTransformer_.truePred();
          }
          else if (!isCreatingZSchemas())
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
          
          vcType = ZFsbVCKind.STATE;
        }
        // otherwise, there is nothing to do: just return P
        else // before = after = {}
        {
          result = predTransformer_.truePred(); // TODO: still to return P from ZName (!!!)
          vcType = ZFsbVCKind.DEFAULT;
        }
      }

      // if anything got created, add them (if the result pred is not trivial)
      if (schNameSigSchema != null && result != null && !(result instanceof TruePred))
      {
        
        // mark the handled schema as source paragraph for the signature schema
        VCSource sourceInfo = new VCSource(para);
        schNameSigSchema.getAnns().add(sourceInfo);
        
        int cnt = 0;
        AxPara old = addedSigSchemas_.put(schSigName, schNameSigSchema);
        //addedSigSchemasList_.add(schNameSigSchema);
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
        //assert addedSigSchemasList_.size() == addedSigSchemas_.size();
      }
      
      VCConfig config = createVCConfig(vcType, Precedence.AFTER);
      result.getAnns().add(config);
      
      return result;
    }
    catch (DefinitionException ex)
    {
      throw new CztException(createVCCollectionException("VC-FSB-SCHEMA-DEFEXCEPTION for " + schName, ex));
    }
  }

  /**
   * User supplied predicate to be assumed as part of the given schema name
   * @param schName
   * @param genParams
   * @return
   */
  protected Pred getUserDefinedSchemaPRE(ZName schName, ZNameList genParams)
  {
    ZName nameNoStrokes = factory_.createZName(schName.getWord());
    Definition schDef = getDefTable().lookupName(nameNoStrokes);
    Pred result = predTransformer_.truePred();
    if (schDef != null)
    {
      try
      {
        // not quite the same as calling method: it consider names without strokes (!)
        // TODO: see if we could avoid this rework
        SortedSet<Definition> mixed = getBindingsFor(nameNoStrokes);
        SortedSet<Definition> before = BindingUtils.beforeBindingsOf(mixed);
        SortedSet<Definition> after = BindingUtils.afterBindingsOf(mixed);
        assert BindingUtils.bindingsInvariant(mixed, before, after);

        // if there are no after bindings on the schema def, then add it as part
        // of the Pred part of assumptions.

        // if there are after variables, but the no before variables, this is
        // like Initialisation or existential quantification case for dashed
        // variables only schemas
        if (after.isEmpty() || before.isEmpty())
        {
          //result = factory_.createExprPred(schDef.getExpr()); ??
          //result = factory_.createExprPred(factory_.createRefExpr(nameNoStrokes));
          result = predTransformer_.asPred(predTransformer_.createSchRef(nameNoStrokes, genParams));
        }
        // else, if they are indeed mixed, then look for some user given table for any extra predicate
        // for instance the Z State schema as tagged by \zstate or \zastate (e.g., abstract only for now).
        else
        {
          // init/fin with I/O parameters
          SortedSet<Definition> inputBindings = BindingUtils.inputBindingsOf(before);
          SortedSet<Definition> outputBindings = BindingUtils.outputBindingsOf(after);
          boolean initWithInput = !after.isEmpty() && !inputBindings.isEmpty() && inputBindings.equals(before);
          boolean finWithOutput = !before.isEmpty() && !outputBindings.isEmpty() && outputBindings.equals(after);
          boolean dashedState = (initWithInput ^ finWithOutput); // both true then not the case;

          SortedSet<Definition> relevantBindings = before;
          // if just one of them is true, and that is finWithOutput, then use after
          if (dashedState && finWithOutput)
            relevantBindings = after;

          // check the bindings...: initWithInputs is just like normal cases; finWithOutput needs after bindings
          result = handleStateSchemaInUserDefinedSchemaPRE(schName, genParams,
                    relevantBindings, dashedState);

        }
      }
      catch(DefinitionException e)
      {
        // ignore and make it just true
        final String message = "Definition exception raised whilst trying to collect user defined preconditions for schema " + ZUtils.toStringZName(schName) +
                "\n---------------------------------------" + e.toString() + "\n---------------------------------------\n";
        CztLogger.getLogger(getClass()).warning(message);
      }
    }
    // just true for now.
    return result;
  }

  protected Pred handleStateSchemaInUserDefinedSchemaPRE(ZName schName, ZNameList genParams, SortedSet<Definition> relevantBindings, boolean dashedState)
  {
    Pred result = predTransformer_.truePred();
    ZName stateSchema = getState(STATE);
    ZNameList stateSchemaGenParams = getStateGenParams(STATE);
    if (stateSchema != null)
    {
      if (stateSchemaGenParams != null && genParams != null &&
          !genParams.containsAll(stateSchemaGenParams))
      {
        final String message = "Included state schema " + ZUtils.toStringZName(stateSchema) +
                " depends on generic parameters not given to schema " + ZUtils.toStringZName(schName) +
                "\n\tGiven.....: " + genParams.toString() +
                "\n\tExpected..: " + stateSchemaGenParams.toString();
        CztLogger.getLogger(getClass()).warning(message);
      }

      // if state schema is not null but init schema is okay, then check it against the state init schema
      if (isState(STINIT, schName))
      {
        // init schema has already checked the state bindings by using checkStateInfo upon assignment.
        // so, the only problem is to check whether the before bindings are inputs only
        SortedSet<Definition> inputBindings = BindingUtils.inputBindingsOf(relevantBindings);
        relevantBindings.removeAll(inputBindings);
        if (!relevantBindings.isEmpty())
        {
          final String message = "Could not generate user-defined predicate for initialisation schema " + ZUtils.toStringZName(schName) +
              " because it has invalid before bindings (e.g., only input or state bindings are valid)" +
              "\n\tGiven.....: " + String.valueOf(relevantBindings) +
              "\n\tAllowed...: " + String.valueOf(inputBindings);
          handleInclBindingsMismatch(message);
        }
      }
      else if (isState(STFIN, schName))
      {
        // init schema has already checked the state bindings by using checkStateInfo upon assignment.
        // so, the only problem is to check whether the before bindings are inputs only
        SortedSet<Definition> outputBindings = BindingUtils.outputBindingsOf(relevantBindings);
        relevantBindings.removeAll(outputBindings);
        if (!relevantBindings.isEmpty())
        {
          final String message = "Could not generate user-defined predicate for finalisation schema " + ZUtils.toStringZName(schName) +
              " because it has invalid after bindings (e.g., only output or after state bindings are valid)" +
              "\n\tGiven.....: " + String.valueOf(relevantBindings) +
              "\n\tAllowed...: " + String.valueOf(outputBindings);
          handleInclBindingsMismatch(message);
        }
      }
      else
      {
        // otherwise check the before bindings for the given schema name
        checkInclBindingsWithinGivenSchBindings(getState(STATE), schName, relevantBindings);
      }

      // if creating ZSchemas, then the name will already be within the ZDeclList
      if (!isCreatingZSchemas())
      {

        // Keep the state schema as Pred part of "OpSig == [ x, y : T | State ]", for "State = [ x, y: T | inv(x,y) ]".
        // the repetition of bindings is for both clarity of what the VCG is doing and to ensure in odd cases we do not
        // mess up the VC itself (e.g., State having more bindings than we found for OpSig will lead to a type error).
        Expr schExpr;
        if (dashedState)
          schExpr = predTransformer_.createDashedSchRef(getState(STATE), getStateGenParams(STATE));
        else
          schExpr = predTransformer_.createSchRef(getState(STATE), getStateGenParams(STATE));
        result = predTransformer_.asPred(schExpr);

      }

    }
    // else ???? TODO: let the user give schemas as string text and parser ???
    return result;
  }

   /**
   *
   * @param inclStateSchemaName concrete or abstract state schema
   * @param schName
   * @param beforeBindings
   */
  protected void checkInclBindingsWithinGivenSchBindings(ZName inclStateSchemaName, ZName schName, SortedSet<Definition> beforeBindings)
  {
    assert inclStateSchemaName != null && schName != null;
    
    // check the given mixed bindings are indeed within the remit of the state associated with it.
    SortedSet<Definition> stateBindings = computedBindings_.get(inclStateSchemaName);
    if (stateBindings == null || !beforeBindings.containsAll(stateBindings))
    {
      final String message = "Included state schema " + ZUtils.toStringZName(inclStateSchemaName) +
              " depends on bindings not declared in schema " + ZUtils.toStringZName(schName) +
              "\n\tGiven.....: " + String.valueOf(beforeBindings) +
              "\n\tExpected..: " + String.valueOf(stateBindings);
      handleInclBindingsMismatch(message);
    }
  }

  /**
   * Just log a waning on the feasibility case. On refinement case throw an exception
   * @param errorMsg
   */
  protected void handleInclBindingsMismatch(String errorMsg)
  {
    final String message = errorMsg + "\n\n\tThis might be caused by inconsistent state. Ignoring for " + getClass().getSimpleName();
    CztLogger.getLogger(getClass()).warning(message);
  }

  protected void createStateVCS(List<VC<Pred>> vcList) throws VCCollectionException
  {
    // if state inialisation is not present, we will have a VC like
    // \exists AState' @ true
    ZName stateInitSchema = getState(STINIT);
    ZName stateFinSchema = getState(STFIN);
    ZName stateSchema = getState(STATE);
    ZNameList stateSchemaGenParams = getStateGenParams(STATE);
    
    if (stateInitSchema != null)
    {
      if (stateSchema == null)
        throw createVCCollectionException("Cannot create state initialisation VC for state initialisation schema " + stateInitSchema +
                " because there is no state schema name assigned");

      Expr stateDash = predTransformer_.createDashedSchRef(stateSchema, stateSchemaGenParams);
      Expr stateInit = predTransformer_.createSchRef(stateInitSchema, stateSchemaGenParams);
      Pred initVC = predTransformer_.createStateInitialisationVC(stateDash, stateInit);

      addStateVC(vcList, getStateSchema(STINIT), initVC, ZFsbVCKind.INIT);
    }
    if (stateFinSchema != null)
    {
      if (stateSchema == null)
        throw createVCCollectionException("Cannot create state finalisation VC for state initialisation schema " + stateFinSchema +
                " because there is no state schema name assigned");

      Expr state    = predTransformer_.createSchRef(stateSchema, stateSchemaGenParams);
      Expr stateFin = predTransformer_.createSchRef(stateFinSchema, stateSchemaGenParams);
      Pred finVC    = predTransformer_.createStateFinalisationVC(state, stateFin);

      addStateVC(vcList, getStateSchema(STFIN), finVC, ZFsbVCKind.FIN);
    }
  }

  private void addStateVC(List<VC<Pred>> vcList, AxPara para, Pred pred, ZFsbVCKind kind) 
      throws VCCollectionException
  {
    assert para != null;
    
    pred.getAnns().add(new VCConfig(kind.getTypeId(), Precedence.AFTER, getStateGenParams(STATE)));
    
    stepVCCounter();
    VC<Pred> initStateVC = createVC(getVCCount(), para, VCType.NONE, pred);
    vcList.add(initStateVC);
  }

  private DefinitionComparator definitionComparatorIgnoringStrokes_ = new DefinitionComparator(true);

  protected boolean bindingsSubsetEq(SortedSet<Definition> LHS, SortedSet<Definition> RHS, boolean dashed)
  {
    if (!dashed)
      return LHS.containsAll(RHS);
    else
    {
      // change the comparator to ignore strokes
      SortedSet<Definition> lhs = new TreeSet<Definition>(definitionComparatorIgnoringStrokes_);
      lhs.addAll(LHS);
      // if considering dashed bindings, then ignore dash for comparison
      for (Definition e : RHS)
        if (!lhs.contains(e))
         return false;
      return true;
    }
  }

  protected boolean bindingsRemoveAll(SortedSet<Definition> LHS, SortedSet<Definition> RHS, boolean dashed)
  {
    if (!dashed)
      return LHS.removeAll(RHS);
    else
    {
      // change the comparator to ignore strokes
      SortedSet<Definition> rhs = new TreeSet<Definition>(definitionComparatorIgnoringStrokes_);
      rhs.addAll(RHS);

      // if considering dashed bindings, then ignore dash for comparison
      boolean modified = false;
      Iterator<Definition> it = LHS.iterator();
      while (it.hasNext()) 
      {
        if (rhs.contains(it.next()))
        {
          // affects the LHS from caller.
          it.remove();
          modified = true;
        }
      }
      it = null;
      return modified;
    }
  }

  protected void populateDeclList(ZDeclList zDeclList, SortedSet<Definition> bindings, boolean dashed)
  {
    if (bindings.isEmpty())
    { 
      //throw new CztException(new FeasibilityException("Invalid (empty) bindings to populate ZDeclList of current name " + currentName_));
      CztLogger.getLogger(getClass()).log(Level.WARNING, "Empty bindings to populate ZDeclList of current name {0}", currentName_);
      return;
    }
    assert !bindings.isEmpty();
    List<Decl> decls = factory_.list();
    if (isCreatingZSchemas())
    {
      // look for known bindings packed up as schema names
      Iterator<Map.Entry<ZName, SortedSet<Definition>>> it = computedBindings_.entrySet().iterator();
      while (it.hasNext() && !bindings.isEmpty())
      {
        Map.Entry<ZName, SortedSet<Definition>> entry = it.next();
        SortedSet<Definition> knownBindings = entry.getValue();
        // if all bindings from the known set is within bindings given
        // then add the name as an inclusion to the declaration list
        if (bindingsSubsetEq(bindings, knownBindings, dashed))
        {
          bindingsRemoveAll(bindings, knownBindings, dashed);
          
          // TODO: generic params properly - for now consider only abstract state ones.
          // "properly means going through all the generic params in the bindings given
          // to see whether they are contained within the state or concrete state ones.
          Expr schExpr = dashed ? predTransformer_.createDashedSchRef(entry.getKey(), getStateGenParams(STATE)) :
                                        predTransformer_.createSchRef(entry.getKey(), getStateGenParams(STATE));
          InclDecl id = factory_.createInclDecl(schExpr);
          decls.add(id);
        }
      }
      it = null;
    }

    // process any remaining bindings
    if (!bindings.isEmpty())
    {
      Iterator<Definition> it = bindings.iterator();

      // process the first one
      Definition currentBinding = it.hasNext() ? it.next() : null;
      ZName currentName = currentBinding != null ? currentBinding.getDefName() : null;
      Expr currentExpr;
      VarDecl currentVarDecl = null;
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
      it = null;
    }

    // update the decl list with created bindings as either VarDecl or InclDecl
    zDeclList.addAll(decls);
  }
}
