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

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.logging.Level;
import java.util.logging.Logger;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.vcg.util.BindingFilter;
import net.sourceforge.czt.vcg.util.BindingUtils;
import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.util.DefinitionException;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCConfig;
import net.sourceforge.czt.vcg.z.VCConfig.Precedence;
import net.sourceforge.czt.vcg.z.VCSource;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateAnn;
import net.sourceforge.czt.vcg.z.feasibility.util.ZStateInfo;
import net.sourceforge.czt.vcg.z.refinement.util.ZRefinesAnn;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Box;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author leo
 * @since Jan 02, 2011
 */
public class FeasibilityVCCollector extends 
	AbstractFeasibilityVCCollector<SchemaType, SortedSet<Definition>> //implements
  //GivenParaVisitor<Pred>,
  //FreeParaVisitor<Pred>,
  //AxParaVisitor<Pred>,
  //ZFreetypeListVisitor<Pred>,
  //FreetypeVisitor<Pred>,
  //ZBranchListVisitor<Pred>,
  //BranchVisitor<Pred>,
  //FeasibilityPropertyKeys
{
	private ZName currentName_;
	private final ZName setInterName_;
	private final ZName freeTypeCtorOpName_;

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
    
    setVCGContext(new FeasibilityVCGContext());
    currentName_ = null;
	setInterName_ = getFactory().createZName(ZString.ARG_TOK + ZString.CAP
			+ ZString.ARG_TOK);
	freeTypeCtorOpName_ = getFactory().createZName(ZString.ARG_TOK
			+ ZString.INJ + ZString.ARG_TOK);
  }
  
  
//  @Override
//  public VCGContext<SchemaType, SortedSet<Definition>> getVCGContext()
//  {
//	  return super.getVCGContext();
//  }
  
  public FeasibilityVCGContext getFSBVCGContext()
  {
	  return (FeasibilityVCGContext)getVCGContext();
  }
  
  protected final void setStateSchema(ZStateInfo stateInfo, ZName n, AxPara para, ZNameList genParams)
  {
    setStateName(stateInfo, n);
    getFSBVCGContext().getStateSchemas().put(stateInfo, para);
    setStateGenParams(stateInfo, genParams);
  }
  
  protected final void setStateName(ZStateInfo type, ZName n) {
    getFSBVCGContext().getStateSchemaNames().put(type, n);
  }

  public ZName getStateName(ZStateInfo type)
  {
    return getFSBVCGContext().getStateSchemaNames().get(type);
  }
  
  protected AxPara getStateSchema(ZStateInfo type) {
    return getFSBVCGContext().getStateSchemas().get(type);
  }
  
  protected ZNameList getStateGenParams(ZStateInfo type)
  {
    return getFSBVCGContext().getStateGenParams().get(type);
  }
  
  protected void setStateGenParams(ZStateInfo type, ZNameList genParams)
  {
	  getFSBVCGContext().getStateGenParams().put(type, genParams);
  }
  
  protected void checkZStateInfo(AxPara para)
  {
    if (para.hasAnn(ZStateAnn.class))
    {
      ZStateAnn zsi = para.getAnn(ZStateAnn.class);
      ZStateInfo zsii = zsi.getInfo();
      ZName name = getStateName(zsii);
      // take into account the common names for state and init when doing refinement
      if (name == null)
      {
        if (zsii.equals(ZStateInfo.ASTATE))
          name = getStateName(ZStateInfo.STATE);
        else if (zsii.equals(ZStateInfo.STATE))
          name = getStateName(ZStateInfo.ASTATE);
        else if (zsii.equals(ZStateInfo.ASTINIT))
          name = getStateName(ZStateInfo.STINIT);
        else if (zsii.equals(ZStateInfo.STINIT))
          name = getStateName(ZStateInfo.ASTINIT);
        else if (zsii.equals(ZStateInfo.ASTFIN))
          name = getStateName(ZStateInfo.STFIN);
        else if (zsii.equals(ZStateInfo.STFIN))
          name = getStateName(ZStateInfo.ASTFIN);
      }

      if (name == null && para.getBox().equals(Box.SchBox))
      {
        name = ZUtils.assertZName(ZUtils.getSchemaName(para));
        Name old = getFSBVCGContext().getStateSchemaNames().put(zsi.getInfo(), name);
        assert old == null;
      }
      // bad format or missing name
      else
      {
        Name other = ZUtils.getAxParaSchOrAbbrName(para);
        if (!ZUtils.namesEqual(name, other))
        { 
          //Object[] params = new Object[]
          //        {
          //          para, zsi, name, other
          //        };
          //error(para, ErrorMessage.ZSTATEINFO_INCONSISTENCY, params);
        }
      }
    }
    else if (para.hasAnn(ZRefinesAnn.class))
    {
      ZRefinesAnn zra = para.getAnn(ZRefinesAnn.class);
      //Name abstractName = zra.getAbstractName();
      //Type2 absType = unwrapType(getType(abstractName));
      //if (!(absType instanceof PowerType &&
      //    ((PowerType)absType).getType() instanceof SchemaType))
      //{
      //  // this error might happen if the abstract name within \zrefines{AbsName}
      //  // isn't declared within the specification where the concrete name appears
      //  error(para, ErrorMessage.ZREFINES_UNKNOWN_ABSNAME, new Object[] { para, abstractName, absType} );
      //}

      Name concreteName = zra.getConcreteName();
      Name paraName = ZUtils.getAxParaSchOrAbbrName(para);
      boolean namesEqual = ZUtils.namesEqual(paraName, concreteName);
      // paraName and concreteName differ or if not for a SchBox
      if (!namesEqual || !para.getBox().equals(Box.SchBox))
      {
        //Object[] params = new Object[]
        //          {
        //            para, abstractName, concreteName, paraName
        //          };
        // given the parser assigns the concrete name, this error can only
        // happen if the ZRefinesAnn AST is created manually
        //error(para, ErrorMessage.ZREFINES_INCONSISTENCY, params);
        Logger.getLogger(getClass().getName()).warning("ZREFINES_INCONSISTENCY");  
      }
    }
  }

  /** PARAGRAPH VISITING METHODS */

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
      result = getPredTransformerFSB().truePred();
      for (Name name : term.getNames())
      {
        Pred vc = getFactory().createNegPred(getFactory().createEquality(
                    getFactory().createRefExpr(name),
                    getFactory().createSetExpr(getFactory().createZExprList())));
        vc.getAnns().add(VCType.AXIOM);
        result = getPredTransformerFSB().andPred(result, vc);
      }
    }
    else
    {
      result = getPredTransformerFSB().truePred();
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
    return getPredTransformerFSB().andPredList(term);
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
    return getPredTransformerFSB().andPredList(term);
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
      Expr ftExpr = getFactory().createGenOpApp(freeTypeCtorOpName_,
              getFactory().list(term.getExpr(), getFactory().createRefExpr(currentName_)));
      // FT ::= f \ldata E \rdata ==> add: f \in E \inj FT
      Pred result = getFactory().createMemPred(term.getName(), ftExpr);
      result.getAnns().add(VCType.RULE);
      return result;
    }
    else
    {
      return getPredTransformerFSB().truePred();
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
   * This covers the Z/EVES domain check rules for:
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
        
        ZStateInfo type;
        BindingFilter filter;
        
        switch (zsi) {
          case STATE:
          case ASTATE:
            type = ZStateInfo.STATE;
            filter = BindingUtils.STATE_FILTER;
            break;
          case STINIT:
          case ASTINIT:
            type = ZStateInfo.STINIT;
            filter = BindingUtils.INIT_FILTER;
            break;
          case STFIN:
          case ASTFIN:
            type = ZStateInfo.STFIN;
            filter = BindingUtils.FIN_FILTER;
            break;
          default:
            type = null;
            filter = null;
            break;
        }
        
        if (type != null) {
          markStateSchema(term, termDefName, termDefGenParams, zsi.getDescription(), type, filter);
          result = true;
        }
      }

    }
    else if (isState(ZStateInfo.STATE, termDefName)) {
      setStateGenParams(ZStateInfo.STATE, termDefGenParams);
    }
    return result;
  }
  
  protected void markStateSchema(AxPara term, ZName termDefName, ZNameList termDefGenParams,
      final String prefixMsg, ZStateInfo type, BindingFilter filter)
  {

    checkPreviousState(prefixMsg, getStateName(type), termDefName);
    setStateSchema(type, termDefName, term, termDefGenParams);
    checkStateBindings(prefixMsg, termDefName, filter);
  }
  
  protected boolean isState(ZStateInfo type, ZName termDefName)
  {
    ZName stateSchema = getStateName(type);
    return stateSchema != null && ZUtils.namesEqual(termDefName, stateSchema);
  }


  /* VC GENERATION HELPER METHODS */

  // FSB(AX D | P ) => \exists D | true @ P
  protected Pred handleAxiom(ZSchText zSchText)
  {
    Pred pred = zSchText.getPred();
    Pred result = getPredTransformerFSB().existsPred(zSchText.getZDeclList(), pred == null ? truePred() : pred);
    
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
      expr = getFactory().createSetExpr(getFactory().createZExprList(getFactory().list(expr)));
    }
    Pred result = getPredTransformerFSB().existsPred(getFactory().createZDeclList(
            getFactory().list(getFactory().createVarDecl(getFactory().createZNameList(getFactory().list(horizDef.getDefName())), expr))), truePred());
    
    // horizontal definitions have BEFORE precedence - they need to be proved before the 
    // horizontal definition is stated, otherwise it may be used to prove the VC
    result.getAnns().add(createVCConfig(ZFsbVCKind.HORIZ_DEF, Precedence.BEFORE));
    
    return result;
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
    Expr schRef = getPredTransformerFSB().createSchRef(schName, genParams);
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
      ZSchText fsbAssumptions = getFactory().createZSchText(getFactory().createZDeclList(), getFactory().createTruePred());

      if (isCreatingZSchemas())
      {
        // create a signature schema name + ref expr from current schema, considering its generic params
        schSigName = getSigSchemaName(schName);
        schSigRef = getPredTransformerFSB().createSchRef(schSigName, genParams);

        // create a ZSchText with the schSigRef (e.g., [ SchNameSig | true ]), as well as an AxPara
        // as SchNameSig == [ before + inputs | P ], where P = getUserDefinedSchemaPRE
        schSigSchText = getPredTransformerFSB().createSchemaInclusion(schSigRef);
        schNameSigSchema = getPredTransformerFSB().createSchExpr(genParams, schSigName, fsbAssumptions);
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
          if (isState(ZStateInfo.STINIT, schName) 
              || isState(ZStateInfo.STFIN, schName) 
              || isState(ZStateInfo.STATE, schName)
                && (getStateName(ZStateInfo.STINIT) != null || getStateName(ZStateInfo.STFIN) != null))
          {
            result = getPredTransformerFSB().truePred();
          }
          else if (!isCreatingZSchemas())
          {
            // fsbAssumptions will have either initialisation or just true
            result = getPredTransformerFSB().existsPred(fsbAssumptions, getFactory().createTruePred());
          }
          else
          {
            // z centric existential proof
            // \exists SchSig @ true
            assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
            result = getPredTransformerFSB().existsPred(schSigSchText, getFactory().createTruePred());
          }
          
          vcType = ZFsbVCKind.STATE;
        }
        // otherwise, there is nothing to do: just return P
        else 
        {
          result = getPredTransformerFSB().truePred(); // TODO: still to return P from ZName (!!!)
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
            ZSchText fsbConclusions = getFactory().createZSchText(getFactory().createZDeclList(), getFactory().createTruePred());
            // conclusions = [ d1', ... dn', do!: T | true ]
            populateDeclList(fsbConclusions.getZDeclList(), afterBindings, true);

            // \forall assumptions @ \exists conclusions @ Sch
            //Pred invariant = getSchemaInvariant(schRef);//, schExpr); // try expanding the schema invariants - if fails, just use the schema reference
            result = getPredTransformerFSB().asPred(
                    getPredTransformerFSB().forAllExpr(fsbAssumptions,
                      getPredTransformerFSB().existsExpr(fsbConclusions, schRef)));
          }
          else
          {
            assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
            // create the conclusions as a Z-centric \pre SchRef operator
            // \forall SchSig | true @ \pre Sch
            result = getPredTransformerFSB().asPred(
                    getPredTransformerFSB().forAllExpr(
                      schSigSchText, getFactory().createPreExpr(schRef)));
          }
          
          vcType = ZFsbVCKind.PRE;
        }
        // no after bindings; if there are any before bindings then create existential proof
        else if (!emptybindings) // before \neq {} XOR after \neq {} and it is existential
        {
          // for the state schema, if there is a init schema, then a vc \exists State' @ StInit is added in the end
          // otherwise, add the whole VC anyway as \exists State' @ true; similarly for init/fin schemas
          if (isState(ZStateInfo.STINIT, schName) 
              || isState(ZStateInfo.STFIN, schName) 
              || isState(ZStateInfo.STATE, schName)
                && (getStateName(ZStateInfo.STINIT) != null || getStateName(ZStateInfo.STFIN) != null))
          {
            result = getPredTransformerFSB().truePred();
          }
          else if (!isCreatingZSchemas())
          {
            // fsbAssumptions will have either initialisation or just true
            result = getPredTransformerFSB().existsPred(fsbAssumptions, getFactory().createTruePred());
          }
          else
          {
            // z centric existential proof
            // \exists SchSig @ true
            assert schSigName != null && schSigRef != null && schSigSchText != null && schNameSigSchema != null;
            result = getPredTransformerFSB().existsPred(schSigSchText, getFactory().createTruePred());
          }
          
          vcType = ZFsbVCKind.STATE;
        }
        // otherwise, there is nothing to do: just return P
        else // before = after = {}
        {
          result = getPredTransformerFSB().truePred(); // TODO: still to return P from ZName (!!!)
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
          getLogger().warning(message.toString());
        }
        //assert addedSigSchemasList_.size() == addedSigSchemas_.size();
      }
      
      VCConfig config = createVCConfig(vcType, Precedence.AFTER);
      if (config == null) throw new DefinitionException(getDialect(), "Couldn't create VC configuration for FSB schema");
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
    ZName nameNoStrokes = getFactory().createZName(schName.getWord());
    Definition schDef = getDefTable().lookupName(nameNoStrokes);
    Pred result = getPredTransformerFSB().truePred();
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
          //result = getFactory().createExprPred(schDef.getExpr()); ??
          //result = getFactory().createExprPred(getFactory().createRefExpr(nameNoStrokes));
          result = getPredTransformerFSB().asPred(getPredTransformerFSB().createSchRef(nameNoStrokes, genParams));
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
        getLogger().warning(message);
      }
    }
    // just true for now.
    return result;
  }

  protected Pred handleStateSchemaInUserDefinedSchemaPRE(ZName schName, ZNameList genParams, SortedSet<Definition> relevantBindings, boolean dashedState)
  {
    Pred result = getPredTransformerFSB().truePred();
    ZName stateSchema = getStateName(ZStateInfo.STATE);
    ZNameList stateSchemaGenParams = getStateGenParams(ZStateInfo.STATE);
    if (stateSchema != null)
    {
      if (stateSchemaGenParams != null && genParams != null &&
          !genParams.containsAll(stateSchemaGenParams))
      {
        final String message = "Included state schema " + ZUtils.toStringZName(stateSchema) +
                " depends on generic parameters not given to schema " + ZUtils.toStringZName(schName) +
                "\n\tGiven.....: " + genParams.toString() +
                "\n\tExpected..: " + stateSchemaGenParams.toString();
        getLogger().warning(message);
      }

      // if state schema is not null but init schema is okay, then check it against the state init schema
      if (isState(ZStateInfo.STINIT, schName))
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
      else if (isState(ZStateInfo.STFIN, schName))
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
        checkInclBindingsWithinGivenSchBindings(getStateName(ZStateInfo.STATE), schName, relevantBindings);
      }

      // if creating ZSchemas, then the name will already be within the ZDeclList
      if (!isCreatingZSchemas())
      {

        // Keep the state schema as Pred part of "OpSig == [ x, y : T | State ]", for "State = [ x, y: T | inv(x,y) ]".
        // the repetition of bindings is for both clarity of what the VCG is doing and to ensure in odd cases we do not
        // mess up the VC itself (e.g., State having more bindings than we found for OpSig will lead to a type error).
        Expr schExpr;
        if (dashedState)
          schExpr = getPredTransformerFSB().createDashedSchRef(getStateName(ZStateInfo.STATE), getStateGenParams(ZStateInfo.STATE));
        else
          schExpr = getPredTransformerFSB().createSchRef(getStateName(ZStateInfo.STATE), getStateGenParams(ZStateInfo.STATE));
        result = getPredTransformerFSB().asPred(schExpr);

      }

    }
    // else ???? TODO: let the user give schemas as string text and parser ???
    return result;
  }

  protected void createStateVCS(List<VC<Pred>> vcList) throws VCCollectionException
  {
    // if state inialisation is not present, we will have a VC like
    // \exists AState' @ true
    ZName stateInitSchema = getStateName(ZStateInfo.STINIT);
    ZName stateFinSchema = getStateName(ZStateInfo.STFIN);
    ZName stateSchema = getStateName(ZStateInfo.STATE);
    ZNameList stateSchemaGenParams = getStateGenParams(ZStateInfo.STATE);
    
    if (stateInitSchema != null)
    {
      if (stateSchema == null)
        throw createVCCollectionException("Cannot create state initialisation VC for state initialisation schema " + stateInitSchema +
                " because there is no state schema name assigned");

      Expr stateDash = getPredTransformerFSB().createDashedSchRef(stateSchema, stateSchemaGenParams);
      Expr stateInit = getPredTransformerFSB().createSchRef(stateInitSchema, stateSchemaGenParams);
      Pred initVC = getPredTransformerFSB().createStateInitialisationVC(stateDash, stateInit);

      addStateVC(vcList, getStateSchema(ZStateInfo.STINIT), initVC, ZFsbVCKind.INIT);
    }
    if (stateFinSchema != null)
    {
      if (stateSchema == null)
        throw createVCCollectionException("Cannot create state finalisation VC for state initialisation schema " + stateFinSchema +
                " because there is no state schema name assigned");

      Expr state    = getPredTransformerFSB().createSchRef(stateSchema, stateSchemaGenParams);
      Expr stateFin = getPredTransformerFSB().createSchRef(stateFinSchema, stateSchemaGenParams);
      Pred finVC    = getPredTransformerFSB().createStateFinalisationVC(state, stateFin);

      addStateVC(vcList, getStateSchema(ZStateInfo.STFIN), finVC, ZFsbVCKind.FIN);
    }
  }

  private void addStateVC(List<VC<Pred>> vcList, AxPara para, Pred pred, ZFsbVCKind kind) 
      throws VCCollectionException
  {
    assert para != null;
    
    pred.getAnns().add(new VCConfig(kind.getTypeId(), Precedence.AFTER, getStateGenParams(ZStateInfo.STATE)));
    
    stepVCCounter();
    VC<Pred> initStateVC = createVC(getVCCount(), para, VCType.NONE, pred);
    vcList.add(initStateVC);
  }


  protected void populateDeclList(ZDeclList zDeclList, SortedSet<Definition> bindings, boolean dashed)
  {
    if (bindings.isEmpty())
    { 
      //throw new CztException(new FeasibilityException("Invalid (empty) bindings to populate ZDeclList of current name " + currentName_));
      getLogger().log(Level.WARNING, "Empty bindings to populate ZDeclList of current name {0}", currentName_);
      return;
    }
    assert !bindings.isEmpty();
    List<Decl> decls = getFactory().list();
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

          // NOTE: for knownBindings that are already all dashed, and if dashed is true, then no point in adding refExpr dashed.
          //       will force not adding SInit~' inclusion, where SInit already has all dashed that is necessary in the case where 
          //       the user didn't provide a state schema to guide the population of declarations.
          //
          //       that is, if all bindings are accounted for by the known bindings, then we need to add a ref to its key
          //       if all known bindings are dashed, then no need to add the InclDecl with dash again. Otherwise, we do...
          if (dashed && bindings.isEmpty())
          {
            SortedSet<Definition> state  = BindingUtils.stateBindingsOf(knownBindings);

            // if all known bindings are state bindings (no after, no input, no output), then add the dash
            // otherwise, the inclusion isn't right with dashes
            dashed = state.equals(knownBindings);

            if (!dashed)
            {
              // if state bindings aren't all known ones, check dashed bindings.
              SortedSet<Definition> dashedBindings = BindingUtils.dashedBindingsOf(knownBindings);

              // if dashed=known, then all is okay and no need for extra dash on inclusion
              dashed = !dashedBindings.equals(knownBindings);
              
              // otherwise, there are mixed bindings around or I/O...
              if (dashed)
              {
                SortedSet<Definition> io  = BindingUtils.inputBindingsOf(knownBindings);
                io.addAll(BindingUtils.outputBindingsOf(knownBindings));

                // if just IO then no need for dash
                dashed = !io.equals(knownBindings);

                // there are mixed bindings
                if (dashed)
                {
  //              SortedSet<Definition> after  = BindingUtils.afterBindingsOf(knownBindings);
  //              SortedSet<Definition> before = BindingUtils.beforeBindingsOf(knownBindings);
  //
  //              boolean initWithInput = !after.isEmpty() && !input.isEmpty() && input.equals(before);
  //              boolean finWithOutput = !before.isEmpty() && !output.isEmpty() && output.equals(after);
                  final String message = "Could not completely infer the (mixed) inclusion bindings for " + entry.getKey() + "; adding dashed inclusion...";
                  CztLogger.getLogger(getClass()).warning(message);
                }
              }
            }
          }

          Expr schExpr = dashed ? getPredTransformerFSB().createDashedSchRef(entry.getKey(), getStateGenParams(ZStateInfo.STATE)) :
                                        getPredTransformerFSB().createSchRef(entry.getKey(), getStateGenParams(ZStateInfo.STATE));
          InclDecl id = getFactory().createInclDecl(schExpr);
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
        currentVarDecl = getFactory().createVarDecl(getFactory().createZNameList(getFactory().list(currentName)), currentExpr);
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
          currentVarDecl.setExpr(getFactory().createFunOpAppl(setInterName_, getFactory().createTupleExpr(currentVarDecl.getExpr(), currentExpr)));
        }
        // otherwise create a new expression
        else
        {
          currentVarDecl = getFactory().createVarDecl(getFactory().createZNameList(getFactory().list(currentName)), currentExpr);
          decls.add(currentVarDecl);
        }

      }
      it = null;
    }

    // update the decl list with created bindings as either VarDecl or InclDecl
    zDeclList.addAll(decls);
  }
}
