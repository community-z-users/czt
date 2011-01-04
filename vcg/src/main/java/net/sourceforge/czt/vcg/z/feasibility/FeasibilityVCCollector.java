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

import java.util.List;
import java.util.Set;
import net.sourceforge.czt.vcg.util.DefinitionTable;
import net.sourceforge.czt.vcg.util.DefinitionTable.Definition;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.ZBranchList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.vcg.z.TermTransformer;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.transformer.ZPredTransformer;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.util.ZUtils;

import net.sourceforge.czt.z.visitor.AxParaVisitor;

import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.visitor.BranchVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.ZBranchListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;

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

  /**
   * Definition table containing declared types of names. This is important
   * to query known names to see weather they are partial functions that
   * require domain check predicates or not.
   */
  private DefinitionTable defTable_;
  private ZPredTransformer predTransformer_;

  private boolean nonEmptyGivenSets_;
  
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
    defTable_ = null;    
    predTransformer_ = new ZPredTransformer(factory, this);
    nonEmptyGivenSets_ = PROP_VCG_FEASIBILITY_NONEMPTY_GIVENSETS_DEFAULT;
    predTransformer_.setApplyTransformer(PROP_VCG_FEASIBILITY_APPLY_TRANSFORMERS_DEFAULT);
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

  protected final void setNonemptyGivenSetVC(boolean value)
  {
    nonEmptyGivenSets_ = value;
  }

  /** VC COLLECTOR METHODS */

  @Override
  protected VCType getVCType(Pred vc) throws VCCollectionException
  {
    VCType result = vc.getAnn(VCType.class);
    if (result == null)
      result = VCType.NONE;
    return result;
  }

  @Override
  public VC<Pred> createVC(Para term, VCType type, Pred vc) throws VCCollectionException
  {
    return new FeasibilityVC(term, type, vc);
  }

  @Override
  protected void beforeCalculateVC(Term term, List<? extends InfoTable> tables)
          throws VCCollectionException
  {
    defTable_ = null; // a null dts means always "applies$to", rather than \in \dom~? when possible
    for (InfoTable tbl : tables)
    {
      if (tbl instanceof DefinitionTable)
      {
        defTable_ = (DefinitionTable)tbl;
      }
    }
  }

  @Override
  protected void afterCalculateVC(VC<Pred> vc) throws VCCollectionException
  {
    defTable_ = null;
  }

  @Override
  protected Pred calculateVC(Para term) throws VCCollectionException
  {
    return visit(term);
  }

  /** PARAGRAPH VISITING METHODS */

  /**
   * Calculates DC for given term (i.e. visits term). As some Z productions have
   * null terms, like AxPara \begin{axdef} x: \nat \end{axdef} has null predicate,
   * implementations should take care of such situations accordingly. For null terms
   * in this collector, we presume a harmless DC condition (e.g., true).
   * @param term
   * @return
   */
  @Override
  public Pred visit(Term term)
  {
    if (term == null)
    {
      // for null terms, warn, but assume harmless (E.g., no VCs to be generated)
      SectionManager.traceLog("VCG-FSBCOL-NULL-TERM");
      return predTransformer_.truePred();
    }
    else
    {
      return predTransformer_.visit(term);
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
                    factory_.createRefExpr(name), factory_.createSetExpr()));
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
    return visit(ZUtils.assertZBranchList(term.getBranchList()));
  }

  /** DC a list of Branch from a Freetype */
  @Override
  public Pred visitZBranchList(ZBranchList term)
  {
    return predTransformer_.andPredList(term);
  }

  /** DC the expression E on a Freetype branch  "b \ldata E \rdata" as "DC(E)". */
  @Override
  public Pred visitBranch(Branch term)
  {
    // constructors need dc, names don't
    if (term.getExpr() != null)
    {
      return predTransformer_.truePred();
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
    switch (term.getBox())
    {
      case AxBox:
        // for AxBox (axdef and gendef), use getAxBoxXXX methods
        ZDeclList decl = ZUtils.getAxBoxDecls(term);
        Pred pred = ZUtils.getAxBoxPred(term);

        Pred dcd = visit(decl); // DC(D)
        Pred dcp = visit(pred); // DC(P)

        // DC(D) \land (\forall D @ DC(P))
        return predTransformer_.andPred(dcd, predTransformer_.forAllPred(decl, dcp));

      case SchBox:
        // for schemas add\
        Name schName = ((ConstDecl)term.getZSchText().getZDeclList().get(0)).getName();
        try
        {
          Set<Definition> bindings = defTable_.bindings(schName);

        }
        catch (DefinitionTable.DefinitionException ex)
        {
          throw new CztException(new VCCollectionException(ex));
        }


        // for SchBox (schema), use use getSchDefExpr methods
        Expr schExpr = ZUtils.getSchemaDefExpr(term);

        // for SchBox, expr must be an SchExpr! Well-formed/parsed ASTs should never suffer from this.
        if (!(schExpr instanceof SchExpr))
          throw new CztException(new VCCollectionException("VC-DC-COL-APPLEXPR-NOSCHEXPR = " + term));
        //assert (schExpr instanceof SchExpr) : "Invalid SchBox AxPara, no SchExpr within ConstDecl!";

        // for SchBox : DC([ D | P ]) \iff DC(D) \land (\forall D @ DC(P)), which comes from ZSchText DC in SchExpr ;)
        return visit(schExpr);

      case OmitBox:
        // for OmitBox (horiz. def or abbreviations), use getSchemaDefExpr method
        // This can be either a SchExpr (for horizontal definitions) or other abbreviation.

        // If this is a SchExpr...
        Expr horizExpr = ZUtils.getSchemaDefExpr(term);
        // or else it is an abbreviation
        if (horizExpr == null)
          horizExpr = ZUtils.getAbbreviationExpr(term);

        if (horizExpr == null)
          throw new CztException(new VCCollectionException("VC-DC-COL-APPLEXPR-NULL-HORIZEXPR = " + term));
        //assert horizExpr != null : "Invalid horizontal definition: neither schema construction, nor abbreviation (null)!";

        // for OmitBox: DC(n[X] == E) \iff DC(E), where E could be a SchExpr ([ D | P])
        return visit(horizExpr);

      default:
        // this case should never happen, yet we need to return something
        // in the unlikely case the Java compiler messes up with Box Enums
        // (i.e. corrupted byte code classes)!
        throw new AssertionError("Invalid Box for AxPara! " + term.getBox());
    }
  }
}
