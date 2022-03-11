/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

package net.sourceforge.czt.rules.prover;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.oracles.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;
import net.sourceforge.czt.zpatt.visitor.*;

/**
 * Utility methods for proving and rewriting.
 *
 * @author Petra Malik
 */
public final class ProverUtils
{
  public static Factory FACTORY = new Factory(new ProverFactory());
  public static Map<String,AbstractOracle> ORACLES = createOracleMap();

  /**
   * Copies the given predicate using the CopyVisitor (which makes
   * sure that unification works) and creates a Sequent with that
   * predicate.
   */
  public static Sequent createSequent(Pred pred, boolean copy)
  {
    if (copy) {
      CopyVisitor copyVisitor = new CopyVisitor(FACTORY);
      pred = (Pred) pred.accept(copyVisitor);
    }
    Sequent sequent = FACTORY.createSequent();
    sequent.setPred(pred);
    return sequent;
  }

  public static Sequent createSequent(Expr expr, boolean copy)
  {
    Pred pred = FACTORY.createExprPred(expr);
    return createSequent(pred, copy);
  }

  public static Sequent createRewriteSequent(Expr expr, boolean copy)
  {
    ProverJokerExpr joker = (ProverJokerExpr)
      new Factory(new ProverFactory()).createJokerExpr("_", null);
    Pred pred = FACTORY.createEquality(expr, joker);
    return createSequent(pred, copy);
  }

  public static Sequent createRewriteSequent(Pred pred, boolean copy)
  {
    ProverJokerPred joker = (ProverJokerPred)
      new Factory(new ProverFactory()).createJokerPred("_", null);
    return createSequent(FACTORY.createIffPred(pred, joker), copy);
  }

  public static Sequent createRewriteSequent(SchText schText,
                                             boolean copy)
  {
    ProverJokerExpr joker = (ProverJokerExpr)
      new Factory(new ProverFactory()).createJokerExpr("_", null);
    Expr original = FACTORY.createSchExpr(schText);
    TupleExpr pair = FACTORY.createTupleExpr(original, joker);
    String schemaEqOp = ZString.ARG_TOK + "schemaEquals" + ZString.ARG_TOK;
    StrokeList noStrokes = FACTORY.createZStrokeList();
    ZName name = FACTORY.createZName(schemaEqOp, noStrokes, "global");
    RefExpr schemaEquals = FACTORY.createRefExpr(name);
    Pred pred = FACTORY.createMemPred(pair, schemaEquals, Boolean.TRUE);
    return createSequent(pred, copy);
  }

  /**
   * Resets all the bindings in the collection.
   *
   * @throws NullPointerException if one of the bindings is <code>null</code>.
   */
  public static void reset(Collection<Binding> bindings)
  {
    if (bindings != null) {
      for (Binding binding : bindings) {
        binding.reset();
      }
    }
  }

  public static List<ConjPara> collectConjectures(Term term)
  {
    List<ConjPara> result = new ArrayList<ConjPara>();
    if (term instanceof Spec) {
      for (Sect sect : ((Spec) term).getSect()) {
        if (sect instanceof ZSect) {
          ZSect zsect = (ZSect) sect;
          for (Para para : ZUtils.assertZParaList(zsect.getParaList())) {
            if (para instanceof ConjPara) {
              result.add((ConjPara) para);
            }
          }
        }
      }
    }
    return result;
  }

  public static void collectBindings(Sequent sequent, List<Binding> list)
  {
    Deduction ded = sequent.getAnn(Deduction.class);
    if (ded == null) return;
    if (ded instanceof RuleAppl) {
      RuleAppl ruleAppl = (RuleAppl) ded;
      list.addAll(ruleAppl.getBinding());
      for (Sequent s : ruleAppl.getSequentList()) {
        collectBindings(s, list);
      }
    }
    else if (ded instanceof OracleAppl) {
      OracleAppl oracleAppl = (OracleAppl) ded;
      list.addAll(oracleAppl.getBinding());
      if (oracleAppl.getOracleAnswer() instanceof CheckPassed) {
        CheckPassed passed = (CheckPassed) oracleAppl.getOracleAnswer();
        list.addAll(passed.getBinding());
      }
    }
  }

  public static List<Joker> collectJokers(Term term)
  {
    JokerCollector collector = new JokerCollector();
    term.accept(collector);
    return collector.getResult();
  }

  public static void printJokers(Term term)
  {
    for (Joker joker : collectJokers(term)) {
      System.err.println(joker + " named " + joker.getName() +
                         " bound to " + joker.boundTo());
    }
  }

  public static Term removeJoker(Term term)
    throws UnboundJokerException
  {
    RemoveJokerVisitor visitor = new RemoveJokerVisitor();
    try {
      return (Term) term.accept(visitor);
    }
    catch (ProverUtils.UnboundJokerRuntimeException e) {
      throw new UnboundJokerException(e.getMessage());
    }
  }


  public static class GetZSectNameVisitor
    implements SpecVisitor<String>,
               ZSectVisitor<String>
  {
    public String visitSpec(Spec spec)
    {
      for (Sect sect : spec.getSect()) {
        String name = sect.accept(this);
        if (name != null) return name;
      }
      return null;
    }

    public String visitZSect(ZSect zSect)
    {
      return zSect.getName();
    }
  }

  private static class RemoveJokerVisitor
    implements TermVisitor<Term>,
               HeadDeclListVisitor<Term>
  {
    public Term visitTerm(Term term)
    {
      if (term instanceof Joker) {
        Joker joker = (Joker) term;
        Term boundTo = joker.boundTo();
        if (boundTo == null) {
          final String message = "Joker " + joker.getName() +
            " is not associated to a term.";
          throw new UnboundJokerRuntimeException(message);
        }
        return boundTo.accept(this);
      }
      return VisitorUtils.visitTerm(this, term, true);
    }

    public Term visitHeadDeclList(HeadDeclList headDeclList)
    {
      ZDeclList zDeclList =
        VisitorUtils.visitTerm(this, headDeclList.getZDeclList(), false);
      zDeclList = (ZDeclList) zDeclList.create(zDeclList.getChildren());
      ZDeclList rest =
        (ZDeclList) headDeclList.getJokerDeclList().accept(this);
      zDeclList.addAll(rest);
      return zDeclList;
    }
  }

  public static class UnboundJokerRuntimeException
    extends net.sourceforge.czt.util.CztException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 6636261022785187318L;

	public UnboundJokerRuntimeException()
    {
    }

    public UnboundJokerRuntimeException(String message)
    {
      super(message);
    }
  }

  public static Map<String,AbstractOracle> createOracleMap()
  {
    Map<String,AbstractOracle> result = new HashMap<String,AbstractOracle>();
    result.put("TypecheckOracle", new TypecheckOracle());
    result.put("LookupOracle", new LookupOracle());
    result.put("ThetaOracle", new ThetaOracle(false));
    result.put("DecorThetaOracle", new ThetaOracle(true));
    result.put("DecorOracle", new DecorateOracle());
    result.put("SchemaMinusOracle", new SchemaMinusOracle());
    result.put("UnprefixOracle", new UnprefixOracle());
    result.put("SplitNamesOracle", new SplitNamesOracle());
    result.put("HideOracle", new HideOracle());
    result.put("RenameOracle", new RenameOracle());
    result.put("XiOracle", new XiOracle());
    return result;
  }
}
