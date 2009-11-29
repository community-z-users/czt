/**
Copyright (C) 2008, 2009 Petra Malik, Clare Lenihan
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
package net.sourceforge.czt.z2alloy;

import static net.sourceforge.czt.z.util.ZUtils.assertZBranchList;
import static net.sourceforge.czt.z2alloy.ast.Sig.NONE;
import static net.sourceforge.czt.z2alloy.ast.Sig.SEQIDX;
import static net.sourceforge.czt.z2alloy.ast.Sig.SIGINT;

import java.io.IOException;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Stack;
import java.util.Map.Entry;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.visitor.TermVisitor;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.typecheck.z.TypeCheckUtils;
import net.sourceforge.czt.z.ast.AndExpr;
import net.sourceforge.czt.z.ast.AndPred;
import net.sourceforge.czt.z.ast.ApplExpr;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.BindSelExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.CompExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DecorExpr;
import net.sourceforge.czt.z.ast.Exists1Pred;
import net.sourceforge.czt.z.ast.ExistsExpr;
import net.sourceforge.czt.z.ast.ExistsPred;
import net.sourceforge.czt.z.ast.ForallPred;
import net.sourceforge.czt.z.ast.FreePara;
import net.sourceforge.czt.z.ast.Freetype;
import net.sourceforge.czt.z.ast.GivenPara;
import net.sourceforge.czt.z.ast.GivenType;
import net.sourceforge.czt.z.ast.HideExpr;
import net.sourceforge.czt.z.ast.IffExpr;
import net.sourceforge.czt.z.ast.IffPred;
import net.sourceforge.czt.z.ast.ImpliesExpr;
import net.sourceforge.czt.z.ast.ImpliesPred;
import net.sourceforge.czt.z.ast.InStroke;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.LambdaExpr;
import net.sourceforge.czt.z.ast.LatexMarkupPara;
import net.sourceforge.czt.z.ast.MemPred;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.NarrPara;
import net.sourceforge.czt.z.ast.NextStroke;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.NumStroke;
import net.sourceforge.czt.z.ast.OrExpr;
import net.sourceforge.czt.z.ast.OrPred;
import net.sourceforge.czt.z.ast.OutStroke;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.PowerExpr;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.ProdExpr;
import net.sourceforge.czt.z.ast.ProdType;
import net.sourceforge.czt.z.ast.RefExpr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.SchExpr2;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.SetCompExpr;
import net.sourceforge.czt.z.ast.SetExpr;
import net.sourceforge.czt.z.ast.Stroke;
import net.sourceforge.czt.z.ast.ThetaExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.Type2;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZFreetypeList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.ast.ZSchText;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.z.util.OperatorName;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.z.visitor.AndExprVisitor;
import net.sourceforge.czt.z.visitor.AndPredVisitor;
import net.sourceforge.czt.z.visitor.ApplExprVisitor;
import net.sourceforge.czt.z.visitor.AxParaVisitor;
import net.sourceforge.czt.z.visitor.BindSelExprVisitor;
import net.sourceforge.czt.z.visitor.CompExprVisitor;
import net.sourceforge.czt.z.visitor.ConstDeclVisitor;
import net.sourceforge.czt.z.visitor.DecorExprVisitor;
import net.sourceforge.czt.z.visitor.Exists1PredVisitor;
import net.sourceforge.czt.z.visitor.ExistsExprVisitor;
import net.sourceforge.czt.z.visitor.ExistsPredVisitor;
import net.sourceforge.czt.z.visitor.ForallPredVisitor;
import net.sourceforge.czt.z.visitor.FreeParaVisitor;
import net.sourceforge.czt.z.visitor.FreetypeVisitor;
import net.sourceforge.czt.z.visitor.GivenParaVisitor;
import net.sourceforge.czt.z.visitor.GivenTypeVisitor;
import net.sourceforge.czt.z.visitor.HideExprVisitor;
import net.sourceforge.czt.z.visitor.IffExprVisitor;
import net.sourceforge.czt.z.visitor.IffPredVisitor;
import net.sourceforge.czt.z.visitor.ImpliesExprVisitor;
import net.sourceforge.czt.z.visitor.ImpliesPredVisitor;
import net.sourceforge.czt.z.visitor.InclDeclVisitor;
import net.sourceforge.czt.z.visitor.LambdaExprVisitor;
import net.sourceforge.czt.z.visitor.LatexMarkupParaVisitor;
import net.sourceforge.czt.z.visitor.MemPredVisitor;
import net.sourceforge.czt.z.visitor.NarrParaVisitor;
import net.sourceforge.czt.z.visitor.NumExprVisitor;
import net.sourceforge.czt.z.visitor.OrExprVisitor;
import net.sourceforge.czt.z.visitor.OrPredVisitor;
import net.sourceforge.czt.z.visitor.PowerExprVisitor;
import net.sourceforge.czt.z.visitor.PowerTypeVisitor;
import net.sourceforge.czt.z.visitor.ProdExprVisitor;
import net.sourceforge.czt.z.visitor.ProdTypeVisitor;
import net.sourceforge.czt.z.visitor.RefExprVisitor;
import net.sourceforge.czt.z.visitor.SchExprVisitor;
import net.sourceforge.czt.z.visitor.SchemaTypeVisitor;
import net.sourceforge.czt.z.visitor.SetCompExprVisitor;
import net.sourceforge.czt.z.visitor.SetExprVisitor;
import net.sourceforge.czt.z.visitor.StrokeVisitor;
import net.sourceforge.czt.z.visitor.ThetaExprVisitor;
import net.sourceforge.czt.z.visitor.TruePredVisitor;
import net.sourceforge.czt.z.visitor.TupleExprVisitor;
import net.sourceforge.czt.z.visitor.TypeAnnVisitor;
import net.sourceforge.czt.z.visitor.VarDeclVisitor;
import net.sourceforge.czt.z.visitor.ZDeclListVisitor;
import net.sourceforge.czt.z.visitor.ZExprListVisitor;
import net.sourceforge.czt.z.visitor.ZFreetypeListVisitor;
import net.sourceforge.czt.z.visitor.ZSectVisitor;
import net.sourceforge.czt.z2alloy.ast.Enum;
import net.sourceforge.czt.z2alloy.ast.Expr;
import net.sourceforge.czt.z2alloy.ast.ExprBinary;
import net.sourceforge.czt.z2alloy.ast.ExprCall;
import net.sourceforge.czt.z2alloy.ast.ExprConstant;
import net.sourceforge.czt.z2alloy.ast.ExprQuant;
import net.sourceforge.czt.z2alloy.ast.ExprUnary;
import net.sourceforge.czt.z2alloy.ast.ExprVar;
import net.sourceforge.czt.z2alloy.ast.Field;
import net.sourceforge.czt.z2alloy.ast.Func;
import net.sourceforge.czt.z2alloy.ast.Module;
import net.sourceforge.czt.z2alloy.ast.PrimSig;
import net.sourceforge.czt.z2alloy.ast.Sig;
import net.sourceforge.czt.z2alloy.ast.SubsetSig;
import net.sourceforge.czt.z2alloy.ast.Toolkit;
import net.sourceforge.czt.zpatt.ast.Rule;
import net.sourceforge.czt.zpatt.visitor.RuleVisitor;

public class Z2Alloy implements TermVisitor<Expr>,
				AndExprVisitor<Expr>,
				AndPredVisitor<Expr>,
				ApplExprVisitor<Expr>,
				AxParaVisitor<Expr>,
				BindSelExprVisitor<Expr>,
				CompExprVisitor<Expr>,
				ConstDeclVisitor<Expr>,
				DecorExprVisitor<Expr>,
				ExistsExprVisitor<Expr>,
				Exists1PredVisitor<Expr>,
				ExistsPredVisitor<Expr>,
				ForallPredVisitor<Expr>,
				FreeParaVisitor<Expr>,
				FreetypeVisitor<Expr>,
				GivenParaVisitor<Expr>,
				GivenTypeVisitor<Expr>,
				HideExprVisitor<Expr>,
				IffExprVisitor<Expr>,
				IffPredVisitor<Expr>,
				ImpliesExprVisitor<Expr>,
				ImpliesPredVisitor<Expr>,
				InclDeclVisitor<Expr>,
				LambdaExprVisitor<Expr>,
				LatexMarkupParaVisitor<Expr>,
				MemPredVisitor<Expr>,
				NarrParaVisitor<Expr>,
				NumExprVisitor<Expr>,
				OrExprVisitor<Expr>,
				OrPredVisitor<Expr>,
				PowerExprVisitor<Expr>,
				PowerTypeVisitor<Expr>,
				ProdExprVisitor<Expr>,
				ProdTypeVisitor<Expr>,
				RefExprVisitor<Expr>,
				RuleVisitor<Expr>,
				SchemaTypeVisitor<Expr>,
				SchExprVisitor<Expr>,
				SetCompExprVisitor<Expr>,
				SetExprVisitor<Expr>,
				ThetaExprVisitor<Expr>,
				TruePredVisitor<Expr>,
				TupleExprVisitor<Expr>,
				TypeAnnVisitor<Expr>,
				VarDeclVisitor<Expr>,
				ZDeclListVisitor<Expr>,
				ZExprListVisitor<Expr>,
				ZFreetypeListVisitor<Expr>,
				ZSectVisitor<Expr>
{
	private SectionManager manager_;
	private AlloyPrintVisitor printVisitor_ = new AlloyPrintVisitor();
	private String section_ = "z2alloy";
	private boolean unfolding_ = false;
	private List<ExprVar> vars_;
	private List<Expr> exprs_;

	private Module module_ = new Module();

	private Map<String, Expr> macros_ = new HashMap<String, Expr>();

	private Map<String, Expr> fields_ = new HashMap<String, Expr>();

	private Stack<Term> stack = new Stack<Term>();

	private List<ExprVar> thetaQuantified = new ArrayList<ExprVar>();
	private Expr thetaPred = ExprConstant.TRUE;

	/**
	 * A mapping from ZName ids to alloy names.
	 */

	private Map<net.sourceforge.czt.z.ast.Expr, String> names = new HashMap<net.sourceforge.czt.z.ast.Expr, String>();

	private Map<String, String> names_ = new HashMap<String, String>();

	public Z2Alloy(SectionManager manager) throws Exception {
		manager_ = manager;
		module_.addModule(new Toolkit());
	}

	public void setUnfolding(boolean unfolding) {
		unfolding_ = unfolding;
	}

	public Module module() {
		return module_;
	}

	// ==================== Visitor Methods ==================

	public Expr visitTerm(Term term) {
		System.err.println(term.getClass() + " not yet implemented");
		throw new RuntimeException(print(term));
	}

	/**
	 * translates an and expression (schema conjunction) into an alloy and
	 * expression. The schemas are translated into a call to the predicate
	 * translated by the schema
	 * 
	 * eg
	 * 
	 * <pre>
	 *    A has a predicate of pred_A[a]{...}
	 *    B has a predicate of pred_B[b]{...}
	 *    
	 *    A \land B =&gt; pred_A[a] and pred_B[b]
	 * </pre>
	 * 
	 * Currently the actual variables from the signiture are not used in the
	 * pred calls. Instead new ones are created. This works, assuming the
	 * variables are declared with the same name as in the predicate
	 * declaration.
	 * 
	 * @return the expression
	 */
	public Expr visitAndExpr(AndExpr andExpr) {
		Expr[] comps = schExpr2SigComponent(andExpr);
		return comps[0].and(comps[1]);
	}

	/**
	 * translates an and predicate (ie conjunction) into an alloy and
	 * expression.The kind of conjunction used (newline, \and, chain) does not
	 * change the result
	 * 
	 * left and right expressions are recurisvely translated using visit
	 * 
	 * @return the expression if it successfully translated, or null it
	 *         something fails
	 */
	public Expr visitAndPred(AndPred andPred) {
		Expr left = visit(andPred.getLeftPred());
		Expr right = visit(andPred.getRightPred());
		if (left == null || right == null) {
			System.err.println("left and right of andpred must not be null");
			return null;
		}
		return left.and(visit(andPred.getRightPred()));
	}

	/**
	 * translates a function application <br>
	 * types of application expressions currently translated:
	 * 
	 * <pre>
	 * union                      left + right
	 * relational override        left ++ right
	 * rightwards arrow from bar  left -&gt; right
	 * ndres                      calls ndres[left, right]
	 * implication                left =&gt; right
	 * ..                         {i : Int | i &gt;= left and i &lt;= right}
	 * dom                        calls dom[right]
	 * ran						  calls ran[right]
	 * addition					  left + right
	 * substraction				  left - right
	 * dres						  left <: right
	 * </pre>
	 * 
	 * otherwise tries left.right
	 * 
	 * @return the expression if it successfully translated, or null it
	 *         something fails
	 */
	public Expr visitApplExpr(ApplExpr applExpr) {
		if (applExpr.getMixfix()) {
			if (applExpr.getRightExpr() instanceof TupleExpr
					&& applExpr.getLeftExpr() instanceof RefExpr) {
				RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
				String binOp = isInfixOperator(refExpr.getZName());
				ZExprList exprs = ((TupleExpr) applExpr.getRightExpr()).getZExprList();
				Expr left = visit(exprs.get(0));
				Expr right = visit(exprs.get(1));
				if (left == null || right == null) {
					System.err.println("left and right of a binary expression must not be null");
					return null;
				}
				if (binOp.equals(ZString.CUP)) {
					return left.plus(right);
				}
				if (binOp.equals(ZString.OPLUS)) {
					return left.override(right);
				}
				if (binOp.equals(ZString.MAPSTO)) {
					return left.product(right);
				}
				if (binOp.equals(ZString.NDRES)) {
					List<Expr> args = new ArrayList<Expr>();
					args.add(left);
					args.add(right);
					if (module_.containsFunc("ndres"))
						return module_.getFunc("ndres").call(args);
				}
				if (binOp.equals(ZString.DRES)) {
					return left.domain(right);
				}
				if (binOp.equals(ZString.IMP)) {
					return left.implies(right);
				}
				if (binOp.equals("..")) {
					ExprVar i = new ExprVar("i", SIGINT);
					Expr pred = i.gte(left).and(i.lte(right));
					return pred.comprehensionOver(Arrays
							.asList(new ExprVar[] { i }));
				}
				if (binOp.equals(ZString.CAT)) {
					if (module_.containsFunc("append"))
						return module_.getFunc("append").call(left, right);
				}
				if (binOp.equals(ZString.PLUS)) {
					return left.plus(right);
				}
				if (binOp.equals(ZString.MINUS)) {
					return left.minus(right);
				}
				System.err.println(applExpr.getClass() + " not yet implemented");
				return null;
			}
			if (applExpr.getLeftExpr() instanceof RefExpr) {
				RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
				if (print(refExpr.getName()).equals(
						ZString.LANGLE + " ,, " + ZString.RANGLE)) { // sequence
					Expr body = visit(applExpr.getRightExpr());
					if (body == NONE) {
						return NONE.product(NONE);
					} else {
						System.err.println("non empty sequences not translated yet");
						return null;
					}
				}
			}

		} else { // application
			if (applExpr.getLeftExpr() instanceof RefExpr) {
				RefExpr refExpr = (RefExpr) applExpr.getLeftExpr();
				if (print(refExpr.getName()).equals("dom")) {
					Expr body = visit(applExpr.getRightExpr());
					if (module_.containsFunc("dom"))
						return module_.getFunc("dom").call(body);
				}
				if (print(refExpr.getName()).equals("ran")) {
					Expr body = visit(applExpr.getRightExpr());
					if (module_.containsFunc("ran"))
						return module_.getFunc("ran").call(body);
				}
				if (print(refExpr.getName()).equals("last")) {
					Expr body = visit(applExpr.getRightExpr());
					if (module_.containsFunc("last"))
						return module_.getFunc("last").call(body);
				}
				if (print(refExpr.getName()).equals("front")) {
					Expr body = visit(applExpr.getRightExpr());
					if (module_.containsFunc("front"))
						return module_.getFunc("front").call(body);
				}
				if (module_.containsFunc(print(refExpr.getZName()))) {
					Func fun = module_.getFunc(print(refExpr.getZName()));
					if (applExpr.getRightExpr() instanceof TupleExpr) {
						Expr first = visit(applExpr.getRightExpr());
						if (first != null) {
							exprs_.add(0, first);
						}
						return fun.call(exprs_);
					}
					Expr body = visit(applExpr.getRightExpr());
					return fun.call(body);
				}
			}
		}
		Expr left = visit(applExpr.getLeftExpr());
		Expr right = visit(applExpr.getRightExpr());

		if (left instanceof ExprVar && ((ExprVar) left).label().equals("# _ ")) {
			return right.cardinality();
		}

		if (left == null || right == null) {
			System.err.println("left and right exprs must not be null in an ApplExpr");
			return null;
		}

		return right.join(left);
	}

	/**
	 * If the para is a schema defined by a schema expression, it creates a new
	 * signiture which contains all the fields of the translated sigs of the
	 * schemas in the expression. The precicate of the new sig is the result of
	 * recursively calling visit on the schema expression, ie the expression
	 * created by visitAndExpr, visitOrExpr, etc.
	 * 
	 * eg for
	 * 
	 * <pre>
	 *    A =&gt; sig A {a : univ}{pred_A[a]} pred pred_A[a:univ]{...}
	 *    B =&gt; sig B {b : univ}{pred_B[b]} pred pred_B[b:univ]{...}
	 *    C =&gt; sig C {c : univ}{pred_C[c]} pred pred_C[c:univ]{...}
	 *  
	 *    D == (A \land B) \lor C
	 *    
	 *  =&gt;
	 *    sig D {a : univ, b : univ, c : univ}{pred_D[a,b,b]} pred pred_D[a:univ,b:univ,c:univ]{(pred_A[a] and pred_B[b]) or pred_C[c]}
	 * </pre>
	 * 
	 * @return null
	 * 
	 * 
	 */
	// TODO Other cases: RefExprs, LambdaExpr, just visit(result).
	public Expr visitAxPara(AxPara para) {
		if (para.getName().size() > 0) {
			System.err.println("Generic definitions not handled yet.");
			return null;
		}
		ZSchText schText = para.getZSchText();
		if (schText.getZDeclList().size() == 1 && schText.getZDeclList().get(0) instanceof ConstDecl) {
			visit(schText.getZDeclList().get(0));
		}
		else if (schText.getZDeclList().size() == 1) {
			Expr expr = visit(schText.getZDeclList().get(0));
			if (expr instanceof ExprVar) {
				ExprVar exprVar = (ExprVar) expr;
				if (exprVar.expr() instanceof Sig) {
					Sig sig = (Sig) exprVar.expr();
					SubsetSig subsetSig = new SubsetSig(exprVar.label(), sig);
					addSig(subsetSig);
					Expr pred = visit(schText.getPred());
					if (pred != null) {
						addSigPred(subsetSig, pred);
					}
				}
			}
		}
		return null;
	}

	// TODO figure out wtf this is supposed to be
	public Expr visitBindSelExpr(BindSelExpr bindSelExpr) {
		Expr left = visit(bindSelExpr.getExpr());
		ExprVar right = new ExprVar(print(bindSelExpr.getName()));
		return left.join(right);
	}
	
	public Expr visitCompExpr(CompExpr compExpr) {
		Expr leftExpr = visit(compExpr.getLeftExpr());
		Expr rightExpr = visit(compExpr.getRightExpr());
		if (leftExpr instanceof Sig && rightExpr instanceof Sig) {
			Sig left = (Sig) leftExpr;
			Sig right = (Sig) rightExpr;
			// assumes it comes from the first element
			Expr leftmost = left.pred();
			if (! (leftmost instanceof ExprCall)) {
				System.out.println("error");
				return null;
			}
			leftmost = ((ExprCall) leftmost).fun().body();
			while (!(leftmost instanceof ExprCall)) {
				if (leftmost instanceof ExprUnary) {
					leftmost = ((ExprUnary) leftmost).sub();
				}
				else if (leftmost instanceof ExprBinary) {
					leftmost = ((ExprBinary) leftmost).left();
				}
				else {
					System.err.println("not translated " + leftmost.getClass());
					return null;
				}
			}
			System.out.println(((ExprCall) leftmost).fun().label());
			String name = ((ExprCall) leftmost).fun().label().substring(10);
			if (! module_.containsSig(name)) {
				System.err.println("not translated");
				return null;
			}
			Sig quant = module_.getSig(name);
			ExprVar quantSig = new ExprVar("temp", quant);
			List<ExprVar> vars = new ArrayList<ExprVar>();
			vars.add(quantSig);
			List<Expr> vars1 = new ArrayList<Expr>();
			List<Expr> vars2 = new ArrayList<Expr>();
			for (Field f : quant) {
				vars1.add(new ExprVar(f.label(), f.expr()));
				vars1.add(quantSig.join(f));
				vars2.add(quantSig.join(f));
				vars2.add(new ExprVar(f.label() + "'", f.expr()));
			}
			
			Func predleft = module_.getFunc("pred_" + left.label());
			Func predRight = module_.getFunc("pred_" + right.label());
			
			return predleft.call(vars1).and(predRight.call(vars2)).forSome(vars);
		}
		else {
			System.err.println("not implemented");
			return null;
		}
	}

	public Expr visitConstDecl(ConstDecl cDecl) {
		try {
			String sigName = print(cDecl.getName());
			net.sourceforge.czt.z.ast.Expr result = cDecl.getExpr();
			if (unfolding_) {
				Source exprSource = new StringSource("normalize~"
						+ print(cDecl.getName()));
				exprSource.setMarkup(Markup.LATEX);
				net.sourceforge.czt.z.ast.Expr toBeNormalized = ParseUtils
				.parseExpr(exprSource, section_, manager_);
				result = (net.sourceforge.czt.z.ast.Expr) preprocess(toBeNormalized);
				TypeCheckUtils.typecheck(result, manager_, false,
						section_);
			}
			//			if (result instanceof ApplExpr) {
			//				System.err.println("Failed to normalize");
			//				return null;
			//			}

			names.put(result, sigName);
			if (result instanceof SchExpr2) {
				processSchExpr2((SchExpr2) result);
				return null;
			}
			if (result instanceof LambdaExpr) {
				visitLambdaAsFunc((LambdaExpr) result);
				return null;
			}
			if (result instanceof SchExpr) {
				return visit(result);
			}
			Expr value = visit(result);
			macros_.put(sigName, value);
			return null;
		} catch (CommandException e) {
			throw new RuntimeException(e);
		} catch (IOException e) {
			throw new RuntimeException(e);
		}
	}

	public Expr visitDecorExpr(DecorExpr decorExpr) {
		Expr expr = visit(decorExpr.getExpr());
		if (expr instanceof Sig) {
			Sig sig = (Sig) expr;
			Sig sigStroke = new PrimSig(sig.label() + print(decorExpr.getStroke()));
			for (Field field : sig) {
				sigStroke.addField(new Field(field.label() + print(decorExpr.getStroke()), field.expr()));
			}
			return sigStroke;
		}
		else {
			System.err.println("not yet translated");
			return null;
		}
	}

	/**
	 * Creates a new signiture which contains all the fields in the predicate
	 * schemas, except those in schemas quantified over <br>
	 * Includes a signiture predicate which is an exists predicate translated
	 * from the schema predicate, with the additon that any fields in more than
	 * one predicate schema are equal <br>
	 * eg
	 * 
	 * <pre>
	 * A == \exists B, C @ D \and E
	 * </pre>
	 * 
	 * <br>
	 * where B has fields b:X, C has fields b:X, c:Y, D has fields b : X, c : Y,
	 * d : Z, E has field b : X translates to:
	 * 
	 * <pre>
	 * sig A {
	 *    d : Z
	 * }{pred_A[d]}
	 * pred pred_A[d : Z] {
	 *    some b_temp : B, c_temp : C | pred_D[c_temp.b, c_temp.c, d] and pred_E[c_temp.b] and c_temp.b = b_temp.b
	 * }
	 * 
	 */
	public Expr visitExistsExpr(ExistsExpr existsExpr) {

		/*
		 * basically this method accumulates all the fields of predicate bits,
		 * then removes all fields in exists sigs the ones left over are the
		 * fields for the new signiture
		 * 
		 * then it creates all the predicate - using build which makes the
		 * predicate calls to the sigs from either the arguments of the
		 * predicate (fields of the new sig) or joins between the fields of the
		 * exists sigs and the sigs
		 * 
		 * also needs to find exists sigs with matching fields and ensure they
		 * are equal
		 */

		ZDeclList incl = existsExpr.getZSchText().getZDeclList();

		List<Sig> inclSigs = new ArrayList<Sig>(); // the sigs quantified over
		ExprVar[] inclVars = new ExprVar[incl.size() - 1]; // the variables of
		// the sigs
		// quantified over

		// treats the first one separatly just for the call at the end
		Sig s = (Sig) visit(((InclDecl) incl.get(0)).getExpr());
		inclSigs.add(s);
		ExprVar first = (new ExprVar(s.label().toLowerCase() + "_temp", s));

		for (int i = 1; i < incl.size(); i++) {
			s = (Sig) visit(((InclDecl) incl.get(i)).getExpr());
			inclSigs.add(s);
			inclVars[i - 1] = (new ExprVar(s.label().toLowerCase() + "_temp", s));
		}

		Expr pred = visit(existsExpr.getExpr());

		List<Sig> predSigs = new ArrayList<Sig>(); // all the sigs in the body
		// of the predicate
		Stack<Expr> predParts = new Stack<Expr>(); // just for accumulating them
		// above
		predParts.add(pred);

		while (!predParts.isEmpty()) {
			Expr temp = predParts.pop();
			if (temp instanceof Sig) {
				predSigs.add((Sig) temp);
			} else if (temp instanceof ExprCall) {
				predSigs.add(module_.getSig(((ExprCall) temp).fun().label()
						.replaceFirst("pred_", "")));
			} else {
				System.err.println("Not fully translated: " + temp.getClass()
						+ " " + temp);
				return null;
			}
		}

		Map<String, Expr> fields = new HashMap<String, Expr>(); // the fields
		// for the new signiture
		Map<String, Expr> vars = new HashMap<String, Expr>(); // the expressions
		// to be used in predicate calls
		for (Sig sig : predSigs) {
			for (Field field : sig.fields()) {
				fields.put(field.label(), field.expr());
				vars.put(field.label(),
						new ExprVar(field.label(), field.expr()));

			}
		}

		for (int i = 0; i < inclSigs.size(); i++) {
			for (Field field : inclSigs.get(i).fields()) {
				fields.remove(field.label()); // fields in the quantified over
				// sigs should not be in the signiture
				if (i == 0) {
					vars.put(field.label(), first.join(field.expr()));
					// remember vars does not include them first because of the call at the end
				} else {
					vars.put(field.label(), inclVars[i - 1].join(field.expr()));
				}
			}
		}

		PrimSig sig;
		sig = new PrimSig(names.get(existsExpr));
		for (Entry<String, Expr> field : fields.entrySet()) {
			sig.addField(new Field(field.getKey(), field.getValue()));
		}
		addSig(sig);
		// unfolds the pred and builds it up into a tree contianing the pred
		// calls, ands, ors
		Expr predBody = build(pred, vars);

		// the name of the duplicate field, and the list of expressions
		// the expressions are such that they can be directly used in the
		// equality expression
		Map<String, List<Expr>> dupFields = new HashMap<String, List<Expr>>();
		for (int i = 0; i < inclSigs.size(); i++) {
			for (Field field : inclSigs.get(i).fields()) {
				if (!dupFields.containsKey(field.label())) {
					dupFields.put(field.label(), new ArrayList<Expr>());
				}
				if (i == 0) { // remember vars does not include the first
					// because of the call at the end
					dupFields.get(field.label()).add(first.join(field.expr()));
				} else {
					dupFields.get(field.label()).add(
							inclVars[i - 1].join(field.expr()));
				}
			}
		}

		// starts from the second entry, and puts all the later entries equal to
		// the first
		// ie looks like first=second and first=third and first=fourth ...
		for (Entry<String, List<Expr>> entry : dupFields.entrySet()) {
			for (int i = 1; i < entry.getValue().size(); i++) {
				if (predBody == null) {
					predBody = entry.getValue().get(0).equal(
							entry.getValue().get(i));
				} else {
					predBody = predBody.and(entry.getValue().get(0).equal(
							entry.getValue().get(i)));
				}
			}
		}

		vars_.add(first);
		addSigPred(sig, predBody.forSome(vars_));

		return null;
	}

	/**
	 * uses visit to recursively translate variables and predicates.
	 * 
	 * <pre>
	 * \exists_1 var1, ... varn @ pred1 | pred2
	 * </pre>
	 * 
	 * translates to :
	 * 
	 * <pre>
	 * one var1, ..., varn | pred1 and pred2
	 * </pre>
	 * 
	 * @return the expression, or null if something is null that should not be
	 */
	public Expr visitExists1Pred(Exists1Pred exists1Pred) {
		ExprVar firstVar = (ExprVar) visit(exists1Pred.getZSchText()
				.getZDeclList());
		List<ExprVar> rest = vars_;

		Expr pred;

		Expr pred1 = visit(exists1Pred.getZSchText().getPred());
		Expr pred2 = visit(exists1Pred.getPred());

		if (pred2 == null) {
			System.err.println("pred of ExistsPred must not be null");
			return null;
		}

		if (pred1 == null) {
			pred = pred2;
		} else {
			pred = pred1.and(pred2);
		}

		rest.add(firstVar);
		return pred.forOne(rest);
	}

	/**
	 * uses visit to recursively translate variables and predicates.
	 * 
	 * <pre>
	 * \exists var1, ..., varn @ pred1 | pred2
	 * </pre>
	 * 
	 * translates to
	 * 
	 * <pre>
	 * some var1, ... var2 | pred1 and pred2
	 * </pre>
	 * 
	 * @return the epxression, or null if something is null that should not be
	 */
	public Expr visitExistsPred(ExistsPred existsPred) {
		ExprVar firstVar = null;
		
		Expr first = visit(existsPred.getZSchText().getZDeclList());
		Expr sigPred = null;
		List<ExprVar> rest = vars_;		
		
		if (first instanceof ExprVar) firstVar = (ExprVar) first;
		else if (first instanceof Sig) {
			List<Expr> sigCallVars = new ArrayList<Expr>();
			Sig s = (Sig) first;
			for (Field f : s) {
				ExprVar temp = new ExprVar(f.label(), f.expr());
				sigCallVars.add(temp);
				if (s.fields().get(0).equals(f)) {
					firstVar = temp;
				}
				else {
					vars_.add(temp);
				}
			}
			sigPred = module_.getFunc("pred_" + s.label()).call(sigCallVars);
		}

		Expr pred;

		Expr pred1 = visit(existsPred.getZSchText().getPred());
		Expr pred2 = visit(existsPred.getPred());

		if (pred2 == null) {
			System.err.println("pred of ExistsPred must not be null");
			return null;
		}
		
		if (sigPred != null) {
			if( pred1 == null) {
				pred1 = sigPred;
			}
			else {
				pred1 = pred1.and(sigPred);
			}
		}

		if (pred1 == null) {
			pred = pred2;
		} else {
			pred = pred1.and(pred2);
		}
		
		if (! thetaQuantified.isEmpty()) {
			pred = thetaPred.and(pred).forSome(thetaQuantified);
			thetaPred = ExprConstant.TRUE;
			thetaQuantified.clear();
		}

		if (firstVar == null) {
			System.err.println("firstVar of ExistsPred must not be null");
			return null;
		}

		rest.add(firstVar);
		return pred.forSome(rest);
	}

	/**
	 * uses visit to recurisvely translate variables and predicates
	 * 
	 * <pre>
	 * \forall var1, ..., varn @ pred1 | pred2
	 * </pre>
	 * 
	 * translates to:
	 * 
	 * <pre>
	 * all var1, ..., var2 | pred1 =&gt; pred2
	 * </pre>
	 */

	public Expr visitForallPred(ForallPred allPred) {
		ExprVar firstVar = (ExprVar) visit(allPred.getZSchText().getZDeclList());
		List<ExprVar> rest = vars_;

		Expr pred;

		Expr pred1 = visit(allPred.getZSchText().getPred());
		Expr pred2 = visit(allPred.getPred());

		if (pred2 == null) {
			System.err.println("pred of allpred must not be null");
			return null;
		}

		if (pred1 == null) {
			pred = pred2;
		} else {
			pred = pred1.implies(pred2);
		}
		if (firstVar == null) {
			System.err.println("fistVar of allpred must not be null");
		}
		rest.add(firstVar);
		return pred.forAll(rest);
	}

	public Expr visitFreePara(FreePara para) {
		return visit(para.getFreetypeList());
	}

	/***
	 * creates a new enum
	 * eg
	 * 
	 * <pre>
	 * A ::= B | C | D
	 * </pre>
	 * 
	 * translates to:
	 * 
	 * <pre>
	 * enum A {B, C, C}
	 * </pre>
	 * 
	 * @return null
	 * 
	 */
	public Expr visitFreetype(Freetype freetype) {
		String parent = print(freetype.getName());
		Iterator<Branch> i = assertZBranchList(freetype.getBranchList())
		.iterator();
		List<String> children = new ArrayList<String>();
		while (i.hasNext()) {
			Branch branch = (Branch) i.next();
			if (branch.getExpr() != null)
				System.err
				.println("free types must be simple enumerations, but "
						+ branch.getName() + " branch has expression "
						+ branch.getExpr());
			children.add(print(branch.getName()));
		}
		module_.addSig(new Enum(parent, children));
		return null;
	}

	/**
	 * translates into a sig for each name, with the given name <br>
	 * eg
	 * 
	 * <pre>
	 * [A, B, C]
	 * </pre>
	 * 
	 * translates to:
	 * 
	 * <pre>
	 * sig A {}
	 * sig B {}
	 * sig C {}
	 * </pre>
	 */

	public Expr visitGivenPara(GivenPara para) {
		for (Name name : para.getNames()) {
			module_.addSig(new PrimSig(print(name)));
		}
		return null;
	}

	/**
	 * if a sig with the name of the givenType has been encountered before,
	 * returns the sig. <br>
	 * otherwise:
	 * 
	 * <pre>
	 *           arithmos         =&gt; Int
	 *           seq              =&gt; seq
	 * </pre>
	 * 
	 * @return the sig, or null if no sig matches
	 */
	public Expr visitGivenType(GivenType givenType) {
		if (print(givenType.getName()).equals(ZString.ARITHMOS)) {
			return SIGINT;
		}
		if (print(givenType.getName()).equals("seq")) {
			return SEQIDX;
		}
		return module_.getSig(print(givenType.getName()));
	}

	@Override
	public Expr visitHideExpr(HideExpr hideExpr) {
		Sig newSig = new PrimSig(names.get(hideExpr));
		List<String> hiddenNames = new ArrayList<String>();
		for (Name n : hideExpr.getZNameList()) hiddenNames.add(print(n));
		List<ExprVar> hidden = new ArrayList<ExprVar>();
		List<String> hiddenNamesIncluded = new ArrayList<String>();
		List<Field> fields = new ArrayList<Field>();
		Expr sub = null;


		if (hideExpr.getExpr() instanceof RefExpr) {
			RefExpr refExpr = (RefExpr) hideExpr.getExpr();
			Expr expr = visit(refExpr);
			if (expr instanceof Sig) {
				Sig sig = (Sig) expr;
				fields = sig.fields();
				sub = sig.pred();
			}
			else {
				System.err.println("class: " + hideExpr.getExpr().getClass());
				System.err.println(hideExpr.getClass() + " not currently translated");
			}
		}
		else if (hideExpr.getExpr() instanceof SchExpr2) {
			SchExpr2 schExpr2 = (SchExpr2) hideExpr.getExpr();
			fields = fields(schExpr2);
			sub = visit(schExpr2);
		}
		else {
			System.err.println("class: " + hideExpr.getExpr().getClass());
			System.err.println(hideExpr.getClass() + " not currently translated");
			return null;
		}

		for (Field f : fields) {
			if (hiddenNames.contains(f.label()) && ! hiddenNamesIncluded.contains(f.label())) {
				hidden.add(new ExprVar(f.label(), f.expr()));
				hiddenNamesIncluded.add(f.label());
			}
			else if (! hiddenNames.contains(f.label()))
				newSig.addField(f);
		}
		addSig(newSig);
		addSigPred(newSig, new ExprQuant(ExprQuant.Op.SOME, hidden, sub));
		return newSig;
	}

	/**
	 * translates an iff expression (schema equivalance) into an alloy iff
	 * expression. The schemas are translated into a call to the predicate
	 * translated by the schema
	 * 
	 * <pre>
	 *    A has a predicate of pred_A[a]{...}
	 *    B has a predicate of pred_B[b]{...}
	 *    
	 *    A \iff B =&gt; pred_A[a] &lt;=&gt; pred_B[b]
	 * </pre>
	 * 
	 * Currently the actual variables from the signiture are not used in the
	 * pred calls. Instead new ones are created. This works, assuming the
	 * variables are declared with the same name as in the predicate
	 * declaration.
	 * 
	 * @return the expression
	 */

	public Expr visitIffExpr(IffExpr iffExpr) {
		Expr[] comps = schExpr2SigComponent(iffExpr);
		return comps[0].iff(comps[1]);
	}

	public Expr visitIffPred(IffPred iffPred) {
	        Expr left = visit(iffPred.getLeftPred());
                Expr right = visit(iffPred.getRightPred());
	        if (left == null || right == null)
                        throw new RuntimeException("arguments of iffPred must not be null");
		return left.iff(right);
	}

	/**
	 * translates an implies expression (schema implication) into an alloy
	 * implies expression. The schemas are translated into a call to the
	 * predicate translated by the schema
	 * 
	 * <pre>
	 *    A has a predicate of pred_A[a]{...}
	 *    B has a predicate of pred_B[b]{...}
	 *    
	 *    A \implies B =&gt; pred_A[a] =&gt; pred_B[b]
	 * </pre>
	 * 
	 * Currently the actual variables from the signiture are not used in the
	 * pred calls. Instead new ones are created. This works, assuming the
	 * variables are declared with the same name as in the predicate
	 * declaration.
	 * 
	 * @return the expression
	 */

	public Expr visitImpliesExpr(ImpliesExpr impliesExpr) {
		Expr[] comps = schExpr2SigComponent(impliesExpr);
		return comps[0].implies(comps[1]);
	}

	/**
	 * translates an implies predicate into an alloy implies expression. <br>
	 * left and right expressions are recurisvely translated using visit
	 * 
	 * @return the expression if it successfully translated, or null it
	 *         something fails
	 */
	public Expr visitImpliesPred(ImpliesPred impl) {
		Expr left = visit(impl.getLeftPred());
		Expr right = visit(impl.getRightPred());
		if (left == null || right == null) {
			System.err
			.println("Left and right of impliespred must be non null");
			return null;
		}
		return left.implies(right);
	}

	public Expr visitInclDecl(InclDecl inclDecl) {
		return visit(inclDecl.getExpr());
	}
	
	/** Ignore Latex markup paragraphs. */
	public Expr visitLatexMarkupPara(LatexMarkupPara para) {
		return null;
	}

	public Expr visitLambdaExpr(LambdaExpr lambda) {
		String name = names.get(lambda);

		if (module_.containsFunc(name))
			return null;
		List<ExprVar> vars = new ArrayList<ExprVar>();
		vars.add((ExprVar) visit(lambda.getZSchText()
				.getZDeclList()));
		if (vars_ != null) {
			for (ExprVar exprVar : vars_) {
				vars.add(exprVar);
			}
		}
		Expr body = visit(lambda.getExpr());
		TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
		Expr returnDecl = visit(type);

		ExprVar j = new ExprVar("j", returnDecl);

		vars.add(j);

		ExprQuant exprQuant = new ExprQuant(ExprQuant.Op.COMPREHENSION, vars, j.equal(body)); 
		return exprQuant;
	}

	public Func visitLambdaAsFunc(LambdaExpr lambda) {
		String name = names.get(lambda);

		if (module_.containsFunc(name))
			return null;
		List<ExprVar> vars = new ArrayList<ExprVar>();
		vars.add((ExprVar) visit(lambda.getZSchText()
				.getZDeclList()));
		if (vars_ != null) {
			for (ExprVar exprVar : vars_) {
				vars.add(exprVar);
			}
		}
		Expr body = visit(lambda.getExpr());
		TypeAnn type = lambda.getExpr().getAnn(TypeAnn.class);
		Expr returnDecl = visit(type);
		Func func = new Func(name, vars, returnDecl);
		if (body != null)
			func.setBody(body);
		module_.addFunc(func);
		return null;
	}

	/**
	 * kinds of MemPred currently translated:
	 * 
	 * <pre>
	 * equality                   left = right
	 * notin                      ! left in right
	 * subseteq                   left in right
	 * subset                     left in right and (not left = right)
	 * less                       left &lt; right
	 * leq                        left &lt;= right
	 * greater                    left &gt; right
	 * geq                        left &gt;= right
	 * neq                        ! left = right
	 * </pre>
	 * 
	 * otherwise assumes it is membership => left in right
	 */
	public Expr visitMemPred(MemPred memPred) {
		if (memPred.getRightExpr() instanceof SetExpr
				&& ((SetExpr) memPred.getRightExpr()).getZExprList().size() == 1) {
			// equality
			Expr left = visit(memPred.getLeftExpr());
			Expr right = visit(memPred.getRightExpr());
			if (left == null || right == null) {
				System.err.println("Left and right of memPred must be non null");
				return null;
			}
			return left.equal(right);
		}
		if (memPred.getLeftExpr() instanceof TupleExpr
				&& memPred.getRightExpr() instanceof RefExpr) {
			RefExpr refExpr = (RefExpr) memPred.getRightExpr();
			ZExprList exprs = ((TupleExpr) memPred.getLeftExpr())
			.getZExprList();
			Expr left = visit(exprs.get(0));
			Expr right = visit(exprs.get(1));
			if (left == null || right == null) {
				System.err
				.println("Left and right of refExpr must be non null");
				return null;
			}
			if (isInfixOperator(refExpr.getZName(), ZString.NOTMEM)) {
				return left.in(right).not();
			}
			if (isInfixOperator(refExpr.getZName(), ZString.SUBSETEQ)) {
				return left.in(right);
			}
			if (isInfixOperator(refExpr.getZName(), ZString.SUBSET)) {
				return left.in(right).and(left.equal(right).not());
			}
			if (isInfixOperator(refExpr.getZName(), ZString.LESS)) {
				return left.lt(right);
			}
			if (isInfixOperator(refExpr.getZName(), ZString.LEQ)) {
				return left.lte(right);
			}
			if (isInfixOperator(refExpr.getZName(), ZString.GREATER)) {
				return left.gt(right);
			}
			if (isInfixOperator(refExpr.getZName(), ZString.GEQ)) {
				return left.gte(right);
			}
			if (isInfixOperator(refExpr.getZName(), ZString.NEQ)) {
				return left.equal(right).not();
			}
		}
		Expr left = visit(memPred.getLeftExpr());
		Expr right = visit(memPred.getRightExpr());
		if (left == null || right == null) {
			System.err.println("Left and right Expr of MemPred must not be null");
			System.out.println(memPred.getRightExpr().getClass());
			return null;
		}
		return left.in(right);
	}

	/** Ignore narrative paragraphs. */
	public Expr visitNarrPara(NarrPara para) {
		return null;
	}

	/**
	 * @return an alloy integer expression with the given value
	 */
	public Expr visitNumExpr(NumExpr numexpr) {
		return ExprConstant.makeNUMBER(numexpr.getValue().intValue());
	}

	/**
	 * translates an or expression (schema disjunction) into an alloy or
	 * expression. The schemas are translated into a call to the predicate
	 * translated by the schema <br>
	 * eg
	 * 
	 * <pre>
	 *    A has a predicate of pred_A[a]{...}
	 *    B has a predicate of pred_B[b]{...}
	 *    
	 *    A \lor B =&gt; pred_A[a] or pred_B[b]
	 * </pre>
	 * 
	 * Currently the actual variables from the signiture are not used in the
	 * pred calls. Instead new ones are created. This works, assuming the
	 * variables are declared with the same name as in the predicate
	 * declaration.
	 * 
	 * @return the expression
	 */
	public Expr visitOrExpr(OrExpr orExpr) {
		Expr[] comps = schExpr2SigComponent(orExpr);
		return comps[0].or(comps[1]);
	}

	/**
	 * translates an or predicate (ie disjunction) into an alloy or expression. <br/>
	 * left and right expressions are recurisvely translated using visit
	 * 
	 * @return the expression if it successfully translated, or null it
	 *         something fails
	 */
	public Expr visitOrPred(OrPred orPred) {
		Expr left = visit(orPred.getLeftPred());
		if (left != null) {
			return left.or(visit(orPred.getRightPred()));
		}
		System.err.println("left pred of orPred must not be null");
		return null;
	}

	/**
	 * recursively calls visit on the sub expression and creates an alloy set of
	 * the translation
	 * 
	 * @return the expression or null if the sub expression translates to null
	 */
	public Expr visitPowerExpr(PowerExpr powerExpr) {
		Expr body = visit(powerExpr.getExpr());
		if (body == null) {
			System.err.println("body of power expr must not be null");
			return null;
		}
		return body.setOf();
	}

	/**
	 * if the type of the subexpression is not null, creates the set of the
	 * translation
	 * 
	 * @return the expression, or null if the subexpression translates to null
	 */
	public Expr visitPowerType(PowerType powerType) {
		Expr body = visit(powerType.getType());
		if (body == null) {
			System.err.println("body of power type must not be null");
			return null;
		}
		return body.setOf();
	}

	/**
	 * translates from a z prod expr to an alloy version using visit to
	 * recursively translate the sub expressions <br/>
	 * eg
	 * 
	 * <pre>
	 * expr1 \cross ... \cross exprn =&gt; expr1 -&gt; ... -&gt; exprn
	 * </pre>
	 * 
	 * @return the expression or null if any of the sub expressions translate to
	 *         null
	 */
	public Expr visitProdExpr(ProdExpr prodExpr) {
		Expr expr = visit(prodExpr.getZExprList().get(0));
		for (int i = 1; i < prodExpr.getZExprList().size(); i++) {
			Expr current = visit(prodExpr.getZExprList().get(i));
			if (current == null || expr == null) {
				System.err.println("body of prodexprs must not be  null");
				return null;
			}
			expr = expr.product(current);
		}
		return expr;
	}

	/**
	 * translates from a prodType to the equivalant expression in alloy
	 * 
	 * @return the expression or null if some of the sub expressions translate
	 *         to null
	 */
	public Expr visitProdType(ProdType prodType) {
		Expr prod = null;
		for (Type2 type : prodType.getType()) {
			Expr cont = visit(type);
			if (cont == null) {
				System.err.println("elements of ProdType must not be null");
				return null;
			} else if (cont instanceof ExprUnary
					&& ((ExprUnary) cont).op() == ExprUnary.Op.SETOF) {
				cont = ((ExprUnary) cont).sub();
			}
			if (prod == null) {
				prod = cont;
			} else {
				prod = prod.product(cont);
			}
		}
		return prod;
	}

	/**
	 * kinds of RefExpr translated: <br>
	 * subexprs are translated recursively using visit
	 * 
	 * <pre>
	 * pfun               expr0 -&gt; lone expr1
	 * seq                seq expr0
	 * arithmos           Int
	 * nat                nat[]
	 * </pre>
	 * 
	 * otherwise if the name has is that of an already encountered signiture, it
	 * uses that signiture <br>
	 * finally it creates an ExprVar with the given name and a type from the
	 * type annotations.
	 */
	public Expr visitRefExpr(RefExpr refExpr) {
		if (isInfixOperator(refExpr.getZName(), ZString.PFUN)) {
			return visit(refExpr.getZExprList().get(0)).any_arrow_lone(
					visit(refExpr.getZExprList().get(1)));
		} else if (isPostfixOperator(refExpr.getZName(), "seq")) {
			return visit(refExpr.getZExprList().get(0)).seq();
		} else if (print(refExpr.getZName()).equals(ZString.ARITHMOS)) {
			return SIGINT;
		} else if (print(refExpr.getZName()).equals(ZString.NAT)) {
			ExprVar i = new ExprVar("i", SIGINT);
			Expr sub = i.gte(ExprConstant.ZERO);
			List<ExprVar> vars = new ArrayList<ExprVar>();
			vars.add(i);
			return sub.comprehensionOver(vars);
		} else if (print(refExpr.getZName()).equals(ZString.NUM)) {
			return SIGINT;
		} else if (print(refExpr.getZName()).equals(ZString.EMPTYSET)) {
			Expr type = visit(refExpr.getAnn(TypeAnn.class));
			int num = arity(type);
			Expr ret = NONE;
			for (int i = 1; i < num; i++) ret = NONE.product(NONE);
			return ret;
		} else if (module_.containsSig(print(refExpr.getName()))) {
			return module_.getSig(print(refExpr.getName()));
		} else if (print(refExpr.getName()).contains("Delta")
				&& module_.containsSig(print(refExpr.getName()).replaceFirst(
						"Delta", ""))) {
			return addDelta(module_.getSig(print(refExpr.getName())
					.replaceFirst("Delta", "")));
		} else if (print(refExpr.getName()).contains("Xi")) {
			return addXi(module_.getSig(print(refExpr.getName()).replaceFirst(
					"Xi", "")));
		} else if (fields_.containsKey(print(refExpr.getName()))) {
			return new ExprVar(print(refExpr.getName()), fields_
					.get(print(refExpr.getName())));
		}
		if (macros_.containsKey(print(refExpr.getName()))) {
			return macros_.get(print(refExpr.getName()));
		}

		String name = print(refExpr.getZName());
		Expr type = visit(refExpr.getAnn(TypeAnn.class));
		if (type == null) {
			return new ExprVar(name, null);
		}
		return new ExprVar(name, type);
	}

	/** Ignore rules. */
	public Expr visitRule(Rule r) {
		return null;
	}

	public Expr visitSchemaType(SchemaType schemaType) {
		// this doesn't really work. It matches the 'first' sig which has the
		// same number of fields, with the same names
		// could check the types
		// If there are two schemas with the same number and names of fields it
		// fails.
		Map<String, Expr> fields = new HashMap<String, Expr>();
		for (NameTypePair p : schemaType.getSignature().getNameTypePair()) {
			fields.put(print(p.getName()), visit(p.getType()));
		}

		for (Sig sig : module_.sigs()) {
			boolean equal = sig.fields().size() == fields.size();
			for (Field field : sig.fields()) {
				if (!fields.containsKey(field.label())) {
					equal = false;
				}
			}
			if (equal) {
				return sig;
			}
		}
		return null;
	}

	/**
	 * creates a new signiture to represent the schema <br>
	 * includes all the fields of the schema <br>
	 * if the schema contains an InclDecl, it includes all the fields of this
	 * schema <br>
	 * the predicate for this schema is included in the new signiture <br>
	 * eg
	 * 
	 * <pre>
	 * given sig A {a : univ}{pred_A[a]} pred pred_A[a] {...}
	 * 
	 * \begin{schema}{B}
	 *  A 
	 *  c : C
	 * \where
	 *  ...
	 * \end{schema}
	 *</pre>
	 * 
	 * translates to:
	 * 
	 * <pre>
	 * sig B {a : univ, c : C} {pred_B[a,c]} pred pred_B {... and pred_A[a]}
	 * </pre>
	 * 
	 */
	public Expr visitSchExpr(SchExpr schExpr) {
		String schName = names.get(schExpr);
		if (schName == null) {
			System.err.println("SchExprs must have names");
			return null;
		}
		Sig sig = new PrimSig(schName);
		Expr fieldPred = null;
		for (Decl d : schExpr.getZSchText().getZDeclList()) {
			if (d instanceof VarDecl) {
				VarDecl vardecl = (VarDecl) d;
				ZNameList nameList = vardecl.getName();
				for (Name name : nameList) {
					sig.addField(new Field(print(name),
							visit(vardecl.getExpr())));
				}
			} else if (d instanceof InclDecl) {
				InclDecl incdecl = (InclDecl) d;
				Expr sigfieldpred = processSigField((Sig) visit(incdecl.getExpr()), sig);
				if (fieldPred != null) {
					fieldPred = fieldPred.and(sigfieldpred);
				} else {
					fieldPred = sigfieldpred;
				}
			} else {
				System.err.println(d.getClass() + " not yet implemented");
				return null;
			}
		}
		addSig(sig);
		Expr pred = visit(schExpr.getZSchText().getPred());
		if (fieldPred != null) {
			addSigPred(sig, fieldPred);
		}

		if (pred != null) {
			addSigPred(sig, pred);
		}
		return null;

	}

	/**
	 * <pre>
	 * {expr1, ..., exprn @ pred}
	 * </pre>
	 * 
	 * translates to
	 * 
	 * <pre>
	 * {expr1, ..., exprn | pred}
	 * </pre>
	 * 
	 * using visit to recursively translate the exprs and pred
	 * 
	 * @return the expression
	 * 
	 */

	public Expr visitSetCompExpr(SetCompExpr setCompExpr) {
		ExprVar firstVar = (ExprVar) visit(setCompExpr.getZSchText()
				.getZDeclList());
		List<ExprVar> rest = vars_;
		Expr pred = visit(setCompExpr.getZSchText().getPred());
		Expr oPred = visit(setCompExpr.getExpr());
		vars_.add(firstVar);

		if (pred == null) {
			pred = ExprConstant.TRUE;
		}
		if (oPred == null) {
			return pred.comprehensionOver(rest);
		}
		
		Expr type = visit(setCompExpr.getExpr().getAnn(TypeAnn.class));
		
		ExprVar exprVar = new ExprVar("temp", type);

		List<ExprVar> temp = new ArrayList<ExprVar>();
		temp.add(exprVar);
		
		return new ExprQuant(ExprQuant.Op.COMPREHENSION, temp, pred.and(new ExprQuant(ExprQuant.Op.SOME, vars_, oPred.equal(exprVar))));
	}

	/**
	 * if the set is null or empty translates it to none <br/>
	 * if the set has one member, transates it to that member <br/>
	 * otherwise translates the set into th union of all its members <br/>
	 * eg
	 * 
	 * <pre>
	 * {a, b, c} =&gt; a + b + c
	 * {a} =&gt; a
	 * {} =&gt; none
	 * </pre>
	 */
	public Expr visitSetExpr(SetExpr setExpr) {
		if (setExpr.getExprList() == null) {
			return NONE;
		}
		ZExprList exprs = setExpr.getZExprList();
		if (exprs.size() == 0) {
			return NONE;
		} else if (exprs.size() == 1) {
			Expr ret = visit(exprs.get(0));
			return ret;
		} else {
			Expr expr = null;
			for (net.sourceforge.czt.z.ast.Expr e : exprs) {
				Expr ve = visit(e);
				if (ve == null) {
					System.err.println("Elements of setexpr must not be null");
					return null;
				}
				if (expr == null) {
					expr = ve;
				} else {
					expr = expr.plus(ve);
				}
			}
			return expr;
		}
	}

	public Expr visitThetaExpr(ThetaExpr thetaExpr) {
		Expr expr = visit(thetaExpr.getExpr());
		if (! (expr instanceof Sig)) {
			System.err.println("not translated");
			return null;
		}
		Sig sig = (Sig) expr;
		String strokes = "";
		for (Stroke s : thetaExpr.getZStrokeList()) {
			strokes+= printVisitor_.visitStroke(s);
		}
		ExprVar exprVar = new ExprVar(sig.label().toLowerCase() + strokes, sig);

		for (ExprVar ev : thetaQuantified) {
			if (ev.label().equals(exprVar.label())) {
				return ev;
			}
		}

		thetaQuantified.add(exprVar);

		Expr pred = null;

		for (Field f : sig.fields()) {
			if (pred == null) {
				pred = exprVar.join(f).equal(new ExprVar(f.label() + strokes, f.expr()));
			}
			else {
				pred = pred.and(exprVar.join(f).equal(new ExprVar(f.label() + strokes, f.expr())));
			}
		}

		if (thetaPred == ExprConstant.TRUE || thetaPred == null) {
			thetaPred = pred;
		}
		else {
			thetaPred = thetaPred.and(pred);
		}
		return exprVar;
	}

	public Expr visitTruePred(TruePred arg0) {
		return ExprConstant.TRUE;
	}

	public Expr visitTupleExpr(TupleExpr tupleExpr) {
		return visit(tupleExpr.getZExprList());
	}

	public Expr visitTypeAnn(TypeAnn typeAnn) {
		return visit(typeAnn.getType());
	}

	/**
	 * creates a exprvar with the name and expr of the vDecl
	 */
	public Expr visitVarDecl(VarDecl vDecl) {
		return new ExprVar(print(vDecl.getName()), visit(vDecl.getExpr()));
	}

	/**
	 * uses visit to recursively translate the elements fo the ZDeclList <br/>
	 * sets internally a list containing translations all elements other than
	 * the first, in order
	 * 
	 * @return the first element
	 */
	public Expr visitZDeclList(ZDeclList zDeclList) {
		Iterator<Decl> iter = zDeclList.iterator();
		Expr result = visit(iter.next());
		if (iter.hasNext()) {
			List<ExprVar> list = new ArrayList<ExprVar>();
			while (iter.hasNext()) {
				list.add((ExprVar) visit(iter.next()));
			}
			vars_ = list;
		} else {
			vars_ = new ArrayList<ExprVar>();
		}
		return result;
	}

	public Expr visitZExprList(ZExprList zExprList) {
		Iterator<net.sourceforge.czt.z.ast.Expr> iter = zExprList.iterator();
		Expr result = visit(iter.next());
		if (iter.hasNext()) {
			List<Expr> list = new ArrayList<Expr>();
			while (iter.hasNext()) {
				list.add(visit(iter.next()));
			}
			exprs_ = list;
		} else {
			exprs_ = new ArrayList<Expr>();
		}
		return result;
	}

	/**
	 * visits each element of the list
	 * 
	 * @return null
	 */
	public Expr visitZFreetypeList(ZFreetypeList list) {
		for (Freetype freetype : list) {
			visit(freetype);
		}
		return null;
	}

	public Expr visitZSect(ZSect zSect) {
		Source specSource = new StringSource("\\begin{zsection} "
				+ "\\SECTION " + section_ + " " + "\\parents "
				+ zSect.getName() + ", " + "expansion\\_rules, "
				+ "simplification\\_rules" + "\\end{zsection}", section_);
		specSource.setMarkup(Markup.LATEX);
		manager_.put(new Key<Source>(section_, Source.class), specSource);

		for (Para para : zSect.getZParaList()) {
			visit(para);
		}

		return null;
	}

	private Expr[] schExpr2SigComponent(SchExpr2 schExpr2) {
		Expr left = visit(schExpr2.getLeftExpr());
		Expr right = visit(schExpr2.getRightExpr());
		if (left instanceof PrimSig) {
			PrimSig leftsig = (PrimSig) left;
			Func leftPred = module_.getFunc("pred_" + leftsig.label());
			List<Expr> content = new ArrayList<Expr>();
			for (Field f : leftsig.fields()) {
				Expr fieldExpr = f;
				fieldExpr = new ExprVar(f.label(), fieldExpr);
				if (fieldExpr == null) {
					System.err.println("fieldexpr must not be null");
					return null;
				}
				content.add(fieldExpr);
			}
			Expr[] args = content.toArray(new Expr[0]);
			left = leftPred.call(args);
		}
		if (right instanceof PrimSig) {
			PrimSig rightsig = (PrimSig) right;
			Func rightPred = module_.getFunc("pred_" + rightsig.label());
			List<Expr> content = new ArrayList<Expr>();
			for (Field f : rightsig.fields()) {
				Expr fieldExpr = f;
				fieldExpr = new ExprVar(f.label(), fieldExpr);
				if (fieldExpr == null) {
					System.err.println("fieldexpr must not be null");
					return null;
				}
				content.add(fieldExpr);
			}
			Expr[] args = content.toArray(new Expr[0]);
			right = rightPred.call(args);
		}
		if (left == null || right == null) {
			System.err.println("left and right of SchExpr2 must not be null");
			return null;
		}
		return new Expr[] { left, right };
	}

	private Expr processSigField(Sig sigField, Sig sig) {
		// so we can easily see if a field is already present
		Map<String, Field> sigfieldnames = new HashMap<String, Field>();
		List<Expr> args = new ArrayList<Expr>();
		for (Field sigfield : sig.fields()) {
			sigfieldnames.put(sigfield.label(), sigfield);
		}

		for (Field subfield : sigField.fields()) {
			if (!sigfieldnames.containsKey(subfield.label())) {
				Field newfield = new Field(subfield.label(), subfield.expr());
				sig.addField(newfield);
				sigfieldnames.put(newfield.label(), newfield);
			}
			Field field = sigfieldnames.get(subfield.label());
			args.add(new ExprVar(field.label(), field.expr()));
		}
		Func f;
		if (module_.containsFunc("pred_" + sigField.label())) {
			f = module_.getFunc("pred_" + sigField.label());
		}
		else if (module_.containsFunc("pred_" + sigField.label().replaceAll("'", ""))) {
			f = module_.getFunc("pred_" + sigField.label().replace("'", ""));
		}
		else {
			return null;
		}
		return f.call(args.toArray(new Expr[0]));
	}

	private void addSigPred(Sig sig, Expr pred) {
		Func existingPred = module_.getFunc("pred_" + sig);
		if (existingPred == null) {
			System.err.println("No pred for " + sig + " so " + pred
					+ " cannot be added");
			return;
		}
		
		if (existingPred.getBody() == ExprConstant.TRUE) {
			existingPred.setBody(pred);
		} else {
			existingPred.setBody(existingPred.getBody().and(pred));
		}
		if (! thetaQuantified.isEmpty()) {
			existingPred.setBody(new ExprQuant(ExprQuant.Op.SOME, thetaQuantified, existingPred.body().and(thetaPred)));
			thetaQuantified.clear();
			thetaPred = ExprConstant.TRUE;
		}
	}

	private boolean isPostfixOperator(ZName name, String op) {
		try {
			OperatorName opName = new OperatorName(name);
			String[] opWords = opName.getWords();
			return opWords.length > 0 && op.equals(opWords[0]);
		} catch (OperatorName.OperatorNameException e) {
			return false;
		}
	}

	private String isInfixOperator(ZName name) {
		try {
			OperatorName opName = new OperatorName(name);
			if (!opName.isInfix())
				return null;
			return opName.getWords()[1];
		} catch (OperatorName.OperatorNameException e) {
			return null;
		}
	}

	private boolean isInfixOperator(ZName name, String op) {
		try {
			OperatorName opName = new OperatorName(name);
			String[] opWords = opName.getWords();
			return opWords.length > 0 && op.equals(opWords[1]);
		} catch (OperatorName.OperatorNameException e) {
			return false;
		}
	}

	private String print(Term t) {
		if (t != null)
			return t.accept(printVisitor_);
		else
			return "";
	}

	private Expr visit(Term t) {
		if (t != null) {
			stack.push(t);
			Expr e = t.accept(this);
			stack.pop();
			return e;
		}
		return null;
	}

	private Term preprocess(Term term) {
		try {
			RuleTable rules = manager_.get(new Key<RuleTable>(section_,
					RuleTable.class));
			RewriteVisitor rewriter = new RewriteVisitor(rules, manager_,
					section_);
			return Strategies.innermost(term, rewriter);
		} catch (Exception e) {
			throw new RuntimeException(e);
		}
	}

	private Expr processSchExpr2(SchExpr2 schExpr2) {
		String schName = names.get(schExpr2);
		if (schName == null) {
			System.err.println("SchExpr2s must have names");
			return null;
		}
		Sig sig = new PrimSig(schName);

		List<Field> exprs = fields(schExpr2);
		for (Field expr : exprs) {
			addField(sig, expr);
		}
		addSig(sig);
		addSigPred(sig, visit(schExpr2));
		return null;
	}

	private List<Field> fields(SchExpr2 schExpr2) {
		Map<String, Expr> fields = new HashMap<String, Expr>();
		Queue<SchExpr2> subexprs = new LinkedList<SchExpr2>();
		subexprs.offer((SchExpr2) schExpr2);

		List<String> order = new ArrayList<String>();

		while (!subexprs.isEmpty()) {
			SchExpr2 subexpr = subexprs.poll();
			if (subexpr.getLeftExpr() instanceof RefExpr) {
				if (!fields.containsKey(print(subexpr.getLeftExpr()))) {
					Expr field = visit(subexpr.getLeftExpr());
					fields.put(print(subexpr.getLeftExpr()), field);
					order.add(print(subexpr.getLeftExpr()));
				}
			} else if (subexpr.getLeftExpr() instanceof SchExpr2) {
				subexprs.offer((SchExpr2) subexpr.getLeftExpr());
			}
			if (subexpr.getRightExpr() instanceof RefExpr) {
				if (!fields.containsKey(print(subexpr.getRightExpr()))) {
					Expr field = visit(subexpr.getRightExpr());
					fields.put(print(subexpr.getRightExpr()), field);
					order.add(print(subexpr.getRightExpr()));
				}
			} else if (subexpr.getRightExpr() instanceof SchExpr2) {
				subexprs.offer((SchExpr2) subexpr.getRightExpr());
			}
		}
		List<Field> fieldsList = new ArrayList<Field>();
		for(String l : order) {
			if (!(fields.get(l) instanceof Sig)) {
				System.err.println("error");
				return null;
			}
			Sig s = (Sig) fields.get(l);
			fieldsList.addAll(s.fields());
		}
		return fieldsList;
	}

	private void addSig(Sig sig) {
		module_.addSig(sig);
		List<ExprVar> vars = new ArrayList<ExprVar>();
		for (Field f : sig.fields()) {
			vars.add(new ExprVar(f.label(), f.expr()));
			fields_.put(f.label(), f.expr());
		}
		Func f = new Func("pred_" + sig.label(), vars);
		f.setBody(ExprConstant.TRUE);
		module_.addFunc(f);
		Expr[] fields = new Expr[sig.fields().size()];
		for (int i = 0; i < sig.fields().size(); i++)
			fields[i] = sig.fields().get(i);
		sig.addPred(f.call(fields));
	}

	private void addField(Sig sig, Field field) {
		if (! sig.containsField(field.label())) {
			sig.addField(field);
		}
	}

	private Sig addDelta(Sig sig) {
		PrimSig delta = new PrimSig("Delta" + sig.label());
		for (Field field : sig.fields()) {
			delta.addField(new Field(field.label(), field.expr()));
			delta.addField(new Field(field.label() + "'", field.expr()));
		}
		addSig(delta);
		return delta;
	}

	private Expr addXi(Sig sig) {
		PrimSig xi = new PrimSig("Xi" + sig.label());
		for (Field field : sig.fields()) {
			xi.addField(new Field(field.label(), field.expr()));
			xi.addField(new Field(field.label() + "'", field.expr()));
		}
		addSig(xi);
		for (int i = 0; i < xi.fields().size(); i += 2) {
			Field field1 = xi.fields().get(i);
			Field field2 = xi.fields().get(i + 1);
			addSigPred(xi, new ExprVar(field1.label(), field1.expr())
			.equal(new Field(field2.label(), field2.expr())));
		}
		return xi;

	}

	private Expr build(Expr expr, Map<String, Expr> vars) {
		if (expr instanceof ExprCall) { // not sure exactly when and why these
			// are sometimes sigs and sometimes
			// preds
			expr = (module_.getSig(((ExprCall) expr).fun().label().replaceFirst(
					"pred_", "")));
		}
		if (expr instanceof Sig) {
			Sig signiture = (Sig) expr;
			Expr[] exprs = new Expr[signiture.fields().size()];
			for (int i = 0; i < signiture.fields().size(); i++) {
				exprs[i] = vars.get(signiture.fields().get(i).label());
			}
			return module_.getFunc("pred_" + signiture.label()).call(exprs);
		}
		// should put in new kinds of things as they are needed
		System.err.println("Not fully translated: " + expr.getClass() + " "
				+ expr);
		return null;
	}


	/*
	 * TODO Clare: make this actually work properly in all cases (maybe this should be in the AST?)
	 */
	private int arity(Expr expr) {
		if (expr instanceof ExprBinary && ((ExprBinary) expr).op().isArrow) {
			ExprBinary exprBinary = (ExprBinary) expr;
			return 1 + arity(exprBinary.left()) + arity(exprBinary.right());
		}
		if (expr instanceof ExprUnary) {
			return arity(((ExprUnary) expr).sub());
		}
		if (expr instanceof ExprVar) {
			return arity(((ExprVar) expr).expr());
		}
		return 1;
	}

	private void debug(Term t) {
		StringWriter foo = new StringWriter();
		PrintUtils.print(t, foo, manager_, section_, Markup.UNICODE);
		System.out.println("Debug: " + foo);
	}

	class AlloyPrintVisitor extends PrintVisitor implements
	DecorExprVisitor<String>, RefExprVisitor<String>, StrokeVisitor<String> {
		public String visitZName(ZName zName) {
			String word = zName.getWord();
			word = word.replaceAll(ZString.DELTA, "Delta");
			word = word.replaceAll(ZString.XI, "Xi");
			word = word.replaceAll("\u03A6", "Phi");
			word = word.replaceAll("\u2295", "Distro");
			word = word.replaceAll("/", "Slash");

			if (names_.containsKey(zName.getId())) {
				return names_.get(zName.getId());
			}
			return word + visit(zName.getStrokeList());
		}

		public String visitInStroke(InStroke inStroke) {
			return "_in";
		}

		public String visitNextStroke(NextStroke nextStroke) {
			return "'";
		}

		public String visitOutStroke(OutStroke outStroke) {
			return "_out";
		}
		
		public String visitNumStroke(NumStroke numStroke) {
			return numStroke.getDigit().toString();
		}

		public String visitDecorExpr(DecorExpr decorExpr) {
			return decorExpr.getExpr().accept(this)
			+ decorExpr.getStroke().accept(this);
		}

		public String visitRefExpr(RefExpr refExpr) {
			return refExpr.getName().accept(this);
		}

		@Override
		public String visitStroke(Stroke stroke) {
			return stroke.accept(this);
		}
	}

}
