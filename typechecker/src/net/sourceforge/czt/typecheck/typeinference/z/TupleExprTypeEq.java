package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.6
public class TupleExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public TupleExprTypeEq(TypeEnvInt env, TupleExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	// need to check tuple expr has at least 2 elements
	public Object solve() throws TypeException {
		TupleExpr term = (TupleExpr) sequent.getTerm();
		List exprs = term.getExpr();

		if (exprs.size() < 2) {
			throw new TypeException(ErrorKind.TUPLEEXPR_LESSTHAN_2, term);
		}

		// type of term should be a cartesian product type
		ProdType prodt = factory_.createProdType();
		List types = prodt.getType();

		Expr expr = null;
		Type type = null;
		for (int i = 0; i < exprs.size(); i++) {
			expr = (Expr) ((Expr) exprs.get(i)).accept(checker);
			// should overwrite?
			exprs.set(i, expr);

			type = checker.getTypeFromAnns(expr);
			types.add(type);
		}
		term = (TupleExpr) checker.addAnns(term, prodt);

		return term;
	}
}
