package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.3
public class SetExprTypeEq implements TypeInferenceRule {
	// list of type subsequents, not used here
	private List subsequent;
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public SetExprTypeEq(TypeEnvInt env, SetExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
		typeEnv = env;
	}

	public Object solve() throws TypeException {
		SetExpr stexpr = (SetExpr) sequent.getTerm();
		List exprs = stexpr.getExpr();
		int size = exprs.size();

		// type of set extension expr should be a power type of some type
		PowerType pt = factory_.createPowerType();

		// type of the member exprs
		Type exprType = null;
		if (size == 0) {
			exprType = new VariableType();
		}
		else {
			Expr expr = null;
			Expr firstExpr = null;
			boolean ok = true;

			firstExpr = (Expr) ((Expr) exprs.get(0)).accept(checker);
			Type firstType = checker.getTypeFromAnns(firstExpr);
			if (firstType instanceof VariableType) ok = false;

			for (int i = 1; (ok && i < size); i++) {
				try {
					expr = (Expr) ((Expr) exprs.get(i)).accept(checker);
					exprType = (Type) checker.getTypeFromAnns(expr);
					if (! (((PowerType) firstType).getType() instanceof VariableType))
						ok = TypeChecker.unify(firstType, exprType);
					if (! ok) {
						throw new TypeException(ErrorKind.SETEXPR_MEMBTYPE_NOT_AGREE, firstType, exprType);
					}
				} catch(TypeException e) {
					Type tmpType = new VariableType();
					exprType = factory_.createPowerType(tmpType);
					e.printStackTrace();
					ok = false;
				}
			}
		}
		pt.setType(exprType);
		stexpr = (SetExpr) checker.addAnns(stexpr, pt);
		return stexpr;
	}
}