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
public class PowerExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public PowerExprTypeEq(TypeEnvInt env, PowerExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	public Object solve() throws TypeException {
		PowerExpr term = (PowerExpr) sequent.getTerm();
		Expr expr = term.getExpr();
		expr = (Expr) expr.accept(checker);

		Type type = checker.getTypeFromAnns(expr);
		if (! (type instanceof PowerType)) {
			throw new TypeException(ErrorKind.POWERTYPE_NEEDED, expr);
		}
		PowerType pt = factory_.createPowerType(type);
		term = (PowerExpr) checker.addAnns(term, pt);

		return term;
	}
}
