package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.7
public class TupleSelExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public TupleSelExprTypeEq(TypeEnvInt env, TupleSelExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	public Object solve() throws TypeException {
		TupleSelExpr term = (TupleSelExpr) sequent.getTerm();
		Expr expr = (Expr) term.getExpr().accept(checker);
		Type type = checker.getTypeFromAnns(expr);

		int which = term.getSelect().intValue();

		if (! (type instanceof ProdType)) {
			throw new TypeException(ErrorKind.PRODTYPE_REQUIRED, term);
		}

		List types = ((ProdType) type).getType();
		if (which > types.size()) {
			throw new TypeException(ErrorKind.INVALID_TUPLESELEXPR_SELECT, term);
		}

		Type resultType = (Type) types.get(which-1);

		return resultType;
	}
}

