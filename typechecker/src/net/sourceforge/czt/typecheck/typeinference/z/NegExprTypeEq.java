package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.15
public class NegExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public NegExprTypeEq(TypeEnvInt env, NegExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;
		typeEnv = checker.getTypeEnv();

		factory_ = checker.getFactory();
	}

	// why should the expr be optional?
	public Object solve() throws TypeException {
		NegExpr term = (NegExpr) sequent.getTerm();
		
		Expr expr = (Expr) term.getExpr().accept(checker);
		
		Type type = checker.getTypeFromAnns(expr);
		
		if (! (type instanceof PowerType)) {
			throw new TypeException(ErrorKind.POWERTYPE_NEEDED, type);
		}
		
		Type innerType = ((PowerType) type).getType();
		if (! (innerType instanceof SchemaType)) {
			throw new TypeException(ErrorKind.SCHEMATYPE_NEEDED, innerType);
		}
		
		term = (NegExpr) checker.addAnns(term, type);
		return term;
	}
}