package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.12
public class MuExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public MuExprTypeEq(TypeEnvInt env, MuExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;
		typeEnv = checker.getTypeEnv();

		factory_ = checker.getFactory();
	}

	// why should the expr be optional?
	public Object solve() throws TypeException {
		MuExpr term = (MuExpr) sequent.getTerm();
		
		typeEnv.enterScope();
		SchText schtext = (SchText) term.getSchText().accept(checker);
		// now typeEnv should contain decls from schtext
		
		Expr expr = (Expr) term.getExpr().accept(checker);
		Type type = checker.getTypeFromAnns(expr);
		
		term = (MuExpr) checker.addAnns(term, type);
		
		typeEnv.exitScope();

		return term;
	}
}