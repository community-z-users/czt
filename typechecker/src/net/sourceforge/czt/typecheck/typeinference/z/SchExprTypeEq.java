package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.14
public class SchExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public SchExprTypeEq(TypeEnvInt env, SchExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;
		typeEnv = checker.getTypeEnv();

		factory_ = checker.getFactory();
	}

	// why should the expr be optional?
	public Object solve() throws TypeException {
		SchExpr term = (SchExpr) sequent.getTerm();
		
		typeEnv.enterScope();
		SchText schtext = (SchText) term.getSchText().accept(checker);
		
		Type type = checker.getTypeFromAnns(schtext);
		term = (SchExpr) checker.addAnns(term, type);
		
		typeEnv.exitScope();

		return term;
	}
}