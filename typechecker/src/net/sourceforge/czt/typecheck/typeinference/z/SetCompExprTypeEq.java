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
public class SetCompExprTypeEq implements TypeInferenceRule {
	// list of type subsequents
	// 2 items
	private List subsequent;
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public SetCompExprTypeEq(TypeEnvInt env, SetCompExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;
		factory_ = checker.getFactory();
	}

	public Object solve() throws TypeException {
		SetCompExpr scexpr = (SetCompExpr) sequent.getTerm();

		// type check the schma text part
		SchText schtxt = (SchText) scexpr.getSchText().accept(checker);
		// useful?
		//typeEnv = checker.getTypeEnv();

		// type check the expr part
		Expr expr = (Expr) scexpr.getExpr().accept(checker);
		Type type = checker.getTypeFromAnns(expr);

		// type of the set comprehension expr
		PowerType pt = factory_.createPowerType(type);
		scexpr = (SetCompExpr) checker.addAnns(scexpr, pt);

		return scexpr;
	}
}
