package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;

public class Sequent {
	// accomodate variable env
	private TypeEnvInt typeEnv;
	private Term term;

	public Sequent (TypeEnvInt env, Term t) {
		typeEnv = env;
		term = t;
	}

	public TypeEnvInt getTypeEnv() {
		return typeEnv;
	}

	public Term getTerm() {
		return term;
	}

	public void setTypeEnv(TypeEnvInt en) {
		typeEnv = en;
	}

	public void setTerm(Term t) {
		term = t;
	}

//	public Object typeChecks() throws TypeException {
//		TypeEnv tmpEnv =
//	}
}