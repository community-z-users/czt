package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

// 13.2.6.3
public class VarDeclTypeEq implements TypeInferenceRule {
	private Sequent subsequent;
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public VarDeclTypeEq(TypeEnvInt env, VarDecl term, TypeChecker tc) {
		subsequent = new Sequent(env, term.getExpr());
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	// this method won't throw exceptions
	public Object solve() throws TypeException {
		VarDecl term = (VarDecl) sequent.getTerm();

		// type-checks the expr and gets its type -> to do
		Type type = null;
		try {
			Expr expr = (Expr) ((Expr) subsequent.getTerm()).accept(checker);

			type = checker.getTypeFromAnns(expr);
			if (! (type instanceof PowerType)) {
				throw new TypeException(ErrorKind.POWERTYPE_NEEDED, expr);
			}
		// if there's an exception, create a power type of variable type
		} catch (TypeException e) {
			e.printStackTrace();
			VariableType vt = new VariableType();

			// a power type of variable type
			type = factory_.createPowerType(vt);
		}

		NameTypePair ntp = null;
		List decls = term.getDeclName();
		DeclName decl = null;

		// add annotation to the VarDecl
		Signature sig = factory_.createSignature();
		List ntps = sig.getNameTypePair();
		SchemaType st = factory_.createSchemaType(sig);
		// TypeAnn should contain a power type
		PowerType pt = factory_.createPowerType(st);
		TypeAnn ta = factory_.createTypeAnn(pt);

		Type curT = ((PowerType) type).getType();
		for (int i = 0; i < decls.size(); i++) {
			decl = (DeclName) decls.get(i);
			ntp = factory_.createNameTypePair(decl, curT);
			try {
				typeEnv.addNameTypePair(ntp);
				ntps.add(ntp);
			} catch (TypeException e) {
				e.printStackTrace();
			}
		}

		checker.addAnns(term, ta);

		return term;
	}
}