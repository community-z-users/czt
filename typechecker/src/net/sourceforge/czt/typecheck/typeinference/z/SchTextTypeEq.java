package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

// rule: whenever there's a SchText, enterScope & exitScope from the parent node

//13.2.6.14
public class SchTextTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public SchTextTypeEq(TypeEnvInt env, SchText term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	public Object solve() throws TypeException {
		SchText term = (SchText) sequent.getTerm();

		List decls = term.getDecl();

		Decl decl = null;
		for (int i = 0; i < decls.size(); i++) {
			decl = (Decl) ((Decl) decls.get(i)).accept(checker);
			// change decl to contain visited decl
			// alternatively could construct a new list and add checked decl to that list
			decls.set(i, decl);
		}

		// add type annotation for the schema text here
		Signature sig = factory_.createSignature();
		List ntps = sig.getNameTypePair();
		SchemaType st = factory_.createSchemaType(sig);
		PowerType tp = factory_.createPowerType(st);

		// SchText only contains (transformed) VarDecl
		VarDecl vdcl = null;
		// type of VarDecl is SchemaType
		SchemaType st1 = null;
		List tmpList = null;
		for (int i = 0; i < decls.size(); i++) {
			vdcl = (VarDecl) decls.get(i);
			st1 = (SchemaType) ((PowerType) checker.getTypeFromAnns(vdcl)).getType();
			tmpList = st1.getSignature().getNameTypePair();
			for (int j = 0; j < tmpList.size(); j++) {
				NameTypePair ntmp = (NameTypePair) tmpList.get(j);
				try {
					if (! TypeChecker.findInSignature(ntmp, ntps)) {
						throw new TypeException(ErrorKind.REDECLARATION, ntmp);
					}
					ntps.add(ntmp);
					
					// add ntmp to typeEnv
					typeEnv.addNameTypePair(ntmp);
					
				} catch (TypeException e) {
					e.printStackTrace();
					continue;
				}
			}
		}

		//TypeAnn ta = factory_.createTypeAnn(tp);
		term = (SchText) checker.addAnns(term, tp);

		Pred pred = (Pred) term.getPred().accept(checker);

		return term;
	}
}