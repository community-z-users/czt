package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

public class AxParaTypeEq implements TypeInferenceRule {
	private Sequent subsequent;
	private Sequent sequent;

	private TypeChecker checker;

	private boolean generic;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public AxParaTypeEq(TypeEnvInt env, AxPara term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		if (term.getDeclName().size() == 0) generic = false;
		else generic = true;

		factory_ = checker.getFactory();
	}

	public Object solve () throws TypeException {
		AxPara term = (AxPara) sequent.getTerm();
		typeEnv = sequent.getTypeEnv();

		// temp vector to store all decl names
		Vector tmpList = new Vector();

		List forParas = term.getDeclName();

		// check for duplicate in gen paras and add type annotations to DeclNames
		for (int i = 0; generic && i < forParas.size(); i++) {
			DeclName tmpDn = (DeclName) ((DeclName) forParas.get(i)).accept(checker);

			// exception happened
			if (tmpDn == null) continue;

			if (tmpList.contains(tmpDn.getWord())) {
				throw new TypeException (ErrorKind.REDECLARATION, tmpDn);
			}
			tmpList.add(tmpDn.getWord());

			// add annotation to DeclName
			GenType gt = factory_.createGenType(tmpDn);
			PowerType pt = factory_.createPowerType(gt);
			tmpDn = (DeclName) checker.addAnns(tmpDn, pt);

			// add NameTypePair into env
			NameTypePair ntp = factory_.createNameTypePair(tmpDn, pt);
			typeEnv.addNameTypePair(ntp);
		}

		// now form the subsequent of the eq
		SchText schtxt = term.getSchText();
		subsequent = new Sequent(typeEnv, schtxt);

		// now take care of the schema text
		schtxt = (SchText) schtxt.accept(checker);

		PowerType pt = (PowerType) checker.getTypeFromAnns(schtxt);
		// is a SchemaType
		Type type = pt.getType();

		// add type annotation to the AxPara
		TypeAnn ta = factory_.createTypeAnn(type);
		term = (AxPara) checker.addAnns(term, ta);

		return term;
	}
}