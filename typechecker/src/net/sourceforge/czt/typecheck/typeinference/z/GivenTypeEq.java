package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

public class GivenTypeEq implements TypeInferenceRule {
	// no type sequents for given type para
	private Sequent sequent;

	private TypeChecker checker;

	public GivenTypeEq (TypeEnvInt env, GivenPara term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;
	}

	public Object solve() throws TypeException {
		GivenPara term = (GivenPara) sequent.getTerm();

		List declNames = term.getDeclName();

		DeclName curName = null;

		// temp vector to store all decl names
		Vector tmpList = new Vector();

		for (int i = 0; i < declNames.size(); i++) {
			curName = (DeclName) ((DeclName) declNames.get(i)).accept(checker);

			// exception happened
			if (curName == null) continue;

			if (tmpList.contains(curName.getWord())) {
				// actually should delay this exception...
				throw new TypeException (ErrorKind.REDECLARATION, curName);
			}

			tmpList.add(curName.getWord());
		}

		return tmpList;
	}
}