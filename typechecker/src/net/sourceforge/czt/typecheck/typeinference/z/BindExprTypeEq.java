package net.sourceforge.czt.typecheck.typeinference.z;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;

import net.sourceforge.czt.typecheck.util.typingenv.*;
import net.sourceforge.czt.typecheck.util.typeerror.*;
import net.sourceforge.czt.typecheck.typeinference.z.Sequent;
import net.sourceforge.czt.typecheck.z.TypeChecker;

//13.2.6.9
public class BindExprTypeEq implements TypeInferenceRule {
	private Sequent sequent;

	private TypeChecker checker;

	private ZFactory factory_;
	private TypeEnvInt typeEnv;

	public BindExprTypeEq(TypeEnvInt env, BindExpr term, TypeChecker tc) {
		sequent = new Sequent(env, term);
		checker = tc;

		factory_ = checker.getFactory();
	}

	public Object solve() throws TypeException {
		BindExpr term = (BindExpr) sequent.getTerm();
		List pairs = term.getNameExprPair();
		
		Vector tmpNameList = new Vector();
		Vector tmpNTList = new Vector();
				
		Signature sig = factory_.createSignature(tmpNTList);
		// type of the term
		SchemaType st = factory_.createSchemaType(sig);

		NameExprPair nep = null;
		DeclName dn = null;
		Expr expr = null;
		Type type = null;
		for (int i = 0; i < pairs.size(); i++) {
			nep = (NameExprPair) pairs.get(i);
			dn = (DeclName) ((DeclName) nep.getName()).accept(checker);
			
			// exception happened
			if (dn == null) continue;
			if (tmpNameList.contains(dn.getWord())) {
				// actually should delay this exception
				throw new TypeException(ErrorKind.REDECLARATION, dn);
			}
			
			tmpNameList.add(dn.getWord());
			
			expr = (Expr) ((Expr) nep.getExpr()).accept(checker);
			type = checker.getTypeFromAnns(expr);
			NameTypePair ntp = factory_.createNameTypePair(dn, type);
			tmpNTList.add(ntp);
		}
		
		term = (BindExpr) checker.addAnns(term, st);
		return term;
	}
}
