package net.sourceforge.czt.typecheck.util.typeerror;

import java.util.List;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.z.visitor.*;

public class TypeException extends Throwable {
	int kind;
	Term term1;
	Term term2;

	public TypeException (int k, Term t) {
		kind = k;
		term1 = t;
	}

	public TypeException (int k, Term t1, Term t2) {
		kind = k;
		term1 = t1;
		term2 = t2;
	}
	
	public String toString() {
		String cause = ErrorKind.getCase(kind);
/*
		String name = null;
		String cause = null;
		switch (kind) {
			case REDECLARATION:
				if (term instanceof DeclName) {
					name = ((DeclName) term).getName().getId();
					cause
				}
			case UNKNOWN_ERROR:
			default:
				break;
		}

*/
		return cause;
	}
}