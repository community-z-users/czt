package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public final class EmptyType implements Type {
	public List getAnns() {
		return new Vector();
	}

	public Object accept(Visitor visitor) {
		return this;
	}

	public Term create(Object[] args) {
		return null;
	}

	public Object[] getChildren() {
		return null;
	}
}