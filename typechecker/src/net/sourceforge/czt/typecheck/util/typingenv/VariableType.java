package net.sourceforge.czt.typecheck.util.typingenv;

import java.util.List;
import java.util.Vector;

import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;

public class VariableType implements Type {
	private static int serial = 0;
	private String name;

	public VariableType() {
		name = new String("_alpha_" + Integer.toString(serial++));
	}

	// create a variable type from a generic type
	public VariableType(String n) {
		name = n;
	}

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