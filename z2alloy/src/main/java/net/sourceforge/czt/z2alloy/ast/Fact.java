package net.sourceforge.czt.z2alloy.ast;

public class Fact {

	private final Expr expr;
	private final String label;
	
	public Fact (Expr expr, String label) {
		this.expr = expr;
		this.label = label;
	}

	public String label() {
		return label;
	}
	
	public Expr expr() {
		return expr.copy();
	}
	
	public String toString() {
		return label;
	}
	
}
