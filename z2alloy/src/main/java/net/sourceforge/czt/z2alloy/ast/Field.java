package net.sourceforge.czt.z2alloy.ast;

public final class Field extends Expr {
	private final String label;
	private final Expr expr;

	public Field(String label, Expr expr) {
		this.label = label;
		this.expr = expr;
	}
	
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public String label() {
		return label;
	}
	
	public Expr expr() {
		return expr;
	}
	
	public String toString() {
		return label;
	}
}