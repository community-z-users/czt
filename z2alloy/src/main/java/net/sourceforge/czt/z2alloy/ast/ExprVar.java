package net.sourceforge.czt.z2alloy.ast;

public class ExprVar extends Expr {
    private final String label;

    private final Expr expr;
    
    public ExprVar(String label, Expr expr) {
    	super();
    	this.label = label;
    	this.expr = expr;
    }
    
	public ExprVar(String label) {
		super();
		this.label = label;
		this.expr = null;
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
