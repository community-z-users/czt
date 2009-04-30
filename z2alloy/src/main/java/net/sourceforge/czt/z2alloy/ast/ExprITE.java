package net.sourceforge.czt.z2alloy.ast;

public class ExprITE extends Expr {

    private final Expr cond;

    private final Expr left;

    private final Expr right;
    
    public ExprITE (Expr cond, Expr left, Expr right) {
    	this.cond = cond;
    	this.left = left;
    	this.right = right;
    }
    
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public ExprITE copy() {
		return new ExprITE(cond.copy(), left.copy(), right.copy());
	}
	
	public Expr cond() {
		return cond.copy();
	}
	
	public Expr left() {
		return left.copy();
	}
	
	public Expr right() {
		return right.copy();
	}
	
	public String toString() {
		return "exprite";
	}
	
}
