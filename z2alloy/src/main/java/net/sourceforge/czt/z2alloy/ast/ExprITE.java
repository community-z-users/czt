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
	
	public Expr cond() {
		return cond;
	}
	
	public Expr left() {
		return left;
	}
	
	public Expr right() {
		return right;
	}
	
	public String toString() {
		return "exprite";
	}
	
}
