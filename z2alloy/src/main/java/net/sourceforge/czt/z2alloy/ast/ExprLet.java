package net.sourceforge.czt.z2alloy.ast;

public class ExprLet extends Expr {

    private final ExprVar label;
    private final Expr var;
    private final Expr sub;
	
    public ExprLet (ExprVar label, Expr var, Expr sub) {
    	super();
    	this.label = label;
    	this.var = var;
    	this.sub = sub;
    }
    
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public ExprLet copy() {
		return new ExprLet(label.copy(), var.copy(), sub.copy());
	}
	
	public Expr label() {
		return label.copy();
	}
	
	public Expr var() {
		return var.copy();
	}
	
	public Expr sub() {
		return sub.copy();
	}
	
	public String toString() {
		return "exprlet";
	}
}
