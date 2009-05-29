package net.sourceforge.czt.z2alloy.ast;


import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


public final class ExprCall extends Expr {

    /** The actual function being called; never null. */
    private final Func fun;

    /** The list of arguments to the call. */
    private final List<Expr> args;
    
    public ExprCall(Func fun, List<Expr> args) {
    	super();
    	this.fun = fun;
    	this.args = Collections.unmodifiableList(args);
    }
    
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public Func fun() {
		return fun;
	}
	
	public List<Expr> args() {
		List<Expr> args = new ArrayList<Expr>();
		for (Expr arg : this.args) args.add(arg);
		return args;
	}
	
	public String toString() {
		return "call" + fun.label();
	}
}
