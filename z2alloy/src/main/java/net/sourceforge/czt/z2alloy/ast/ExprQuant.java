package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public final class ExprQuant extends Expr {

    /** The operator (ALL, NO, LONE, ONE, SOME, SUM, or COMPREHENSION) */
    private final Op op;

    /** The unmodifiable list of variables. */
    private final List<ExprVar> vars;

    /** The body of the quantified expression. */
    private final Expr sub;

   public ExprQuant(Op op, List<ExprVar> vars, Expr sub) {
	   super();
	   this.op = op;
	   this.sub = sub;
	   this.vars = Collections.unmodifiableList(vars);
   }
   
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public Expr sub() {
		return sub;
	}
	
	public ExprQuant.Op op() {
		return op;
	}
	
	public List<ExprVar> vars() {
		List<ExprVar> vars = new ArrayList<ExprVar>();
		for (ExprVar var : this.vars) vars.add(var);
		return vars;
	}
    
    /** This class contains all possible quantification operators. */
    public enum Op {
        /** all  a,b:x | formula       */  ALL("all"),
        /** no   a,b:x | formula       */  NO("no"),
        /** lone a,b:x | formula       */  LONE("lone"),
        /** one  a,b:x | formula       */  ONE("one"),
        /** some a,b:x | formula       */  SOME("some"),
        /** sum  a,b:x | intExpression */  SUM("sum"),
        /** { a,b:x | formula }        */  COMPREHENSION("comprehension");

        /** The constructor. */
        private Op(String label) {this.label=label;}
        public String toString() {return label;}

        /** The human readable label for this operator. */
        private final String label;
    }
    
	public String toString() {
		return "exprquant: " + op + " | " + sub;
	}
}
