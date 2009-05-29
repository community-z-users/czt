package net.sourceforge.czt.z2alloy.ast;
public class ExprUnary extends Expr {

    private final Op op;
    private final Expr sub;

    public ExprUnary (Op op, Expr sub) {
    	super();
    	this.op = op;
    	this.sub = sub;
    }
    
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}

	
	public ExprUnary.Op op() {
		return op;
	}
	
	public Expr sub() {
		return sub;
	}
	
	public String toString() {
		return op + " " + sub;
	}
    
    public enum Op {
        /** :some x (where x is a unary set)                             */  SOMEOF("some of"),
        /** :lone x (where x is a unary set)                             */  LONEOF("lone of"),
        /** :one  x (where x is a unary set)                             */  ONEOF("one of"),
        /** :set  x (where x is a set or relation)                       */  SETOF("set of"),
        /** not   f (where f is a formula)                               */  NOT("!"),
        /** no    x (where x is a set or relation)                       */  NO("no"),
        /** some  x (where x is a set or relation)                       */  SOME("some"),
        /** lone  x (where x is a set or relation)                       */  LONE("lone"),
        /** one   x (where x is a set or relation)                       */  ONE("one"),
        /** transpose                                                    */  TRANSPOSE("~"),
        /** reflexive closure                                            */  RCLOSURE("*"),
        /** closure                                                      */  CLOSURE("^"),
        /** cardinality of x (truncated to the current integer bitwidth) */  CARDINALITY("#"),
        /** IntAtom-to-integer                                           */  CAST2INT("Int->int"),
        /** integer-to-IntAtom                                           */  CAST2SIGINT("int->Int");

        /** The constructor */
        private Op(String label) {this.label=label;}
        public String toString() {return label;}

        /** The human readable label for this operator */
        private final String label;
    }
}
