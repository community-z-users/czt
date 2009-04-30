package net.sourceforge.czt.z2alloy.ast;


public class SubsetSig extends Sig {

	private final Sig parent;
	
	public SubsetSig (String label, Sig parent, Expr pred, boolean abs, boolean lone, boolean one, boolean some) {
		super (label, pred, abs, lone, one, one);
		this.parent = parent;
	}
	
	public SubsetSig (String label, Sig parent, Expr pred) {
		super (label, pred);
		this.parent = parent;
	}
	
	public SubsetSig (String label, Sig parent) {
		super(label);
		this.parent = parent;
	}
	
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public SubsetSig copy() {
		return new SubsetSig(label(), parent.copy(), pred().copy(), isAbstract(), isLone(), isOne(), isSome());
	}
	
	public Sig parent() {return parent.copy();}
	
}
