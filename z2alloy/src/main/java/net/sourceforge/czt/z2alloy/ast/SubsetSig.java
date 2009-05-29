package net.sourceforge.czt.z2alloy.ast;


public class SubsetSig extends Sig {

	private final Sig parent;
	
	public SubsetSig (String label, Sig parent, Expr pred, boolean abs, boolean lone, boolean one, boolean some) {
		super (label, pred, abs, lone, one, one);
		for (Field f : parent) {
			addField(f);
		}
 		this.parent = parent;
	}
	
	public SubsetSig (String label, Sig parent, Expr pred) {
		super (label, pred);
		for (Field f : parent) {
			addField(f);
		}
		this.parent = parent;
	}
	
	public SubsetSig (String label, Sig parent) {
		super(label);
		for (Field f : parent) {
			addField(f);
		}
		this.parent = parent;
	}
	
	public <T> T accept(VisitReturn<T> visitor) {
		return visitor.visit(this);
	}
	
	public Sig parent() {return parent;}
	
}
