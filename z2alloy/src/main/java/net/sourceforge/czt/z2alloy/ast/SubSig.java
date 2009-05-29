package net.sourceforge.czt.z2alloy.ast;


public class SubSig extends Sig {

	private final Sig parent;
	
	public SubSig (String label, Sig parent, Expr pred, boolean abs, boolean lone, boolean one, boolean some) {
		super (label, parent, abs, lone, one, one);
		for (Field f : parent) {
			addField(f);
		}
		this.parent = parent;
	}
	
	public SubSig (String label, Sig parent, Expr pred) {
		super (label, pred);
		for (Field f : parent) {
			addField(f);
		}
		this.parent = parent;
	}
	
	public SubSig (String label, Sig parent) {
		super (label);
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
