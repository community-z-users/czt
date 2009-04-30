package net.sourceforge.czt.z2alloy.ast;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class Func {

	private final String label;

    private final boolean isPred;

    private final List<ExprVar> params;

    private final Expr returnDecl;
    
    private Expr body; 
    
    public Func (String label, List<ExprVar> params, Expr returnDecl) {
    	this.label = label;
    	this.isPred = false;
    	this.params = Collections.unmodifiableList(params);
    	this.returnDecl = returnDecl;
    	body = ExprConstant.TRUE;
    }
    
    public Func (String label, List<ExprVar> params) {
    	this.label = label;
    	this.isPred = true;
    	this.params = Collections.unmodifiableList(params);
    	this.returnDecl = null;
    	body = ExprConstant.TRUE;
    }
    
    public Expr getBody() {
    	return body;
    }
    
    public Expr setBody(Expr body) {
    	Expr temp = this.body;
    	this.body = body;
    	return temp;
    }

	public Expr call(List<Expr> args) {
		return new ExprCall(this, args);
	}
	
	public Expr call(Expr... args) {
		return new ExprCall(this, Arrays.asList(args));
	}   
	
	public String toString() {
		if (isPred) return "pred " + label;
		return "fun " + label;
	}

	public String label() {
		return label;
	}
	
	public boolean pred() {
		return isPred;
	}
	
	public boolean fun() {
		return !pred();
	}
	
	public List<ExprVar> params() {
		List<ExprVar> params = new ArrayList<ExprVar>();
		for (ExprVar param : this.params) params.add(param);
		return params;
	}
	
	public Expr returnDecl() {
		return returnDecl.copy();
	}
	
	public Expr body() {
		return body.copy();
	}
	
	public Func copy() {
		List<ExprVar> newParams = new ArrayList<ExprVar>();
		for (ExprVar exprvar : this.params) newParams.add(exprvar.copy());
		Func ret = isPred ? new Func(this.label, newParams) : new Func(this.label, newParams, this.returnDecl.copy());
		ret.body = body.copy();
		return ret;
	}

}
