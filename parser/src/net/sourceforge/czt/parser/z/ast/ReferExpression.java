/**
Copyright 2003 CHEN Chunqing.  chenchun@comp.nus.edu.sg
This file is part of the CZT project: http://czt.sourceforge.net

The CZT project contains free software; you can redistribute it and/or
modify it under the terms of the GNU General Public License as published
by the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should have received a copy of the GNU General Public License along 
with CZT; if not, write to the Free Software Foundation, Inc., 
59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.parser.z.ast;
import java.util.*;

public class ReferExpression implements Expression{
	public VarName vn;
	public Vector el;
	public String op;
	public Expression e;
	public ReferExpression(VarName nl){
		vn = nl;
	}
	public ReferExpression(VarName nl, Vector el){
		vn = nl;
		this.el = el;
	}
	public ReferExpression(String op, Expression e){
		this.op = op;
		this.e = e;
	}
	public ReferExpression(String op, Vector el){
		this.op = op;
		this.el = el;
	}
	public String toString(){
		if(op != null){
			if(e == null)
			 return "infix Generic instantiation with operator: " + op + " and expressionlist: " + el;
			else return "prefix generic instantiation with operator: " + op + " and expression: " + e;
		}
		else if(el == null) return "Reference : "+ vn;
		else return "ReferExpression with refername: "
			+ vn + " and expressionlist: " + el;
	}
}
