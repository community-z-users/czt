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
public class ParPredicate implements Predicate{
	public String lhs, rhs;
	public Predicate p;
	public ParPredicate(String lhs, Predicate p, String rhs){
		this.lhs = lhs;
		this.p = p;
		this.rhs = rhs;
	}
	public String toString(){
		return "LHS: " + lhs + " Predicate: " + p + " RHS: " + rhs;
	}
}
