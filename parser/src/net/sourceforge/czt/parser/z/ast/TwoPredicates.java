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

public class TwoPredicates implements Predicate{
	public Predicate p1, p2;
	public int flag;
	public TwoPredicates(Predicate p1, Predicate p2, int flag){
		this.p1 = p1;
		this.p2 = p2;
		this.flag = flag;
	}
	public String toString(){
		return "Two predicates with first predicate: " + p1
		+ " and operation type: " + flag + " and second predicate: " + p2;
	}
}
