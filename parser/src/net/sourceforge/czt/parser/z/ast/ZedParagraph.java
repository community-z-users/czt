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

public class ZedParagraph{
	public int num;
	public Vector v;
	public Predicate pp;
	public SchemaText st;
	public OperatorTemp ot;
	public ZedParagraph(SchemaText st){
		this.st = st;
	}
	public ZedParagraph(OperatorTemp ot){
		this.ot = ot;
	}
	public ZedParagraph(int num, Vector nl){
		this.num = num;
		v = nl;
	}
	public ZedParagraph(Vector nl, SchemaText st){
		v = nl;
		this.st = st;
	}
	public ZedParagraph(Predicate pp){
		this.pp = pp;
	}
	public ZedParagraph(Vector nl, Predicate pp){
		v = nl;
		this.pp = pp;
	}
	public String toString(){
		if(ot != null)
			return " operator template: " + ot;
		else if(pp != null){
			if(v != null) return "Generic conjecture: [ " + v + " ] with predicate: " + pp;
			else return "conjecture: " + pp;
		}
		else{
			if(st != null){
				if(v == null)
					return "Horizontal defintion: " + st;
				else return "Generic horizontal defintion: "
				+ " namelist: "+ v + " expression: "+ st;
			}
			else{
				if(num == 1){ //it is a giventype definition
					return "Giventype: "+ v;
				}
				else return "Freetype: "+ v;
			}
		}
	}
}
