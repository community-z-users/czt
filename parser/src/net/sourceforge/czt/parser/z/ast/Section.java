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
public class Section{
	public VarName n;
	public Vector v1;
	public Vector v2;
	public Vector narr;
	public int flag;
	public Section(VarName n, Vector nl, Vector pgs){
		this.n = n;
		v1 = nl;
		v2 = pgs;
	}
	public Section(VarName n, Vector v, int flag){
		this.n = n;
		v1 = v;
		this.flag = flag;
	}
	public Section(VarName n){
		this.n = n;
	}
	public Section(Vector v){
		narr = v;
	}
	public String toString(){
		if(v2 == null){
			if(v1 == null){
				return "section with one name only: "
				+ " beginzsect " + n + "  endzsect";
			}
			else{
				if(flag == 1){
					return "section has parents without paragraphs: "
					+ " beginzsect " + n + " parents " + v1 + " endzsect";
				}
				else if(flag == 2){
					return "section has parents without namelist: "
					+ " beginzsect " + n + " parents  endzsect paragraphs: " + v1 ;
				}
				else if(flag == 3){
					return "section has paragrpahs without parents: "
					+ " beginzsect " + n + " endzsect paragraphs: " + v1 ;
				}
				else{
					return "unmatched section type";
				}
			}
		}
		else{
			return "section has parents with namelist and paragraphs: "
			+ " beginzsect " + n + " parents " + v1+ " endzsect paragraphs: " + v2 ;
		}
	}
}
