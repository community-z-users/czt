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

/**
 * Declaration class represents three types of declaration in Z specification.
 *
 */
public class Declaration{
	public VarName n;
	public Vector namelist;
	public Expression e;
/**
 * Constructor for the constant declaration type "Name == Expression"
 *
 * @param n It is a VarName object.
 * @param e It is an expression.
 */
	public Declaration(VarName n, Expression e){
		this.n = n;
		this.e = e;
	}
/**
 * Constructor for the variable declaration type "Name {, Name} : Expression"
 *
 * @param nl It is vector consists of names.
 * @param e It is an expression.
 */
	public Declaration(Vector nl, Expression e){
		namelist = nl;
		this.e = e;
	}
/**
 * Constructor for the inclusion declaration type "Expression"
 *
 * @param e It is an expression of the declaration.
 *
 */
	public Declaration(Expression e){
		this.e = e;
	}
/**
 * Print out the declaration object.
 *
 * @return String A string to represent declaration.
 */
	public String toString(){
		if(n != null) return n + " == " + e;
		else if(namelist != null) return "Declname: "
		+ namelist.toString() + " : " + e;
		else return " " + e;
	}
}
