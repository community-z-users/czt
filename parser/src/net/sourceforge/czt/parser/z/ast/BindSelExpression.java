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

/**
 * BindSelExpression class implements the abstract class Expression.
 * It can represent an expression with one referred name.
 *
 */
public class BindSelExpression implements Expression{
	public Expression e;
	public VarName n;
/**
 * Default constructor
 *
 * @param e It is an expression.
 * @param n It is a referred name of VarName class.
 */
	public BindSelExpression(Expression e, VarName n){
		this.e = e;
		this.n = n;
	}
/**
 * Print out the BindSelExpression object.
 *
 * @return String A string to represent binding selection.
 */
	public String toString(){
		return "BindExpression with expression : " + e + " . and refname : " + n;
	}
}
