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
 * InfixRel class implements the abstract class Relation.
 * It is used to present a relation that has infix relation operator.
 *
 */
public class InfixRel implements Expression{
	public Expression e1, e2;
	public String op;
/**
 * Default constructor
 *
 * @param e1 It is an expression object in front of the operator.
 * @param op It is the operator.
 * @param e2 It is an expression object behind the operator.
 *
 */
	public InfixRel(Expression e1, String op, Expression e2){
		this.e1 = e1;
		this.op = op;
		this.e2 = e2;
	}
/**
 * Print out the infix relation including two expressions and the operator.
 *
 * @return String A string to represent the InfixRel object.
 */
	public String toString(){
		return "InfixRel first expression: " + e1 + "  infixop: " + op + " second expression: " + e2;
	}
}
