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
 * InfixApp class implements the abstract class Application.
 * It is used to present the application which has infix function operator.
 *
 */
public class InfixApp implements Application{
	public Expression e1, e2;
	public String op;
/**
 * Default constructor
 *
 * @param e1 It is the expression object in front of the operator.
 * @param s It is the infix function operator.
 * @param e2 It is the expression object behind the operator.
 */
	public InfixApp(Expression e1, String s, Expression e2){
		this.e1 = e1;
		op = s;
		this.e2 = e2;
	}
/**
 * Print out the application with two expression and the operator.
 *
 * @return String A string to represent the InfixApp object.
 */
	public String toString(){
		return "infixapplication: " + e1 + " with operator: "
		+ op + " and second exp: " + e2;
	}
}
