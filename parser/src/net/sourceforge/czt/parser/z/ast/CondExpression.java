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
 * CondExpression class implements the abstract class Expression.
 * It represents the conditional expression which is in the following format:
 * "if, Predicate, then, Expression, else, Expression"
 *
 */
public class CondExpression implements Expression{
	public Predicate p;
	public Expression e1, e2;
/**
 * Default constructor.
 *
 * @param pp It is a predicate object.
 * @param e1 It is an expression for the action of then result.
 * @param e2 It is an expression for the action of else result.
 */
	public CondExpression(Predicate pp, Expression e1, Expression e2){
		p = pp;
		this.e1 = e1;
		this.e2 = e2;
	}
/**
 * Print out the condExpression object.
 *
 * @return String It is a string to represent the conditional expression.
 */
	public String toString(){
		return "CondExpression if : " + p
		 + " then : " + e1 + " else : " + e2;
	}
}
