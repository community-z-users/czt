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
 * FlagPredicate class implements the abstract class Predicate.
 * It represents that a predicate has "true" value or "false" value.
 *
 */
public class FlagPredicate implements Predicate{
	public String flag;
/**
 * Default constructor
 *
 * @param s It is an input string to indicate whether a predicate has "true" value
 * or "false" value.
 */
	public FlagPredicate(String s){
		flag = s;
	}
/**
 * Print out the FlagPredicate object.
 *
 * @return String It is a string whose value is "true" or "false".
 */
	public String toString(){
		return "Predicate is: " + flag;
	}
}
