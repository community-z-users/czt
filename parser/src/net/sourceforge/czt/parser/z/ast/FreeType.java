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
 * FreeType class is used to represent the free types of Z specification.
 * It contains the varaible name and the list made up of Branch objects.
 *
 */
public class FreeType{
	public VarName n;
	public Vector bl;
/**
 * Default constructor
 *
 * @param n It is the varaible name to be assigned.
 * @param bl It is a vector that contains Branch objects.
 */
	public FreeType(VarName n, Vector bl){
		this.n = n;
		this.bl = bl;
	}
/**
 * Print out the FreeType object value.
 *
 * @return String A string to represent the FreeType object.
 */
	public String toString(){
		return "FreeType : " + n + " ::= " + bl;
	}
}
