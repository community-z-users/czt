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

package net.sourceforge.czt.parser.z;
import java.util.*;


/**
 * OpMaps acts as a pool to store the use-defined operator.
 *
 * It interacts with LTZCompiler class, LTZparser class and LTZsym class.
 * It stores the user-defined operators from the LTZparser class, and assign
 * those operators to LTZsym class. LTZCompiler will look up it to check up
 * whether a word is user-defined or not.
 *
 */
public class OpMaps{
	public Hashtable ht;
/**
 * Default constructor
 *
 */
	public OpMaps(){
		ht = new Hashtable();
	}
/**
 * This method is to add the user-defined operator with corresponding
 * type.
 *
 * @param key it is the word of user-defined.
 * @param fix it is the type of the user-defined
 *
 */
	public void addOp(String key, String fix){
		ht.put(key, fix);
	}
/**
 * This is method to check whether an input word is in the pool or not.
 *
 * @param key it is the input word
 *
 * @return boolean return true if the word is inside the table, false otherwise.
 *
 */
	public boolean inMap(String key){
		return ht.containsKey(key);
	}
/**
 * This method is to return the corresponding type of a user-defined operator.
 *
 * @param key the user-defined operator inside the table.
 *
 * @return String return the correspoind type of the operator from the table.
 *
 */
	public String getOp(String key){
		return (String)ht.get(key);
	}
/**
 * This method is to print out the table contents.
 *
 */
	public String toString(){
		return ht.toString();
	}
}
