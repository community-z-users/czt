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
 * GenSchemaDef class implements the abstract class Paragraph.
 * It is used to represent the generic schema definition in Z specification.
 *
 */
public class GenSchemaDef implements Paragraph{
	public VarName n;
	public Vector namelist;
	public SchemaText st;
/**
 * Default constructor
 *
 * @param n It is the name of the schema.
 * @param nl It is the vector that consists of input parameters.
 * @param st It is a schematext object.
 */
	public GenSchemaDef(VarName n, Vector nl, SchemaText st){
		this.n = n;
		namelist = nl;
		this.st = st;
	}
/**
 * Print out the generic schema definition.
 *
 * @return String A string to represent the GenSchemaDef object.
 */
	public String toString(){
		return "The GenSchemadef name : " + n + " Namelist : "
		+ namelist.toString()+ " and Schematext : " + st;
	}
}

		

