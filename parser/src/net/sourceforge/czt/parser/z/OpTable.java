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
 * OpTable acts as a table stores those predefined Z special symbols
 * in latex format and in XML format.
 *
 * It offers a mapping between special symbols in latex and XML format.
 * and it will be called by the LTZCompiler class.
 *
 */
public class OpTable{
	public Hashtable ht;
/**
 * Default constructor. It will build the table when it is initialized.
 *
 */
	public OpTable(){
		ht = new Hashtable();
		init();
	}
/**
 * This method is to check whether a word in the table or not.
 *
 * @param s the input word.
 *
 * @return boolean return true if the word is inside the table, fals otherwise.
 *
 */
	public boolean InTable(String s){
		return ht.containsKey(s);
	}
/**
 * This method is to return the correponding XML format of a predefined
 * latex word.
 *
 * @param s it is the Z special symbol in latex format
 *
 * @return String return the correponding XML format for the Z special symbol.
 *
 */
	public String GetOp(String s){
		return (String)ht.get(s);
	}
/**
 * This method is to set up the mapping table.
 *
 */
	private void init(){
		//number symbol
		ht.put("\\nat", "&nat;");
		ht.put("\\nat_1", "&natone;");
		ht.put("\\num", "&integer;");
		ht.put("\\real", "&real;");
		ht.put("\\div", "div");
		ht.put("\\mod", "mod");
		ht.put("\\neq", "&neq;");
		ht.put("\\leq", "&leq;");
		ht.put("\\geq", "&geq;");
		//logic
		ht.put("\\lnot", "&lnot;");
		ht.put("\\land", "&land;");
		ht.put("\\lor", "&lor;");
		ht.put("\\all", "&all;");
		ht.put("\\forall", "&all;");
		ht.put("\\exi", "&exi;");
		ht.put("\\exists", "&exi;");
		ht.put("\\exione", "&exione;");
		ht.put("\\exists_1", "&exione;");
		ht.put("\\nexi", "&nexi;");
		ht.put("\\dot", "&dot;");
		ht.put("\\spot", "&dot;");
		ht.put("@", "&dot;");
		ht.put("\\imp", "&imp;");
		ht.put("\\implies", "&imp;");
		ht.put("\\iff", "&iff;");
		ht.put("\\true", "true");
		ht.put("\\false", "false");
		//sets
		ht.put("\\{", "&startset;");
		ht.put("\\}", "&endset;");
		ht.put("|", "&cbar;");
		ht.put("\\cbar", "&cbar;");
		ht.put("\\emptyset", "&emptyset;");
		ht.put("\\mem", "&mem;");
		ht.put("\\in", "&mem;");
		ht.put("\\nem", "&nem;");
		ht.put("\\notin", "&nem;");
		ht.put("\\pset", "&pset;");
		ht.put("\\power", "&pset;");
		ht.put("\\fset", "&fset;");
		ht.put("\\finset", "&fset;");
		ht.put("\\psetone", "&psetone;");
		ht.put("\\fsetone", "&fsetone;");
		ht.put("\\uni", "&uni;");
		ht.put("\\union", "&uni;");
		ht.put("\\cup", "&uni;");
		ht.put("\\int", "&int;");
		ht.put("\\cap", "&int;");
		ht.put("\\subset", "&subset;");
		ht.put("\\psubs", "&subset;");
		ht.put("\\subseteq", "&subseteq;");
		ht.put("\\subs", "&subseteq;");
		ht.put("\\supset", "&supset;");
		ht.put("\\supseteq", "&supseteq;");
		ht.put("\\cross", "&prod;");
		ht.put("\\prod", "&prod;");
		ht.put("\\min", "min");
		ht.put("\\max", "max");
		ht.put("\\upto", "&upto;");
		ht.put("\\setminus", "\\");
		//relations and functions
		ht.put("\\lambda", "&lambda;");
		ht.put("\\mu", "&mu;");
		ht.put("\\dom", "dom");
		ht.put("\\ran", "ran");
		ht.put("\\fcmp", "&fcmp;");
		ht.put("\\comp", "&fcmp;");
		ht.put("\\circ", "&cmp;");
		ht.put("\\dres", "&dres;");
		ht.put("\\dsub", "&dsub;");
		ht.put("\\ndres", "&dsub;");
		ht.put("\\rres", "&rres;");
		ht.put("\\rsub", "&rsub;");
		ht.put("\\nrres", "&rsub;");
		ht.put("\\oplus", "&fovr;");
		ht.put("\\fovr", "&fovr;");
		ht.put("\\inv", "&inv;");
		ht.put("\\tcl", "&tcl;");
		ht.put("\\plus", "&tcl;");
		ht.put("\\map", "&map;");
		ht.put("\\mapsto", "&map;");
		ht.put("\\rel", "&rel;");
		ht.put("\\tfun", "&tfun;");
		ht.put("\\fun", "&tfun;");
		ht.put("\\tinj", "&tinj;");
		ht.put("\\inj", "&tinj;");
		ht.put("\\pfun", "&pfun;");
		ht.put("\\tsur", "&tsur;");
		ht.put("\\surj", "&tsur;");
		//sequence
		ht.put("\\seq", "seq");
		ht.put("\\emptyseq", "&emptyseq;");
		ht.put("\\lseq", "&lseq;");
		ht.put("\\langle", "&lseq;");
		ht.put("\\rseq", "&rseq;");
		ht.put("\\rangle", "&rseq;");
		ht.put("\\extract", "&ires;");
		ht.put("\\ires", "&ires;");
		ht.put("\\filter", "&sres;");
		ht.put("\\sres", "&sres;");
		ht.put("\\cat", "&cat;");
		ht.put("\\dcat", "&dcat;");
		//schema
		ht.put("\\Delta", "&delta;");
		ht.put("\\Xi", "&xi;");
		ht.put("\\project", "&zproject;");
		ht.put("\\hide", "&zhide;");
		ht.put("\\pipe", "&zpipe;");
		ht.put("\\theta", "&theta;");
		
		//special symbol
		ht.put("<", "ls");
		ht.put(">", "gt");
	}
}
		
