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

import java_cup.runtime.*;
import java.util.*;
import java.io.*;
import net.sourceforge.czt.parser.z.ast.*;

/**
 * LTZCompiler performs the transformation of the direction from Latex to ZML.
 *
 *
 * It reads the source program which in Latex format from user's input
 * file, Then it apply the LTZscanner.java to scan the input source and
 * split them into meaningful tokens. After scanning, it apply the
 * LTZparser.java to consctruct the syntax tree of the source program. When
 * it get the syntax tree of the input source, it will translate the syntax
 * tree to corresponding ZML format based on the syntax and semantic
 * meaning.  */
public class LTZCompiler{
	public   PrintWriter pw;
	public   String fullfilename;
	public   String filename;
	public   boolean debug = true;
	public Exception exception;
	public OpMaps opmaps;
	public OpTable optable;
/**
 * Default Constructor -- does the parsing and writes the XML file.
 *   It throws an exception if any parse errors are found.
 *
 * @param fullname is the input file full name including the directory.
 * @param specname is the name of the specification.
 *          Usually this is the basename of the file (with directories
 *          and suffixes dropped).  It is used to name an anonymous Z
 *          section within the file.  It must be a legal Z identifier.
 * @param outname is the name of the XML file that will be created.
 *                  It should usually end with ".xml".
 *
 */
    public LTZCompiler(String fullname, String specname, String outname)
	throws Exception {
		optable = new OpTable();
		// record input names for later use (in error messages etc.).
		fullfilename = fullname;
		filename = specname;
		// StringTokenizer st = new StringTokenizer(fullname, ".");
		// fullfilename = (String)st.nextToken();
		FileInputStream input = new FileInputStream(fullname);
		BufferedReader stdin = new BufferedReader(new InputStreamReader(input));

		FileOutputStream outfile = new FileOutputStream(outname);
		pw = new PrintWriter(outfile);

		pw.println("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
		pw.println("<!DOCTYPE unicode SYSTEM \"http://nt-appn.comp.nus.edu.sg/fm/zml/unicode.dtd\">");
		pw.println("<Spec xmlns=\"http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT/zstd.xsd\"");
		pw.println("\t xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\"");
		pw.print("\t xsi:schemaLocation=\"http://web.comlab.ox.ac.uk/oucl/work/andrew.martin/CZT/zstd.xsd");
		pw.println(" http://www.comp.nus.edu.sg/~chenchun/ltfz/zstd.xsd \">");
		pw.flush();
		
		String s = "";
		String source = "";
		while((s = stdin.readLine()) != null){
//			if(s.startsWith("\\begin{document}")){
				//source = source.concat(s);
				//while(!((s = stdin.readLine()).startsWith("\\end{document}"))){
					source = source.concat(s);
				//}
		}
		try{
		    compile(source);
		}
		catch(Exception e) {
		    exception = e;
		}
		pw.println("</Spec>");
		pw.flush();
		outfile.close();
		System.out.println("Transformation is done" );
    }

/**
 * This method can print the blank space according to the layer of output. So the
 * output format will have indented shape.
 *
 * @param count an integer to indicate how many blank space need to print
 */
	public   void NicePrint(int count){
		for(int i = 0; i < (2*count); i++)
			pw.print(" ");
	}

/**
 * This method can translate an expression list.
 *
 * @param dummy A vector contains expressions.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaVector(Vector dummy, int count){
		for(int i = 0; i < dummy.size(); i++){
			Expression tempe = (Expression)dummy.elementAt(i);
			anaExpression(tempe, count);
		}
	}

/**
 * This method will parse the input string into a syntax tree which top is
 * a speicification. Start the translation from the root of the tree.
 *
 * @param input it is a string consists of original source program.
 *
 */
	public   void compile(String input)throws Exception{
		LTZparser p = new LTZparser(new LTZscanner(new StringReader(input)));
		opmaps = p.getOpMap();
		Specification spec = (Specification)p.parse().value;
		int count = 1;
		if(spec.flag == 1){//it contains sections
			Vector ss = (Vector)spec.v;
			for(int i = 0; i < ss.size(); i++){
				Section s = (Section)ss.elementAt(i);
				anaSection(s, count);
			}
		}
		else if(spec.flag == 2){ 
		        //create a default section.
			StringTokenizer st1 = new StringTokenizer(filename, ".");
			VarName vn = new VarName((String)st1.nextToken());
			Section s = new Section(vn, spec.v, 3);
			anaSection(s, count);
		}
		else{
			System.out.println("unmatched components of specification");
			return;
		}
	}
/**
 * This method is to analysis the sections part.
 *
 * @param sect it is a vector containing a list of sections.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaSection(Section sect, int count){
		if(sect.narr != null){
			NicePrint(count);
			pw.println("<NarrSect>");
			anaUnparsed((Vector)sect.narr, count+1);
			NicePrint(count);
			pw.println("</NarrSect>");
			pw.flush();
		}
		else{
			NicePrint(count);
			pw.println("<ZSect>");
			NicePrint(count+1);
			VarName vn = (VarName)sect.n;
			pw.println("<Name>" + vn.n + "</Name>");
			if(sect.v1 != null){
				if(sect.v2 != null){
					anaParents(sect.v1, count+1);
					anaParagraphs(sect.v2, count+1);
				}
				else{
					if(sect.flag == 1)
						anaParents(sect.v1, count+1);
					else if(sect.flag == 2 || sect.flag == 3)
						anaParagraphs(sect.v1, count+1);
					else{
						System.out.println("unmatched section");
						return;
					}
				}
			}
			NicePrint(count);
			pw.println("</ZSect>");
			pw.flush();
		}
	}
/**
 * This method is to analysis the parents of section.
 *
 * @param v it is vector contains the name of parents
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaParents(Vector v, int count){
		for(int i = 0; i < v.size(); i++){
			VarName vn = (VarName)v.elementAt(i);
			NicePrint(count);
			pw.println("<Parent>");
			NicePrint(count+1);
			pw.println("<Word>" + (String)vn.n + "</Word>");
			NicePrint(count);
			pw.println("</Parent>");
			pw.flush();
		}
	}
/**
 * This method is to analysis paragraphs based on the type of the paragraph.
 * e.g., the paragraph is a axiom definition or schema defintion, and so on.
 *
 * @param pgs it is a vector containing paragraphs to translate.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaParagraphs(Vector pgs, int count){
		for(int i = 0; i < pgs.size(); i++){
			Paragraph pg = (Paragraph)pgs.elementAt(i);
			if(pg instanceof AxiomDef) anaAxiomDef(pg, count);
			else if(pg instanceof SchemaDef) anaSchemaDef(pg, count);
			else if(pg instanceof GenSchemaDef) anaGenSchemaDef(pg, count);
			else if(pg instanceof GenAxiomDef) anaGenAxiomDef(pg, count);
			else if(pg instanceof ZedDef) anaZedDef(pg, count);
			else if(pg instanceof UnparsedPara) anaUnparsedPara(pg, count);
			else {
				System.out.println("No proper paragraph matches");
				return;
			}
		}
	}
/**
 * This method is to deal with those statments which is unparsed by the parser,
 * and embed them inside the <UnparsedPara> element in ZML
 *
 * @param pg it is a pragraph that can not be parsed by parser.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaUnparsedPara(Paragraph pg, int count){
		Vector nl = (Vector)((UnparsedPara)pg).v;
		NicePrint(count);
		pw.println("<NarrPara>");
		anaUnparsed(nl, count+1);
		NicePrint(count);
		pw.println("</NarrPara>");
		pw.flush();
	}
/**
 * This method is to convert the narrative statements word by word.
 * and keep those statements unchanged.
 *
 * @param nl it is a vector stores the words from narrative paragraph.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaUnparsed(Vector nl, int count){
		NicePrint(count+1);
		pw.println("<Content>");
		NicePrint(count+2);
		for(int i = 0; i < nl.size(); i++){
			pw.print((String)nl.elementAt(i));
			pw.print(" ");
		}
		pw.println();
		NicePrint(count+1);
		pw.println("</Content>");
		pw.flush();
	}
/**
 * This method is to transform an Axiom definition paragraph of Z specification.
 *
 * @param pg it is an axiom definition type paragraph of Z specification
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaAxiomDef(Paragraph pg, int count){
		AxiomDef ad = (AxiomDef)pg;
		SchemaText schtext = (SchemaText)ad.st;
		NicePrint(count);
		pw.println("<AxPara Box=\"AxBox\">");
		pw.flush();
		anaSchemaText(schtext, count+1);
		NicePrint(count);
		pw.println("</AxPara>");
		pw.flush();
	}
/**
 * This method is to transform a schema definition paragraph of Z specification
 *
 * @param pg it is a schema definition paragraph.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaSchemaDef(Paragraph pg, int count){
		SchemaDef sd = (SchemaDef)pg;
		VarName vn = (VarName)sd.n;
		SchemaText schtext = (SchemaText)sd.st;
		NicePrint(count);
		pw.println("<AxPara Box=\"SchBox\">");
		NicePrint(count+1);
		pw.println("<SchText>");
		NicePrint(count+2);
		pw.println("<ConstDecl>");
		NicePrint(count+3);
		pw.println("<DeclName>");
		pw.flush();
		anaVarName(vn, count+4);
		NicePrint(count+3);
		pw.println("</DeclName>");
		NicePrint(count+3);
		pw.println("<SchExpr>");
		pw.flush();
		
		anaSchemaText(schtext, count+4);
		
		NicePrint(count+3);
		pw.println("</SchExpr>");
		NicePrint(count+2);
		pw.println("</ConstDecl>");
		NicePrint(count+1);
		pw.println("</SchText>");
		NicePrint(count);
		pw.println("</AxPara>");
		pw.flush();
	}
/**
 * This method is to transform a generic schema definition paragraph of Z specification
 *
 * @param pg it is a generic schema definition paragraph.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaGenSchemaDef(Paragraph pg, int count){
		GenSchemaDef gsd = (GenSchemaDef)pg;
		VarName vn = (VarName)gsd.n;
		Vector nl = (Vector)gsd.namelist;
		SchemaText schtext = (SchemaText)gsd.st;
		//here choose the attribute 'box' as 'schbox' value.
		NicePrint(count);
		pw.println("<AxPara Box=\"SchBox\">");
		pw.flush();
		anaNameList(nl, count+1);
		
		NicePrint(count+1);
		pw.println("<SchText>");
		NicePrint(count+2);
		pw.println("<ConstDecl>");
		NicePrint(count+3);
		pw.println("<DeclName>");
		pw.flush();
		anaVarName(vn, count+4);
		NicePrint(count+3);
		pw.println("</DeclName>");
		NicePrint(count+3);
		pw.println("<SchExpr>");
		pw.flush();
		
		anaSchemaText(schtext, count+4);
		
		NicePrint(count+3);
		pw.println("</SchExpr>");
		NicePrint(count+2);
		pw.println("</ConstDecl>");
		NicePrint(count+1);
		pw.println("</SchText>");
		NicePrint(count);
		pw.println("</AxPara>");
		pw.flush();
	}
/**
 * This method is to transform a generic axiomatic description of Z specification
 *
 * @param pg it is a generic axiomatic paragraph.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaGenAxiomDef(Paragraph pg, int count){
		GenAxiomDef gad = (GenAxiomDef)pg;
		Vector nl = (Vector)gad.namelist;
		SchemaText schtext = (SchemaText)gad.st;
		NicePrint(count);
		pw.println("<AxPara Box=\"SchBox\">");
		pw.flush();
		
		anaNameList(nl, count+1);
		
		anaSchemaText(schtext, count+1);
		
		NicePrint(count);
		pw.println("</AxPara>");
		pw.flush();
	}
/**
 * This method is to analysis other types of paragraph of Z specification. They are
 * Horizontal definition, Generic horizontal definition, Generic operator definition,
 * Free types, Conjecture, Generic conjecture, Operator template and Given types.
 *
 * @param pg it is a paragraph.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaZedDef(Paragraph pg, int count){
		Vector zd = ((ZedDef)pg).zps;
		for(int i = 0; i < zd.size(); i++){
			ZedParagraph zp = (ZedParagraph)zd.elementAt(i);
			if(zp.pp != null){ //it is a conjecture definition
				NicePrint(count);
				pw.println("<ConjPara>");
				if(zp.v != null){ //it is a generic conjecture definition
					anaNameList((Vector)zp.v, count+1);
				}
				anaPredicate((Predicate)zp.pp, count+1);
				NicePrint(count);
				pw.println("</ConjPara>");
				pw.flush();
			}
			else if(zp.st != null){
				//it is a horizontal definition
				NicePrint(count);
				pw.println("<AxPara Box=\"OmitBox\">");
				pw.flush();
				if(zp.v != null)
				//in case it is generic horizontal defintion.
					anaNameList(zp.v, count+1);
				anaSchemaText(zp.st, count+1);
				NicePrint(count);
				pw.println("</AxPara>");
				pw.flush();
			}
			else if(zp.ot != null){
				//it is an operator template
				anaOperatorTemp((OperatorTemp)zp.ot, count);
			}
			else{
				if(zp.num == 1){ //the zedparagraph is a given type definition
					NicePrint(count);
					pw.println("<GivenPara>");
					pw.flush();
					anaNameList(zp.v, (count + 1));
					NicePrint(count);
					pw.println("</GivenPara>");
					pw.flush();
				}
				else if(zp.num == 2){ //it is a free type defintion and so far just for one freetype declaration
					Vector bl = (Vector)zp.v;
					NicePrint(count);
					pw.println("<FreePara>");
					for(int j = 0; j < bl.size(); j++){
						FreeType ft = (FreeType)bl.elementAt(j);
						anaFreeType(ft, count+1);
					}
					NicePrint(count);
					pw.println("</FreePara>");
					pw.flush();
				}
				else {
					System.out.println("unmatched zedparagraph type!" );
					return;
				}
			}
		}
	}
/**
 * This method is to analyze the operator template in Z specification.
 *
 * @param ot it is an OperatorTemp object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaOperatorTemp(OperatorTemp ot, int count){
		int num = (int)ot.flag;
		CategoryTemp ctemp = (CategoryTemp)ot.ct;
		Template ttemp = (Template)ot.t;
		if(ctemp == null){
			//indicate it is relational template
			NicePrint(count);
			pw.println("<OptempPara Cat=\"Relation\">");
			anaTemplate(ttemp, count+1);
			NicePrint(count);
			pw.println("</OptempPara>");
		}
		else{
			if(num == 1){
				//it is a funcation category
				NicePrint(count);
				pw.print("<OptempPara Cat=\"Function\"");
				anaCategoryTemp(ctemp, count+1);
				NicePrint(count);
				pw.println("</OptempPara>");
			}
			else if(num == 2){
				//it is a generic category
				NicePrint(count);
				pw.print("<OptempPara Cat=\"Generic\"");
				anaCategoryTemp(ctemp, count+1);
				NicePrint(count);
				pw.println("</OptempPara>");
			}
			else{
				System.err.println("unmatched operator template");
			}
		}
		pw.flush();
	}
/**
 * This method is to analyze the Category template in Z specification.
 *
 * @param ct it is a CategoryTemp object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaCategoryTemp(CategoryTemp ct, int count){
		String prec = (String)ct.num;
		String asso = (String)ct.assoc;
		Template ttemp = (Template)ct.t;
		if(asso != null){
			//it is a infix template with association
			pw.println(" Assoc=\"" + asso + "\" Prec=\"" + prec + "\">");
		}
		else if(prec != null){
			pw.println(" Prec=\"" + prec + "\">");
		}
		anaTemplate(ttemp, count);
	}
/**
 * This method is to deal with the template in Z specification.
 *
 * @param t it is a Template object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTemplate(Template t, int count){
		VarName vname = (VarName)t.vn;
		String s = (String)vname.n;
		if(opmaps.inMap(s)){
			String relation = (String)opmaps.getOp(s);
			if(relation.equals("infixrel")){
				//it is an infix template
				NicePrint(count);
				pw.println("<Operand/>");
				NicePrint(count);
				pw.println("<Word>" + s + "</Word>");
				NicePrint(count);
				pw.println("<Operand/>");
			}
			else if(relation.equals("postfixrel")){
				//it is a postfix template
				NicePrint(count);
				pw.println("<Operand/>");
				NicePrint(count);
				pw.println("<Word>" + s + "</Word>");
			}
			else if(relation.equals("prefixrel")){
				NicePrint(count);
				pw.println("<Word>" + s + "</Word>");
				NicePrint(count);
				pw.println("<Operand/>");
			}
			else System.err.println("Unmatched template type!");
		}
		else System.err.println("operator is not defined in the table!");
	}
	
/**
 * This method is to transform the free type
 *
 * @param  ft it is an object which has object "name" and "branch".
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaFreeType(FreeType ft, int count){
		NicePrint(count);
		pw.println("<FreeType>");
		NicePrint(count+1);
		pw.println("<DeclName>");
		pw.flush();
		anaVarName(ft.n, count+2);
		NicePrint(count+1);
		pw.println("</DeclName>");
		pw.flush();
		Vector blist = (Vector)ft.bl;
		for(int j = 0; j < blist.size(); j++){
			Branch b = (Branch)blist.elementAt(j);
			anaBranch(b, count+1);
		}
		NicePrint(count);
		pw.println("</FreeType>");
		pw.flush();
	}
/**
 * This method is to transform a schema text.
 *
 * @param st it is an object "SchemaText" which contains object "declaraion"s and "predicate"s.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaSchemaText(SchemaText st, int count){
		Vector dp = (Vector)st.declpart;
		Predicate pp = (Predicate)st.p;
		NicePrint(count);
		pw.println("<SchText>");
		pw.flush();
		for(int i = 0; i < dp.size(); i++){
			//assume the schematext must have declarations
			Declaration d = (Declaration)dp.elementAt(i);
			anaDeclaration(d, count+1);
		}
		if(pp != null) //exists predicates
			anaPredicate(pp, count+1);
		NicePrint(count);
		pw.println("</SchText>");
		pw.flush();
	}
/**
 * This method is to transform a declaration based on the types of the declaration.
 * The generated ZML will be one of the three types below: <VarDecl>, <ConstDecl> or
 * <InclDecl>.
 *
 * @param d It is a declaration object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaDeclaration(Declaration d, int count){
		VarName vn = d.n;
		Vector nl = d.namelist;
		Expression exp = d.e;
		if(nl != null){ //correspondes to <VarDecl> in ZML
			NicePrint(count);
			pw.println("<VarDecl>");
			pw.flush();
			anaNameList(nl, count+1);
			anaExpression(exp, count+1);
			NicePrint(count);
			pw.println("</VarDecl>");
			pw.flush();
		}
		else if(vn != null){ //corresponding to <ConstDecl> in ZML
			NicePrint(count);
			pw.println("<ConstDecl>");
			NicePrint(count+1);
			pw.println("<DeclName>");
			pw.flush();
			anaVarName(vn, count+2);
			NicePrint(count+1);
			pw.println("</DeclName>");
			anaExpression((Expression)d.e, count+1);
			NicePrint(count);
			pw.println("</ConstDecl>");
			pw.flush();
		}
		else{ //corresponding to <InclDecl> in ZML
			NicePrint(count);
			pw.println("<InclDecl>");
			pw.flush();
			anaExpression(exp, count+1);
			NicePrint(count);
			pw.println("</InclDecl>");
			pw.flush();
		}
	}
/**
 * This method is to transform a branch which has below format:
 * Branch = DeclName, [ <<, Expression ,>>, ]
 *
 * @param b It is a Branch object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaBranch(Branch b, int count){
		VarName vn = (VarName)b.n;
		Expression exp = (Expression)b.e;
		NicePrint(count);
		pw.println("<Branch>");
		NicePrint(count+1);
		pw.println("<DeclName>");
		pw.flush();
		anaVarName(vn, count+2);
		NicePrint(count+1);
		pw.println("</DeclName>");
		pw.flush();
		if(exp != null){
			anaExpression(exp, count+1);
		}
		NicePrint(count);
		pw.println("</Branch>");
		pw.flush();
	}
/**
 * This method is to transform a predicate based on its type.
 *
 * @param p It is a predicate object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaPredicate(Predicate p, int count){
		if(p instanceof TwoPredicate){
			anaTwoPredicate((TwoPredicate)p, count);
		}
		else if(p instanceof ExpPredicate){
			Expression exp = (Expression)((ExpPredicate)p).e;
			anaExpPred(exp, count);
		}
		else if(p instanceof FlagPredicate){
			String s = (String)((FlagPredicate)p).flag;
			anaFlagPred(s, count);
		}
		else{
			System.out.println("Unmatched predicate type!");
			return;
		}
	}
/**
 * This method is to transform predicates which contains two predicates.
 * They are: newline conjunction, semicolon conjunction, equivalence, implication,
 * disjunction and conjunction.
 *
 * @param tp It is a predicate object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTwoPredicate(TwoPredicate tp, int count){
		String s = (String)tp.op;
		Predicate pd1 = (Predicate)tp.p1;
		Predicate pd2 = (Predicate)tp.p2;
		String head = "";
		String tail = "";
		if(s.equals("NL")){
			head = "<AndPred Op=\"NL\">";
			tail = "</AndPred>";
		}
		else if(s.equals("Semi")){
			head = "<AndPred Op=\"Semi\">";
			tail = "</AndPred>";
		}
		else if(s.equals("\\implies")){
			head = "<ImpliesPred>";
			tail = "</ImpliesPred>";
		}
		else if(s.equals("\\iff")){
			head = "<IffPred>";
			tail = "</IffPred>";
		}
		else if(s.equals("\\land")){
			head = "<AndPred Op=\"And\">";
			tail = "</AndPred>";
		}
		else if(s.equals("\\lor")){
			head = "<OrPred>";
			tail = "</OrPred>";
		}
		else{
			System.out.println("unmatched two predicates type!");
			return;
		}
		NicePrint(count);
		pw.println(head);
		anaPredicate(pd1, count+1);
		anaPredicate(pd2, count+1);
		NicePrint(count);
		pw.println(tail);
		pw.flush();
	}
/**
 * This method is to transform predicates which is true or false type.
 *
 * @param s It is a string to indicate whether the predicate is true or not.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaFlagPred(String s, int count){
		NicePrint(count);
		if(s.equals("true")){
			pw.println("<TruePred/>");
			pw.flush();
		}
		else{
			pw.println("<FalsePred/>");
			pw.flush();
		}
	}
/**
 * This method is to transform predicate which is an expression.
 *
 * @param e It is an expression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaExpPred(Expression e, int count){
		if(e instanceof SchemaExpression){
			SchemaExpression se = (SchemaExpression)e;
			String oper = (String)se.op;
			if(oper.equals("\\forall") || oper.equals("\\exists")||oper.equals("\\existsone")){
				anaQuaPred(oper, se, count);
			}
			else{
				anaTrueExpPred(e, count);
			}
		}
		else if(e instanceof TwoExpression){
			TwoExpression te = (TwoExpression)e;
			String oper = (String)te.op;
			if(oper.equals("\\implies") || oper.equals("\\iff")||oper.equals("\\land")||oper.equals("\\lor")){
				ExpPredicate ep1 = new ExpPredicate((Expression)te.e1);
				ExpPredicate ep2 = new ExpPredicate((Expression)te.e2);
				TwoPredicate tp = new TwoPredicate(ep1, oper, ep2);
				anaTwoPredicate(tp, count);
			}
			else{
				anaTrueExpPred(e, count);
			}
		}
		else if(e instanceof SingleExpression){
			SingleExpression se = (SingleExpression)e;
			String s = (String)se.op;
			if(s.equals("\\lnot")){
				anaSinglePred((Expression)se.e, count);
			}
			else
				anaTrueExpPred(e, count);
		}
		else if(e instanceof PrefixRel){
			PrefixRel pr = (PrefixRel)e;
			anaPrefixRel(pr, count);
		}
		else if(e instanceof InfixRel){
			anaInfixRel((InfixRel)e, count);
		}
		else if(e instanceof ChainRel){
			anaChainRel((ChainRel)e, count);
		}
		else{
			anaTrueExpPred(e, count);
		}
		pw.flush();
	}
/**
 * This method is to analyze the Negate Predicate in Z specification.
 * and it shares the same structure with negate expression.
 *
 * @param e it is an expression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSinglePred(Expression e, int count){
		NicePrint(count);
		pw.println("<NegPred>");
		anaExpPred(e, count+1);
		NicePrint(count);
		pw.println("</NegPred>");
		pw.flush();
	}
	public void anaQuaPred(String oper, SchemaExpression se, int count){
		String title = "";
		String tail = "";
		if(oper.equals("\\forall")){
			title = "<ForallPred>";
			tail = "</ForallPred>";
		}
		else if(oper.equals("\\exists")){
			title = "<ExistsPred>";
			tail = "</ExistsPred>";
		}
		else if(oper.equals("\\existsone")){
			title = "<Exists1Pred>";
			tail = "</Exists1Pred>";
		}
		else{
			System.out.println("unmatch qualification predicate type!");
			return;
		}
		NicePrint(count);
		pw.println(title);
		anaSchemaText((SchemaText)se.st, count+1);
		ExpPredicate ep = new ExpPredicate((Expression)se.e);
		anaPredicate(ep, count+1);
		NicePrint(count);
		pw.println(tail);
		pw.flush();
	}
/**
 * This method is to analyze the predicate which is an expression
 * as format : predicate ::= expression.
 *
 * @param e it is an expression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTrueExpPred(Expression e, int count){
		NicePrint(count);
		pw.println("<ExprPred>");
		pw.flush();
		anaExpression(e, count+1);
		NicePrint(count);
		pw.println("</ExprPred>");
		pw.flush();
	}

/**
 * This method is to convert the chain relation into chain
 * predicates. e.g., a < b < c ==> a < b ^ b < c.
 *
 * @param r It is a relation type.
 * @param count It indicates how many blank spaces need to print.
 *
 */
	public void anaChainRel(ChainRel cr, int count){
		Vector rellist = (Vector)cr.v;
		String oper1 = (String)rellist.remove(0);
		Expression e2 = (Expression)rellist.remove(0);
		Expression e1 = (Expression)cr.e;
		NicePrint(count);
		pw.println("<AndPred Op=\"Chain\">");
		InfixRel ir1 = new InfixRel(e1, oper1, e2);
		anaInfixRel(ir1, count+1);
		if(rellist.size() == 2){
			String oper2 = (String)rellist.remove(0);
			Expression e3 = (Expression)rellist.remove(0);
			InfixRel ir2 = new InfixRel(e2, oper2, e3);
			anaInfixRel(ir2, count+1);
		}
		else{
			ChainRel newcr = new ChainRel(e2, rellist);
			anaChainRel(newcr, count+1);
		}
		NicePrint(count);
		pw.println("</AndPred>");
		pw.flush();
	}

/**
 * This method is to transform a relation which has prefix relation operator.
 *
 * @param r It is a relation object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaPrefixRel(PrefixRel pr, int count){
		NicePrint(count);
		pw.println("<MemPred>");
		pw.flush();
		Expression exp = (Expression)pr.e;
		anaExpression(exp, count+1);
		String operator = (String)pr.pre;
		VarName vn = new VarName(operator);
		ReferExpression reexp = new ReferExpression(vn);
		anaRefExpr(reexp, count+1);
		NicePrint(count);
		pw.println("</MemPred>");
		pw.flush();
	}
/**
 * This method is to transform a relation which has infix relation operator.
 *
 * @param r It is a relation object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaInfixRel(InfixRel ir, int count){
		//only concern infix relation symbol and convert
		//those x + y --> (x, y) \in (- + -) format
		//then consider the first parenthesis pair as <TupleExpr> element
		//and the second parenthesis pair as <RefExpr> element.
		NicePrint(count);
		pw.println("<MemPred>");
		pw.flush();
		Expression first = (Expression)ir.e1;
		Expression second = (Expression)ir.e2;
		String operator = (String)ir.op;
		Vector v = new Vector();
		v.addElement(first);
		v.addElement(second);
		TupleExpression pe = new TupleExpression(v);
		anaExpression(pe, count+1);
		
		VarName vn = new VarName(operator);
		ReferExpression reexp = new ReferExpression(vn);
		anaRefExpr(reexp, count+1);
		NicePrint(count);
		pw.println("</MemPred>");
		pw.flush();
	}
/**
 * This method is to transform a reference expression.
 *
 * @param e It is an ReferExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaRefExpr(Expression e, int count){
		ReferExpression re = (ReferExpression)e;
		VarName v = (VarName)re.vn;
		Vector explist = (Vector)re.el;
		String operator = (String)re.op;
		Expression exp = (Expression)re.e;
		if(v == null){ //it is a generic instantiating expression
			NicePrint(count);
			pw.println("<RefExpr Mixfix=\"true\">");
			NicePrint(count+1);
			pw.println("<RefName>");
			VarName vn = new VarName(operator);
			anaVarName(vn, count+2);
			NicePrint(count+1);
			pw.println("</RefName>");
			pw.flush();
		}
		else{
			NicePrint(count);
			pw.println("<RefExpr>");
			NicePrint(count+1);
			pw.println("<RefName>");
			pw.flush();
			anaVarName(v, count+2);
			NicePrint(count+1);
			pw.println("</RefName>");
			pw.flush();
		}
		if(exp != null)
			anaExpression(exp, count+1);
		if(explist != null)
			anaVector(explist, count+1);
		
		NicePrint(count);
		pw.println("</RefExpr>");
		pw.flush();
	}
/**
 * This method is to transform expressions which contain a single expression.
 *
 * @param e It is a SingleExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaSingleExpr(Expression e, int count){
		SingleExpression se = (SingleExpression)e;
		String operator = (String)se.op;
		Expression exp = (Expression)se.e;
		String s1 = "";
		String s2 = "";
		if(operator.equals("\\lnot")){
			s1 = "<NegExpr>";
			s2 = "</NegExpr>";
		}
		else if(operator.equals("\\power")){
			s1 = "<PowerExpr>";
			s2 = "</PowerExpr>";
		}
		else if(operator.equals("\\pre")){
			s1 = "<PreExpr>";
			s2 = "</PreExpr>";
		}
		else if(operator.equals("\\theta")){
			s1 = "<ThetaExpr>";
			s2 = "</ThetaExpr>";
		}
		else{
			System.out.println("Undefined type in singleexpression, error occurs");
			return;
		}
		NicePrint(count);
		pw.println(s1);
		if((exp instanceof DecorExpression)&&(operator.equals("theat"))){
			DecorExpression dexp = (DecorExpression)exp;
			anaExpression((Expression)dexp.e, count+1);
			NicePrint(count+1);
			pw.print("<Stroke>");
			anaStroke((String)dexp.st, count+2);
			NicePrint(count+1);
			pw.println("</Stroke>");
			pw.flush();
		}
		else
			anaExpression(exp, count+1);
		NicePrint(count);
		pw.println(s2);
		pw.flush();
	}
/**
 * This method is to transform applications.
 *
 * @param exp It is an Application object
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaAppExpr(Expression exp, int count){
		//like the transformation of Relation,
		//here we have:
		//x + y ==> (-+-)(x, y)
		//R* ==> (-*)R
		//only consider function operators
		ApplExpression e = (ApplExpression)exp;
		Application aapp = (Application)e.app;
		NicePrint(count);
		pw.println("<ApplExpr>");
		pw.flush();
		if(aapp instanceof InfixApp)
			anaInfixApp(aapp, count+1);
		else if(aapp instanceof NofixApp)
			anaNofixApp(aapp, count+1);
		else if(aapp instanceof PrefixApp)
			anaPrefixApp(aapp, count+1);
		else //here treat prefix and postfix operator the same
			anaPostfixApp(aapp, count+1);
		NicePrint(count);
		pw.println("</ApplExpr>");
		pw.flush();
	}
/**
 * This method is to analyze the nofix application.
 * For example to the operator of sequence "< >"
 *
 * @param app it is an application object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaNofixApp(Application app, int count){
		NofixApp na = (NofixApp)app;
		String first = (String)na.s1;
		String second = (String)na.s2;
		if(optable.InTable(first)){
			first = (String)optable.GetOp(first);
			second = (String)optable.GetOp(second);
		}
		String temp = first + " " + second;
		VarName vn = new VarName(temp);
		ReferExpression re = new ReferExpression(vn);
		anaRefExpr(re, count);
		anaExpression((Expression)na.e, count+1);
	}
/**
 * This method is to transform an application which has an infix function operator.
 *
 * @param app It is an application object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaInfixApp(Application app, int count){
		InfixApp iapp = (InfixApp)app;
		VarName vn = new VarName((String)iapp.op);
		ReferExpression re = new ReferExpression(vn);
		anaRefExpr(re, count);
		Vector v = new Vector();
		v.addElement(iapp.e1);
		v.addElement(iapp.e2);
		TupleExpression pe = new TupleExpression(v);
		anaExpression(pe, count);
	}
/**
 * This method is to transform an application which has prefix function operators.
 *
 * @param app It is an application object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaPrefixApp(Application app, int count){
		PrefixApp prapp = (PrefixApp)app;
		VarName vn = new VarName((String)prapp.op);
		ReferExpression re = new ReferExpression(vn);
		anaExpression(re, count);
		anaExpression((Expression)prapp.e, count);
	}
/**
 * This method is to transform an application which has postfix function operators.
 *
 * @param app It is an application object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaPostfixApp(Application app, int count){
		PostfixApp poapp = (PostfixApp)app;
		VarName vn = new VarName((String)poapp.op);
		ReferExpression re = new ReferExpression(vn);
		anaExpression(re, count);
		anaExpression((Expression)poapp.e, count);
	}
/**
 * This method is to transform a number exxpression
 *
 * @param e It is a number.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaNumExpr(Expression e, int count){
		NumberExpression ne = (NumberExpression)e;
		NicePrint(count);
		pw.println("<NumExpr Value=\"" + (String)ne.n + "\"/>");
		pw.flush();
	}
/**
 * This method is to transform expression which is a set extenstion.
 *
 * @param e It is a SetExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSetExpr(Expression e, int count){
		SetExpression se = (SetExpression)e;
		Vector explist = (Vector)se.el;
		if(explist == null){ //empty set
			NicePrint(count);
			pw.println("<SetExpr/>");
			pw.flush();
		}
		else{
			NicePrint(count);
			pw.println("<SetExpr>");
			anaVector(explist, count+1);
			NicePrint(count);
			pw.println("</SetExpr>");
			pw.flush();
		}
	}
/**
 * This method will do nothing when the expression is enclosed by a pair of
 * parenthesis.
 *
 * @param Exp It is a expression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaParentExpr(Expression exp, int count){
		ParentExpression pe = (ParentExpression)exp;
		anaExpression(pe.e, count);
	}
/**
 * This method is to transform expression which is a tuple extenstion
 *
 * @param e It is a TupleExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTupleExpr(Expression e, int count){
		TupleExpression te = (TupleExpression)e;
		Vector explist = (Vector)te.el;
		NicePrint(count);
		pw.println("<TupleExpr>");
//System.out.println("size of tuple is: " + explist.size());
		anaVector(explist, count+1);
		NicePrint(count);
		pw.println("</TupleExpr>");
	}
/**
 * This method is to transform an expression which is a cartesian product.
 *
 * @param exp It is a CardExpression object
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaCardExpr(Expression exp, int count){
		CardExpression ce = (CardExpression)exp;
		Vector explist = (Vector)ce.el;
		NicePrint(count);
		pw.println("<ProdExpr>");
		anaVector(explist, count+1);
		NicePrint(count);
		pw.println("</ProdExpr>");
		pw.flush();
	}
/**
 * This method is to transform the expression which is a binding extension.
 *
 * @param exp It is a BindExtendExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaBindExpr(Expression exp, int count){
		BindExtendExpression be = (BindExtendExpression)exp;
		Vector eqlist = (Vector)be.eql;
		if(eqlist == null){
			NicePrint(count);
			pw.println("<BindExpr/>");
			pw.flush();
		}
		else{
			NicePrint(count);
			pw.println("<BindExpr>");
			anaEqlist(eqlist, count+1);
			NicePrint(count);
			pw.println("</BindExpr>");
			pw.flush();
		}
	}
/**
 * This method is to transform those equal expression "DeclName == Expression"
 * inside the BindExtendExpression object.
 *
 * @param eql It is a vector contains equal expressions.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaEqlist(Vector eql, int count){
		for(int i = 0; i < eql.size(); i++){
			EqualDecl ed = (EqualDecl)eql.elementAt(i);
			VarName edvn = (VarName)ed.n;
			Expression tempe = (Expression)ed.e;
			NicePrint(count);
			pw.println("<Name>");
			anaVarName(edvn, count+1);
			NicePrint(count);
			pw.println("</Name>");
			pw.flush();
			anaExpression(tempe, count);
		}
	}
/**
 * This method is to transform a tuple selection expression.
 *
 * @param exp It is a TupleSelExpression Object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTupleSelExpr(Expression exp, int count){
		TupleSelExpression tse = (TupleSelExpression)exp;
		Expression tempe = (Expression)tse.e;
		String num = (String)tse.n;
		NicePrint(count);
		pw.println("<TupleSelExpr Select=\"" + num + "\">");
		anaExpression(tempe, count+1);
		NicePrint(count);
		pw.println("</TupleSelExpr>");
	}
/**
 * This method is to transform a binding selection expression.
 *
 * @param exp It is a BindSelExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaBindSelExpr(Expression exp, int count){
		BindSelExpression bse = (BindSelExpression)exp;
		NicePrint(count);
		pw.println("<BindSelExpr>");
		anaExpression(bse.e, count+1);
		NicePrint(count+1);
		pw.println("<Name>");
		anaVarName(bse.n, count+2);
		NicePrint(count+1);
		pw.println("</Name>");
		NicePrint(count);
		pw.println("</BindSelExpr>");
		pw.flush();
	}
/**
 * This method is to transform a conditional expression.
 *
 * @param exp It is a CondExpression object
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaCondExpr(Expression exp, int count){
		CondExpression ce = (CondExpression)exp;
		NicePrint(count);
		pw.println("<CondExpr>");
		Predicate pp = (Predicate)ce.p;
		anaPredicate(pp, count+1);
		anaExpression(ce.e1, count+1);
		anaExpression(ce.e2, count+1);
		NicePrint(count);
		pw.println("</CondExpr>");
		pw.flush();
	}
/**
 * This method is to transform a schema decoration expression.
 *
 * @param exp It is an expression with stroke.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaDecorExpr(Expression exp, int count){
		DecorExpression de = (DecorExpression)exp;
		NicePrint(count);
		pw.println("<DecorExpr>");
		anaExpression((Expression)de.e, count+1);
		NicePrint(count+1);
		pw.println("<Decor>");
		anaStroke((String)de.st, count+2);
		NicePrint(count+1);
		pw.println("</Decor>");
		NicePrint(count);
		pw.println("</DecorExpr>");
		pw.flush();
	}
/**
 * This method is to transform a schema construction expression
 *
 * @param exp It is a SchExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSchExpr(Expression exp, int count){
		SchExpression sche = (SchExpression)exp;
		NicePrint(count);
		pw.println("<SchExpr>");
		anaSchemaText(sche.st, count+1);
		NicePrint(count);
		pw.println("</SchExpr>");
		pw.flush();
	}
/**
 * This method is to transform a schema renaming expression.
 *
 * @param exp It is a ReNameExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaReNameExpr(Expression exp, int count){
		ReNameExpression rne = (ReNameExpression)exp;
		Vector rnlist = (Vector)rne.rnl;
		NicePrint(count);
		pw.println("<RenameExpr>");
		anaExpression(rne, count+1);
		for(int i = 0; i < rnlist.size(); i++){
			ReName rn = (ReName)rnlist.elementAt(i);
			anaReName(rn, count+1);
		}
		NicePrint(count);
		pw.println("</RenameExpr>");
		pw.flush();
	}
/**
 * This method is to transform the rename part of the schema renaming expression.
 *
 * @param rn It is a ReName Object which has two names, and one is the original name,
 *  the other is updated name.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaReName(ReName rn, int count){
		NicePrint(count);
		pw.println("<NewName>");
		anaVarName(rn.n1, count+1);
		NicePrint(count);
		pw.println("</NewName>");
		NicePrint(count);
		pw.println("<OldName>");
		anaVarName(rn.n2, count+1);
		NicePrint(count);
		pw.println("</OldName>");
		pw.flush();
	}
/**
 * This method is to transform expressions which contain two other expressions.
 * The operator between these two expressions can be "composition", "pipe" and
 * "project".
 *
 * @param exp It is a TwoExpression Object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaTwoExpr(Expression exp, int count){
		TwoExpression te = (TwoExpression)exp;
		String operator = (String)te.op;
		String title = "";
		String end = "";
		if(operator.equals("\\comp")){
			title = "<CompExpr>";
			end = "</CompExpr>";
		}
		else if(operator.equals("\\pipe")){
			title = "<PipeExpr>";
			end = "</PipeExpr>";
		}
		else if(operator.equals("\\project")){
			title = "<ProjExpr>";
			end = "</ProjExpr>";
		}
		else if(operator.equals("\\implies")){
			title = "<ImpExpr>";
			end = "</ImpExpr>";
		}
		else if(operator.equals("\\iff")){
			title = "<IffExpr>";
			end = "</IffExpr>";
		}
		else if(operator.equals("\\land")){
			title = "<AndExpr>";
			end = "</AndExpr>";
		}
		else if(operator.equals("\\lor")){
			title = "<OrExpr>";
			end = "</OrExpr>";
		}
		else {
			System.out.println("unmatched binary operators between expressions");
			return;
		}
		NicePrint(count);
		pw.println(title);
		anaExpression(te.e1, count+1);
		anaExpression(te.e2, count+1);
		NicePrint(count);
		pw.println(end);
		pw.flush();
	}
/**
 * This method is to transform a schema hiding expression.
 *
 * @param exp It is a SchemaHideExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSchemaHideExpr(Expression exp, int count){
		SchemaHideExpression she = (SchemaHideExpression)exp;
		NicePrint(count);
		pw.println("<HideExpr>");
		anaExpression(she.e, count+1);
		Vector nl = (Vector)she.namelist;
		for(int i = 0; i < nl.size(); i++){
			VarName vn = (VarName)nl.elementAt(i);
			NicePrint(count+1);
			pw.println("<Hide>");
			anaVarName(vn, count+2);
			NicePrint(count+1);
			pw.println("</Hide>");
			pw.flush();
		}
		NicePrint(count);
		pw.println("</HideExpr>");
		pw.flush();
	}
/**
 * This method is to transform an  expression that contains schematext and one
 * other expression. Since the predicate contains universal quantification,
 * existential quantification and unique existential quantification, expression
 * will not cover these three types. What a SchemaExpression object covers is
 * the function construction, definite description and substitution expression.
 *
 * @param exp It is a SchemaExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSchemaExpr(Expression exp, int count){
		SchemaExpression se = (SchemaExpression)exp;
		String oper = (String)se.op;
		String title = "";
		String end = "";
		if(oper.equals("\\lambda")){
			title = "<LambdaExpr>";
			end = "</LambdaExpr>";
		}
		else if(oper.equals("\\mu")){
			title = "<MuExpr>";
			end = "</MuExpr>";
		}
		else if(oper.equals("\\let")){
			title = "<LetExpr>";
			end = "</LetExpr>";
		}
		else if(oper.equals("\\forall")){
			title = "<ForallExpr>";
			end = "</ForallExpr>";
		}
		else if(oper.equals("\\exists")){
			title = "<ExistsExpr>";
			end = "</ExistsExpr>";
		}
		else if(oper.equals("\\existsone")){
			title = "<Exists1Expr>";
			end = "</Exists1Expr>";
		}
		else{
			System.out.println("unmatched operator for schemaexpression!");
			return;
		}
		NicePrint(count);
		pw.println(title);
		anaSchemaText(se.st, count+1);
		if(se.e != null)
			anaExpression(se.e, count+1);
		NicePrint(count);
		pw.println(end);
		pw.flush();
	}
/**
 * This method is to transform a set comprehension.
 *
 * @param exp It is a SetCompExpression object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaSetCompExpr(Expression exp, int count){
		SetCompExpression sce = (SetCompExpression)exp;
		NicePrint(count);
		pw.println("<SetCompExpr>");
		anaSchemaText(sce.st, count+1);
		if(sce.e != null)
			anaExpression(sce.e, count+1);
		NicePrint(count);
		pw.println("</SetCompExpr>");
		pw.flush();
	}
/**
 * This method is to classify the type of parsing expression and determine which
 * method to apply to transform the expression based on its type.
 *
 * @param exp It is a abstract expression type.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaExpression(Expression exp, int count){
		if(exp instanceof ReferExpression) anaRefExpr(exp, count);
		else if(exp instanceof TupleExpression) anaTupleExpr(exp, count);
		else if(exp instanceof SingleExpression) anaSingleExpr(exp, count);
		else if(exp instanceof ApplExpression) anaAppExpr(exp, count);
		else if(exp instanceof NumberExpression) anaNumExpr(exp, count);
		else if(exp instanceof SetExpression) anaSetExpr(exp, count);
		else if(exp instanceof CardExpression) anaCardExpr(exp, count);
		else if(exp instanceof BindExtendExpression) anaBindExpr(exp, count);
		else if(exp instanceof TupleSelExpression) anaTupleSelExpr(exp, count);
		else if(exp instanceof BindSelExpression) anaBindSelExpr(exp, count);
		else if(exp instanceof CondExpression) anaCondExpr(exp, count);
		else if(exp instanceof DecorExpression) anaDecorExpr(exp, count);
		else if(exp instanceof SchExpression) anaSchExpr(exp, count);
		else if(exp instanceof ReNameExpression) anaReNameExpr(exp, count);
		else if(exp instanceof TwoExpression) anaTwoExpr(exp, count);
		else if(exp instanceof SchemaHideExpression) anaSchemaHideExpr(exp, count);
		else if(exp instanceof SchemaExpression) anaSchemaExpr(exp, count);
		else if(exp instanceof SetCompExpression) anaSetCompExpr(exp, count);
		else if(exp instanceof InfixRel) anaInfixRel((InfixRel)exp, count);
		else if(exp instanceof PrefixRel) anaPrefixRel((PrefixRel)exp, count);
		else{ System.out.println("the expression undefined type yet");
			  System.out.println("try to print out the error expr: " + exp);
		}
	}
/**
 * This method is to transform a list consists of names of variable.
 *
 * @param nl It is a vector containing names.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaNameList(Vector nl, int count){
		for(int i = 0; i < nl.size(); i++){
			NicePrint(count);
			pw.println("<DeclName>");
			pw.flush();
			VarName vn = (VarName)nl.elementAt(i);
			anaVarName(vn, count+1);
			NicePrint(count);
			pw.println("</DeclName>");
			pw.flush();
		}
	}
/**
 * This method is to transform a single and basic name.
 *
 * @param vn It is a VarName object.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public   void anaVarName(VarName vn, int count){
		String vncontent = (String)vn.n;
		String greek = (String)vn.g;
		boolean flag = true;
		NicePrint(count);
		pw.print("<Word>");
		if(greek != null){
			String temp = (String)optable.GetOp(greek);
			pw.print(temp + " ");
		}
		if(optable.InTable(vncontent)){
			vncontent = (String)optable.GetOp(vncontent);
			pw.print(vncontent);
		}
		else if(vncontent.startsWith("\\")){
			vncontent = vncontent.substring(1);
			pw.print(vncontent);
		}
	else{
		int vnlen = vncontent.length();
		if(vnlen >= 2){
			String lastchar = vncontent.substring(vnlen-1);
			String lastsecchar = vncontent.substring(vnlen-2, vnlen-1);
			if(lastchar.equals("'") ||lastchar.equals("?")||lastchar.equals("!")){
				flag =false;
				pw.println(vncontent.substring(0,vnlen-1)+ "</Word>");
				anaStroke(lastchar, count);
			}
			else if(lastsecchar.equals("_")){
				int num1 = lastchar.compareTo("0");
				int num2 = lastchar.compareTo("9");
				if((num1 >= 0) && (num2 <= 0)){
					flag = false;
					pw.println(vncontent.substring(0,vnlen-2)+ "</Word>" );
					anaStroke(lastsecchar+lastchar, count);
				}
				else{
					pw.print(vncontent);
				}
			}
			else{
				pw.print(vncontent);
			}
		}
		else{
			pw.print(vncontent);
		}
	}//end bigger else
	if(flag){
	    pw.println("</Word>");
	 }
		pw.flush();
	}
/**
 * This method is to transform those special strokes.
 *
 * @param s It is a stroke string.
 * @param count An integer to indicate how many blank space need to print.
 *
 */
	public void anaStroke(String s, int count){
		NicePrint(count);
		if(s.equals("'"))
			pw.println("<NextStroke/>");
		else if(s.equals("?"))
			pw.println("<InStroke/>");
		else if(s.equals("!"))
			pw.println("<OutStroke/>");
		else if(s.startsWith("_")){
			Integer num = new Integer(s.substring(1));
			pw.println("<NumStroke Number=\"" + num + "\"/>");
		}
		else{
			System.out.println("no matched stroke");
			return;
		}
		pw.flush();
	}
			
}
