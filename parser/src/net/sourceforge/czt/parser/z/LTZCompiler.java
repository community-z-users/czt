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
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.XmlReader;
import net.sourceforge.czt.base.util.XmlWriter;

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
		    Spec spec = compile(source,debug);
		    // Now output the XML file.
		    XmlWriter writer = new JaxbXmlWriter();
		    // Note that the encoding is set to utf8 explicitly.
		    //OutputStreamWriter outputStream
		//	= new OutputStreamWriter(new 
		//	    FileOutputStream("test.xml"), "utf8");
		    writer.write(spec, outfile);
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
 * This method will parse the input string into a syntax tree which top is
 * a speicification. Start the translation from the root of the tree.
 *
 * @param input it is a string consists of original source program.
 *
 */
	public Spec compile(String input, boolean debug)throws Exception{
		LTZparser p = new LTZparser(
			       new SmartScanner(
				new LTZscanner(
			         new StringReader(input))));
		opmaps = p.getOpMap();
		p.setSourceName(input);
		Spec spec;
		if (debug)
		    spec = (Spec)p.parse().value;
		else
		    spec = (Spec)p.debug_parse().value;

		return spec;
	}
}
