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
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.util.XmlWriter;

/**
 * LTZCompiler performs the transformation from Latex to ZML.
 *
 * It reads the source program in Latex format from user's input
 * file, then it applies the LTZscanner to scan the input source and
 * split them into meaningful tokens.  After scanning, it applies
 * LTZparser to construct the syntax tree of the source program.
 * Then it writes this out in ZML format.
 */
public class LTZCompiler{
	public   PrintWriter pw;
	public   String fullfilename;
	public   String filename;
	public   boolean debug = true;
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
    // record input names for later use (in error messages etc.).
    fullfilename = fullname;
    filename = specname;
    FileInputStream input = new FileInputStream(fullname);
    BufferedReader bufinput
      = new BufferedReader(new InputStreamReader(input,"UTF-8"));
    try{
      Spec spec = parse(bufinput,fullname);

      // Now output the XML file.
      XmlWriter writer = new JaxbXmlWriter();
      FileOutputStream outfile = new FileOutputStream(outname);
      Writer out = new BufferedWriter(new OutputStreamWriter(outfile,"UTF-8"));
      writer.write(spec, out);
      out.close();
    }
    catch(Exception e) {
      e.printStackTrace();
      //System.err.println(e);
    }
    System.out.println("Transformation is done" );
  }
  

  /**
   * This method will parse the input string into a syntax tree which top is
   * a speicification. Start the translation from the root of the tree.
   *
   * @param input it is a string consists of original source program.
   *
   */
  public Spec parse(Reader input, String inputName)
    throws Exception {
    LTZparser p = new LTZparser(new SmartScanner(new LTZscanner(input)));
    p.setSourceName(inputName);
    Spec spec;
    if (debug)
      spec = (Spec)p.parse().value;
    else
      spec = (Spec)p.debug_parse().value;
    
    return spec;
  }
}
