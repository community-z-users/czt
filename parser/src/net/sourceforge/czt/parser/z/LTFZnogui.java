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

import net.sourceforge.czt.parser.z.*;
import java.io.*;
import java.util.*;

class LTFZnogui{
    public static void main(String args[])throws Exception{
	if (args.length == 0) {
	    // process upload/upload.tex
	    LTZCompiler ltz = new LTZCompiler("upload/upload.tex",
					      "upload",
					      "upload/upload.xml");
	}
	else {
	    String inputfile = args[0];
	    // TODO: this needs to be improved to handle UNIX and Windows
	    //       directory syntax.  There must be a library to do this?
	    StringTokenizer st = new StringTokenizer(inputfile, "/\\");
	    String filename = "";
	    while(st.hasMoreTokens()){
		filename =  st.nextToken();
	    }
	    if(filename.endsWith(".tex") || filename.endsWith(".zed")){
		int dotpos = inputfile.length() - 4;
		String xmlfile = inputfile.substring(0, dotpos) + ".xml";
		//System.out.println("New XML file will be: " + xmlfile);
		LTZCompiler ltz = new LTZCompiler(inputfile, filename, xmlfile);
	    }
	    else{
		System.out.println("Arguments: spec.zed or spec.tex");
	    }
	}
    }
}
