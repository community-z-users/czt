package net.sourceforge.czt.z2bzp;
/**
Copyright 2003 Mark Utting
This file is part of the czt project.

The czt project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The czt project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with czt; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.dom.DomXmlWriter;

/** Translate a Z specification from ZML format into BZP format.
 *
 *  It takes a file spec.xml and produces a file spec.bzp.
 *  Note that the BZP format is the input notation for the
 *  BZ-TT (BZ Testing Tools) environment, which can animate
 *  specifications and generate tests.
 */
public class Main {
  public static void main( String[] args ) {
    //TODO use specSource, schemaExtractor, schemaIdentifier, varExtractor
/*
    List argsList=Arrays.asList(args);
    ListIterator iterator=argsList.listIterator();
    try {
      while(iterator.hasNext()) {
	int nextIndex=iterator.nextIndex();
	pluginSetter.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(specificationSource==null) specificationSource=new SpecReaderSource();
	specificationSource.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(schemaExtractor==null) schemaExtractor=new VisitorSchemaExtractor();
	schemaExtractor.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle

	if(schemaIdentifier==null) schemaIdentifier=new CommandLineSchemaIdentifier();
	schemaIdentifier.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycel

	if(variableExtractor==null) variableExtractor=new DefaultVariableExtractor();
	variableExtractor.handleArgs(iterator);
	if(nextIndex!=iterator.nextIndex()) continue;//If it has consumed some of the arguments restart cycle
      } 
    } catch(Exception ex) {
      System.err.println(ex);
      return;
    }
*/
    if (args.length > 0) {
      if (args[0].length() < 5 || ! args[0].endsWith(".xml")) {
	System.err.println("Arguments:  spec.xml");
	System.exit(1);
      }
      translateToBzp(args[0]);
    }
    else {
      translateToBzp("tests/eg1.xml");
    }
  }

  /** Translate a Z specification from ZML format into BZP format.
   *
   *  It takes a file spec.xml and produces a file spec.bzp.
   *  Note that the BZP format is the input notation for the
   *  BZ-TT (BZ Testing Tools) environment, which can animate
   *  specifications and generate tests.
   *
   *  Debug messages are logged into the file z2bzp.log.
   *
   * @param inName The path to the ZML file.  Must end with ".xml".
   */
  public static void translateToBzp(String inName) {
    try {
      Handler handler = new FileHandler("z2bzp.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.z2bzp").setLevel(Level.FINEST);

      // read the input file (which must be in ZML format).
      XmlReader reader = new JaxbXmlReader();
      Term spec = (Term) reader.read(new java.io.File(inName));

      // create output file (*.bzp)
      String outName = inName.substring(0, inName.length()-4) + ".bzp";
      Logger.getLogger("net.sourceforge.czt.z2bzp").fine("output file is " + outName);

      PrintWriter out = new PrintWriter(
			 new BufferedWriter(
			  new FileWriter(outName)));
      // visiting using SubstVisitor
      BzpTranslator visitor = new BzpTranslator(new BzpWriter(out));
      Term result = (Term) spec.accept(visitor);
      out.close();
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
