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

import net.sourceforge.czt.animation.gui.generation.*;
import net.sourceforge.czt.animation.gui.generation.plugins.*;


/** Translate a Z specification from ZML format into BZP format.
 *
 *  It takes a file spec.xml and produces a file spec.bzp.
 *  Note that the BZP format is the input notation for the
 *  BZ-TT (BZ Testing Tools) environment, which can animate
 *  specifications and generate tests.
 */
public class Main {

  private static PluginList plugins
    = new PluginList(
        new Class[] {
	  SpecSource.class,
	  SchemaExtractor.class,
	  SchemaIdentifier.class,
	  VariableExtractor.class},
	new Class[] {
	  SpecReaderSource.class,
	  VisitorSchemaExtractor.class,
	  CommandLineSchemaIdentifier.class,
	  DefaultVariableExtractor.class},
	"Z2BZP",
	"Translates a Z specification (*.xml) into BZP format (.bzp).");
  
  public static void main(String[] args) {
    try {
      // set up our debug log.
      Handler handler = new FileHandler("z2bzp.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.z2bzp").setLevel(Level.FINEST);

      // process all command line arguments
      // Note: this may change the plugins from the defaults above.
      plugins.processOptions(args);

      // Now make shortcuts to the plugins that we need.
      SpecSource source
	= (SpecSource)plugins.getPlugin(SpecSource.class);

      // Now read the spec 
      Term spec = source.obtainSpec();
      URL specURL = source.getURL();


      // now create the output file
      Logger.getLogger("net.sourceforge.czt.z2bzp").fine("input file is "+url);
      BzpWriter bzp = createBzpWriter(specURL);

      // now do the translation
      BzpTranslator tr = new BzpTranslator(spec, specURL, plugins, bzp);

      // close and flush the output file
      bzp.close();
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
 

  /** Create the output BZP file.
   *  TODO: make this a plugin!
   *
   *  It takes a file spec.xml and creates a file spec.bzp.
   *  Note that the BZP format is the input notation for the
   *  BZ-TT (BZ Testing Tools) environment, which can animate
   *  specifications and generate tests.
   *
   * @param inName The path to the ZML file.  Must end with ".xml" or ".zml".
   */
  public BzpWriter createBzpWriter(String inName) {
    // create output file (*.bzp)
    String outName = inName + ".bzp";
    //inName.substring(0, inName.length()-4) + ".bzp";
    
    PrintWriter out
      = new PrintWriter(new BufferedWriter(new FileWriter(outName)));
    return new BzpWriter(out);
  }
}
