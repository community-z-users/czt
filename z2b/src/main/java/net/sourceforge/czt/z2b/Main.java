/**
Copyright 2003, 2006 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z2b;

import java.io.*;
import java.util.logging.*;
import java.util.*;
import java.net.URL;
import java.net.URLDecoder;

import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.Sect;
import net.sourceforge.czt.z.ast.SectTypeEnvAnn;
import net.sourceforge.czt.z.ast.Spec;
import net.sourceforge.czt.z.ast.ZSect;

/** Translate a Z specification from ZML format into B format.
 *
 *  It takes a file spec.xml and produces a file spec.mch.
 */
public class Main
{
  public static void main(String[] args)
  {
    try {
      // set up our debug log.
      Handler handler = new FileHandler("z2b.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger z2bLogger = Logger.getLogger("net.sourceforge.czt.z2b");
      z2bLogger.setLevel(Level.FINEST);

      // Now read the spec 
      if (args.length < 1) {
        System.err.println("Args: spec.tex");
        System.exit(1);
      }
      System.err.println("Reading spec");
      final String input = args[0];
      File file = new File(input);
      FileSource source = new FileSource(input);
      SectionManager manager = new SectionManager(Dialect.Z);
      manager.setProperty("czt.path", file.getParent());
      String name = "spec";
      manager.put(new Key<Source>(name, Source.class), source);
      Spec spec = manager.get(new Key<Spec>(name, Spec.class));

       // now create the output file
      System.err.println("Creating output file");
      z2bLogger.fine("input file is " + input);

      // set up the translation engine
      System.err.println("Translating to B");
      Z2B translator = new Z2B(manager);

     // choose the section -- we just take the last one!
      ZSect sect;
      List<Sect> sects = spec.getSect();
      if (sects.size() > 0 && sects.get(sects.size()-1) instanceof ZSect) {
        sect = (ZSect) spec.getSect().get(sects.size()-1);
      }
      else {
        throw new BException("last section is not a ZSect");
      }
      manager.get(new Key<SectTypeEnvAnn>(sect.getName(), SectTypeEnvAnn.class)); // typecheck

      // do the translation
      BMachine mach = translator.makeBMachine(sect);

      // Output the machine to the .mch file
      System.err.println("Writing out the B");
      BWriter bwriter = createBWriter(file.toURI().toURL());
      mach.print(bwriter);
      bwriter.close();

      System.err.println("Done!");
    }
    catch(Exception e) {
      System.err.println("ERROR: "+e);
      System.err.println("");
      System.err.println("For debugging purposes, here is a stack trace:");
      e.printStackTrace();
    }
  }
 

  /** Create the output B file.
   *  TODO: make this a plugin!
   *
   *  It takes a file spec.xml and creates a file spec.mch.
   *
   * @param inName The path to the ZML file.  Must end with ".xml", ".zml",
   *               ".tex", or ".zed".
   */
  public static BWriter createBWriter(URL inName)
    throws IOException
  {
    // create output file (*.mch)
    String outName = URLDecoder.decode(inName.getPath(), "UTF-8");
    if ( ! inName.getProtocol().equals("file")) {
      // put the output in the current directory
      int slash = outName.lastIndexOf('/');
      if (slash >= 0 && slash < outName.length())
        outName = outName.substring(slash+1); 
    }
    // Now strip off any known suffix
    if (outName.endsWith(".xml")
        || outName.endsWith(".zml")
        || outName.endsWith(".tex")
        || outName.endsWith(".zed")) {
      outName = outName.substring(0, outName.length()-4);
    }

    if (outName.length() == 0) {
      outName = "spec";
    }
    outName += ".mch";
    
    Writer out = new BufferedWriter(new FileWriter(outName));
    return new BWriter(out, inName.toString());
  }
}
