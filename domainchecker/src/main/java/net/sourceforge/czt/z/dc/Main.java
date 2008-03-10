/**
Copyright 2007, Leo Freitas
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
package net.sourceforge.czt.z.dc;

import java.util.logging.FileHandler;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;

/** 
 *  Calculates the definedness criteria for ZSect terms, which
 *  is based on domain checks from the Z/Eves theorem prover.
 * 
 * @author Leo Freitas
 */
public class Main
{
  public static void main(String[] args)
  {
    try {
      // set up our debug log.
      Handler handler = new FileHandler("dc.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger dcLogger = Logger.getLogger("net.sourceforge.czt.z.dc");
      dcLogger.setLevel(Level.FINEST);

      // Now read the spec 
      if (args.length < 1) {
        System.err.println("Args: spec.tex");
        System.exit(1);
      }
      System.err.println("Reading spec");
      final String input = args[0];
      //URL specURL = new File(input).toURL();
      //FileSource source = new FileSource(input);
      //SectionManager manager = new SectionManager();
      //String name = "spec";
      //manager.put(new Key(name, Source.class), source);
      //Spec spec = (Spec) manager.get(new Key(name, Spec.class));

       // now create the output file
      System.err.println("Creating output file");
      dcLogger.fine("input file is " + input);

      System.err.println("Done!");
    }
    catch(Exception e) {
      System.err.println("ERROR: "+e);
      System.err.println("");
      System.err.println("For debugging purposes, here is a stack trace:");
      e.printStackTrace();
    }
  }
}
