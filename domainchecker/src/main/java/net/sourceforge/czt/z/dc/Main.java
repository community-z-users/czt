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

import java.io.File;
import java.io.FileWriter;
import java.util.logging.FileHandler;
import java.util.logging.Handler;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionInfo;
import java.util.logging.Level;
import java.util.logging.Logger;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.session.SectionManager;

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
      Logger dcLogger = Logger.getLogger(DomainChecker.class.getName());
      dcLogger.addHandler(handler);      
      dcLogger.setLevel(Level.FINEST);

      // Now read the spec 
      if (args.length < 1) {
        System.err.println("Args: spec.tex");
        System.exit(1);
      }
      System.out.println("Reading spec in " + args[0]);
      dcLogger.fine("input file is " + args[0]);
      FileSource source = new FileSource(args[0]);      
      SectionInfo manager = new SectionManager();            
      
      System.out.println("Parsing and typechecking..." + args[0]);      
      
      int dotIdx = args[0].lastIndexOf(".") ;
      if (dotIdx == -1) { dotIdx = args[0].length(); }
      String filename = args[0].substring(0, dotIdx);      
      ZSectDCEnvAnn zsDCEnvAnn = manager.get(new Key<ZSectDCEnvAnn>(filename, ZSectDCEnvAnn.class));      
      String outputFileName = "./" + zsDCEnvAnn.getZSect().getName() + ".tex";
            
      System.out.println("Calculating domain checks.." + args[0]);
      LatexString outputData = manager.get(new Key<LatexString>(filename, LatexString.class));
            
      System.out.println("Creating output file......." + outputFileName);
      File outputFile = new File(outputFileName);      
      if (outputFile.exists())
      {
        System.out.println("Output file already exists, deleting it first.");
        outputFile.delete();
      }      
      FileWriter output = new FileWriter(outputFile);      
      output.write(outputData.toString());
      output.close();
      
      System.out.println("Done! See results in " + outputFileName);
    }
    catch(Exception e) {
      System.err.println("ERROR: "+e);
      System.err.println("");
      System.err.println("For debugging purposes, here is a stack trace:");
      e.printStackTrace();
    }
  }

  private Main()
  {
  }
}
