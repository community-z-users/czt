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

package net.sourceforge.czt.scanner;

import java.io.*;

/**
 * @author Petra Malik
 */
public final class UnicodeToLatex
{
  /**
   * Do not create instances of this class.
   */
  private UnicodeToLatex()
  {
  }

  public static void main(String[] args)
  {
    String usage = "Usage: java net.sourceforge.czt.scanner.UnicodeToLatex"
      + " [ -in <inputfile>] [ -out <outputfile>] [-enc <encoding>]";
    try {
      InputStream instream = System.in;
      Writer writer = new OutputStreamWriter(System.out);
      String encoding = "utf8";
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (i < args.length) {
            instream = new FileInputStream(args[++i]);
          }
          else {
            System.err.println(usage);
            return;
          }
        }
        else if ("-out".equals(args[i])) {
          if (i < args.length) {
            writer =
              new OutputStreamWriter(new FileOutputStream(args[++i]));
          }
        }
        else if ("-enc".equals(args[i])) {
          if (i < args.length) {
            encoding = args[++i];
          }
          else {
            System.err.println(usage);
            return;
          }
        }
        else {
          System.err.println(usage);
          return;
        }
      }
      InputStreamReader reader = new InputStreamReader(instream, encoding);
      Unicode2Latex parser =
        new Unicode2Latex(new NewlineScanner(new UnicodeLexer(reader)));
      parser.setWriter(writer);
      Object result = parser.parse().value;
      writer.close();
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }
}
