/*
  Copyright (C) 2003, 2004 Petra Malik
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

package net.sourceforge.czt.print.circus;

import java.io.*;
import net.sourceforge.czt.parser.circus.*;

/**
 * Unicode to Latex transformation utilities for Standard Z.
 * This class provides a unicode to latex command line tool and
 * a static method for transforming unicode (provided via
 * a Reader) to LaTex.  The resulting LaTex is written to a Writer.
 *
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
    String infile = null;
    String encoding = null;
    String outfile = null;
    for (int i = 0; i < args.length; i++) {
      if ("-in".equals(args[i])) {
        if (i < args.length) {
          infile = args[++i];
        }
        else {
          System.err.println(usage);
          return;
        }
      }
      else if ("-out".equals(args[i])) {
        if (i < args.length) {
          outfile = args[++i];
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
    try {
      run(infile, encoding, outfile);
    }
    catch (Exception e) {
      e.printStackTrace();
    }
  }

  /**
   * Reads the given input file using the specified encoding and writes
   * to the given output file.
   *
   * @param infile the name of the input file.
   * @param encoding the encoding used to read the input file.
   * @param outfile the name of the output file.
   */
  public static void run(String infile, String encoding, String outfile)
    throws Exception
  {
    InputStream instream = System.in;
    String enc = "UTF-8";
    Writer writer = new OutputStreamWriter(System.out);
    if (infile != null) {
      instream = new FileInputStream(infile);
    }
    if (encoding != null) {
      enc = encoding;
    }
    if (outfile != null) {
      writer = new OutputStreamWriter(new FileOutputStream(outfile));
    }
    run(new InputStreamReader(instream, enc), writer);
    writer.flush();
    if (outfile != null) {
      writer.close();
    }
  }

  /**
   * Transforms the input provided via a Reader and writes
   * the result to the given Writer.
   *
   * @param in the reader containing the unicode specification.
   * @param out the writer where the LaTex specification goes.
   */
  public static void run(Reader in, Writer out)
    throws Exception
  {
    Unicode2Latex parser =
      new Unicode2Latex(new SectHeadScanner(new NewlineScanner(new ContextFreeScanner(in))));
    parser.setWriter(out);
    Object result = parser.parse().value;
  }
}
