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

package net.sourceforge.czt.parser.oz;

import java.io.*;

import java_cup.runtime.Scanner;
import java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.base.util.XmlWriter;
import net.sourceforge.czt.oz.jaxb.JaxbXmlWriter;

public final class ParseUtils
{
  /**
   * Do not generate instances of this class.
   */
  private ParseUtils()
  {
  }

  /**
   * Converts latex to zml.
   */
  public static void main(String[] args)
  {
    String usage = "Usage: java net.sourceforge.czt.parser.oz.ParseUtils"
      + " [ -in <inputfile>] [ -out <outputfile>]";
    try {
      Reader in = new InputStreamReader(System.in);
      Writer writer = new PrintWriter(System.out);
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (i < args.length) {
            in = new InputStreamReader(new FileInputStream(args[++i]));
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-out".equals(args[i])) {
          if (i < args.length) {
            writer =
              new OutputStreamWriter(new FileOutputStream(args[++i]));
          } else {
            System.err.println(usage);
            return;
          }
        } else {
          System.err.println(usage);
          return;
        }
      }
      Scanner scanner = new SmartScanner(new LatexScannerNew(in));
      OperatorTable table = new OperatorTable();
      LatexParser parser = new LatexParser(scanner, table, "");
      Symbol parseTree = parser.parse();
      Term term = (Term) parseTree.value;
      XmlWriter xmlWriter = new JaxbXmlWriter();
      xmlWriter.write(term, writer);
      writer.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  public static Term parseUtf8File(String filename)
    throws Exception
  {
    Reader in = new InputStreamReader(new FileInputStream(filename), "UTF-8");
    Scanner scanner = new SmartScanner(new UnicodeScanner(in));
    OperatorTable table = new OperatorTable();
    LatexParser parser = new LatexParser(scanner, table, filename);
    Symbol parseTree = parser.parse();
    return (Term) parseTree.value;
  }

  public static Term parseUtf16File(String filename)
    throws Exception
  {
    Reader in = new InputStreamReader(new FileInputStream(filename), "UTF-16");
    Scanner scanner = new SmartScanner(new UnicodeScanner(in));
    OperatorTable table = new OperatorTable();
    LatexParser parser = new LatexParser(scanner, table, filename);
    Symbol parseTree = parser.parse();
    return (Term) parseTree.value;
  }

  public static Term parseLatexFile(String filename)
    throws Exception
  {
    Reader in = new InputStreamReader(new FileInputStream(filename));
    Scanner scanner = new SmartScanner(new LatexScannerNew(in));
    OperatorTable table = new OperatorTable();
    LatexParser parser = new LatexParser(scanner, table, filename);
    Symbol parseTree = parser.parse();
    return (Term) parseTree.value;
  }
}
