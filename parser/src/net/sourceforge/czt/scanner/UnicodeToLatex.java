package net.sourceforge.czt.scanner;

import java.io.*;

public class UnicodeToLatex
{
  static public void main(String[] args) {    
    String usage = "Usage: java net.sourceforge.czt.scanner.UnicodeToLatex"
      + " [ -in <inputfile>] [ -out <outputfile>]";
    try {
      InputStreamReader input = new InputStreamReader(System.in);
      Writer writer = new PrintWriter(System.out);
      for (int i = 0; i < args.length; i++) {
        if ("-in".equals(args[i])) {
          if (i < args.length) {
            input =
              new InputStreamReader(new FileInputStream(args[++i]), "utf8");
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
      Unicode2Latex parser = new Unicode2Latex(new UnicodeLexer(input));
      parser.setWriter(writer);
      Object result = parser.parse().value;      
      writer.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
}
