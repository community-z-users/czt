package net.sourceforge.czt.scanner;

import java.io.*;

public class UnicodeToLatex
{
  static public void main(String[] args) {    
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
          } else {
            System.err.println(usage);
            return;
          }
        } else if ("-out".equals(args[i])) {
          if (i < args.length) {
            writer =
              new OutputStreamWriter(new FileOutputStream(args[++i]));
          }
        } else if ("-enc".equals(args[i])) {
          if (i < args.length) {
            encoding = args[++i];
          } else {
            System.err.println(usage);
            return;
          }
        } else {
          System.err.println(usage);
          return;
        }
      }
      InputStreamReader reader = new InputStreamReader(instream, encoding);
      Unicode2Latex parser = new Unicode2Latex(new UnicodeLexer(reader));
      parser.setWriter(writer);
      Object result = parser.parse().value;      
      writer.close();
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
}
