package net.sourceforge.czt.scanner;

import java.io.*;

public class UnicodeToLatex
{
  static public void main(String argv[]) {    
    try {
      InputStream stream = new FileInputStream(argv[0]);
      InputStreamReader reader = new InputStreamReader(stream, "UTF-8");
      Unicode2Latex parser = new Unicode2Latex(new UnicodeLexer(reader));
      Object result = parser.parse().value;      
    } catch (Exception e) {
      e.printStackTrace();
    }
  }
}
