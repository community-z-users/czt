package net.sourceforge.czt.scanner;

import java.io.*;
import java_cup.runtime.*;
   
class ScannerTest {
  static public void main(String argv[]) {    
    try {
      InputStream stream = new FileInputStream(argv[0]);
      InputStreamReader reader = new InputStreamReader(stream, "UTF-8");
      // reader = new FileReader(argv[0])
      Lexer scanner = new Lexer(reader);
      Symbol s = null;
      while ( (s=scanner.next_token()).sym != sym.EOF) {
	System.out.println("TOKEN " + s.sym +
			   " line:" + s.left +
			   " column:" + s.right +
			   " value:" + s.value);
      }
    } catch (Exception e) {
      /* do cleanup here -- possibly rethrow e */
      e.printStackTrace();
    }
  }
}
