/*
  Copyright (C) 2004, 2005 Petra Malik, Tim Miller
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

package net.sourceforge.czt.print.oz;

import java.io.PrintWriter;
import java.io.Writer;
import java.util.Map;

import net.sourceforge.czt.java_cup.runtime.Scanner;
import net.sourceforge.czt.java_cup.runtime.Symbol;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.DebugUtils;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.util.ZString;
import net.sourceforge.czt.oz.util.OzString;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z tokens in unicode
 * to the PrintWriter class.
 *
 * @author Petra Malik, Tim Miller
 */
public class UnicodePrinter
  extends net.sourceforge.czt.print.z.UnicodePrinter
{ 
  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public UnicodePrinter(Writer out)
  {
    super(out);
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public UnicodePrinter(Writer out, boolean autoFlush)
  {
    super(out, autoFlush);
  }

  /**
   * Prints the CLASS token.
   */
  public void printCLASS()
  {
    print(ZString.SCH + ZString.SPACE + "class" + ZString.SPACE);
  } 

  /**
   * Prints the GENCLASS token.
   */
  public void printGENCLASS()
  {
    print(ZString.SCH + ZString.SPACE + "genclass" + ZString.SPACE);
  }

  /**
   * Prints the STATE token.
   */
  public void printSTATE()
  {
    print(ZString.SCH + ZString.ZEDCHAR);
  }

  /**
   * Prints the INIT token.
   */
  public void printINIT()
  {
    print(ZString.SCH + ZString.SPACE + OzString.INITWORD + ZString.SPACE);
  }

  /**
   * Prints the OPSCH token.
   */
  public void printOPSCH()
  {
    print(ZString.SCH +  "op" + ZString.SPACE);
  }

  /**
   * Prints a token from Symbol.
   */
  public void printSymbol(Symbol s)
  {
    if (s.left == OzPrintVisitor.OZ) {
      switch(s.sym) {
      case(Sym.CLASS):
	printCLASS();
	break;
      case(Sym.GENCLASS):
	printGENCLASS();
	break;
      case(Sym.STATE):
	printSTATE();
	break;
      case(Sym.INIT):
	printINIT();
	break;
      case(Sym.OPSCH):
	printOPSCH();
	break;
      default :
	Map fieldMap = DebugUtils.getFieldMap(Sym.class);
	throw new CztException("Unexpected token (" + s.sym + ", " +
			       fieldMap.get(s.sym) + ", " +
			       s.value + ")");
      }
    }
    else {
      super.printSymbol(s);
    }
  }
}
