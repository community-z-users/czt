/*
  Copyright (C) 2003, 2004 Mark Utting
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

import java.io.*;
import java.util.logging.*;

import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.base.visitor.VisitorUtils;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.z.jaxb.JaxbXmlWriter;
import net.sourceforge.czt.base.ast.Term;

public class Main {
  public static void main(String[] args) {
    // Use a default file name ...
    String fileName = "../../../zml/examples/z/birthdaybook.xml";
    // ... or the file provided as an argument.
    if (args.length > 0) fileName = args[0];

    try {
      Handler handler = new FileHandler("visitor.log");
      handler.setLevel(Level.ALL);
      handler.setEncoding("utf8");
      Logger.getLogger("").addHandler(handler);
      Logger.getLogger("net.sourceforge.czt.base").setLevel(Level.FINEST);

      // Unmarshal file eg1.xml ...
      XmlReader reader = new JaxbXmlReader();
      Term spec =
	(Term) reader.read(new java.io.File(fileName));

      // Create a new visitor
      SubstVisitor visitor = new SubstVisitor();

      // This is a debugging check which can be omitted.
      // It checks whether each visitXXX method has a corresponding
      // implements XXXVisitor declaration in the visitor.
      // This checks for the most common error of a visitor
      // (it has a visitXXX method but it is never called since
      //  the corresponding interface is not implemented;
      //  Note: a term checks whether a certain interface is implemented,
      //  and if it is calls the corresponding visit-method)
      VisitorUtils.checkVisitorRules(visitor);

      // use the visitor to transform an AST into another AST
      Term result = (Term) spec.accept(visitor);

      // ... and marshal the result to stdout.
      XmlWriter writer = new JaxbXmlWriter();
      writer.write(result, System.out);
    } catch( Exception e ) {
      e.printStackTrace();
    }
  }
}
