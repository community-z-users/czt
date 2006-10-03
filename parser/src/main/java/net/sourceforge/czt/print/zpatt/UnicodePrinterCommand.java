/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.print.zpatt;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Properties;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.ast.*;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.print.z.PrecedenceParenAnnVisitor;
import net.sourceforge.czt.print.z.UnicodePrinter;
import net.sourceforge.czt.session.*;

public class UnicodePrinterCommand
  implements Command
{
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      final Writer writer = new StringWriter();
      final Key key = new Key(name, Term.class);
      final Term term = (Term) manager.get(key);
      AstToPrintTreeVisitor toPrintTree = new AstToPrintTreeVisitor(manager);
      Term tree = (Term) term.accept(toPrintTree);
      PrecedenceParenAnnVisitor precVisitor =
        new PrecedenceParenAnnVisitor();
      tree.accept(precVisitor);
      UnicodePrinter printer = new UnicodePrinter(writer);
      Properties props = manager.getProperties();
      ZpattPrintVisitor visitor = new ZpattPrintVisitor(printer, props);
      tree.accept(visitor);
      writer.close();
      manager.put(new Key(name, UnicodeString.class),
                  new UnicodeString(writer.toString()));
      return true;
    }
    catch (IOException e) {
      throw new CommandException(e);
    }
  }
}
