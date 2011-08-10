/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */

package net.sourceforge.czt.print.zeves;

import java.io.IOException;
import java.io.StringWriter;
import java.io.Writer;
import java.util.Properties;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.OldLatexString;
import net.sourceforge.czt.print.util.PrintException;
import net.sourceforge.czt.print.util.PrintPropertiesKeys;
import net.sourceforge.czt.print.z.ToSpiveyZVisitor;
import net.sourceforge.czt.print.z.Unicode2OldLatex;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.util.Section;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class OldLatexPrinterCommand 
  extends net.sourceforge.czt.print.z.OldLatexPrinterCommand
  implements Command
{
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      final Writer writer = new StringWriter();
      final Key key = new Key(name, Term.class);
      final Term term = (Term) manager.get(key);
      printOldLatex(term, writer, manager);
      writer.close();
      manager.put(new Key(name, OldLatexString.class),
                  new OldLatexString(writer.toString()));
      return true;
    }
    catch (IOException e) {
      throw new CommandException(e);
    }
  }

  public void printOldLatex(Term term,
                            Writer out,
                            SectionManager sectInfo)
  {
    String sectionName = Section.STANDARD_TOOLKIT.getName();
    printOldLatex(term, out, sectInfo, sectionName);
  }

  public void printOldLatex(Term term,
                            Writer out,
                            SectionManager sectInfo,
                            String sectionName)
  {
    term.accept(new ToSpiveyZVisitor());
    AstToPrintTreeVisitor toPrintTree =
      new AstToPrintTreeVisitor(sectInfo);
    toPrintTree.setOldZ(true);
    Term tree = toPrintTree(toPrintTree, term, sectionName);
    Properties props = new Properties(sectInfo.getProperties());
    props.setProperty(PrintPropertiesKeys.PROP_PRINT_ZEVES, "true");
    ZmlScanner scanner = new ZmlScanner(tree, PrintUtils.warningManager_, props);
    Unicode2OldLatex parser = new Unicode2OldLatex(prepare(scanner, term));
    parser.setSectionInfo(sectInfo, sectionName);
    UnicodePrinter printer = new UnicodePrinter(out);
    parser.setWriter(printer);
    try {
      parser.parse();
    }
    catch (Exception e) {
      throw new PrintException(ZEvesPrintMessage.MSG_PRINT_OLDLATEX_EXCEPTION.format(sectionName), e);
    }
  }
}
