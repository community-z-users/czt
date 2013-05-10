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

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.print.util.XmlString;
import net.sourceforge.czt.session.Command;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.zeves.jaxb.JaxbXmlWriter;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
public class XmlPrinterCommand
  implements Command
{
  @Override
  public boolean compute(String name, SectionManager manager)
    throws CommandException
  {
    try {
      JaxbXmlWriter xmlWriter = new JaxbXmlWriter();
      final Writer writer = new StringWriter();
      final Key<Term> key = new Key<Term>(name, Term.class);
      final Term term = manager.get(key);
      xmlWriter.write(term, writer);
      writer.close();
      final Key<XmlString> xmlKey = new Key<XmlString>(name, XmlString.class);
      final XmlString xmlStr = new XmlString(writer.toString(), Dialect.ZEVES);
      manager.endTransaction(xmlKey, xmlStr);
      return true;
    }
    catch (IOException e) {
      throw new CommandException(manager.getDialect(), e);
    }
  }
}
