/*
  Copyright (C) 2004, 2006 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.io.*;
import java.net.URL;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.parser.util.DeleteAnnVisitor;
import net.sourceforge.czt.parser.util.ParseException;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.print.util.UnicodeString;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.Spec;

/**
 * A (JUnit) test class for testing the zml to latex and unicode
 * converter.
 *
 * @author Petra Malik
 */
public class ZmlPrinterTest
  extends AbstractParserTest
{
  /** TODO: remove this once conjecture names are preserved by Unicode2Latex */
  @Override
  public void testConjectureNames() throws Exception
  {
  }

  public Term parse(URL url, SectionManager manager)
    throws Exception
  {
    Source source = new UrlSource(url);
    String name = source.getName();

    // parse
    manager.put(new Key(name, Source.class), source);
    Spec spec = (Spec) manager.get(new Key(name, Spec.class));
    // MarkU: turn this off, so that conjecture names are preserved.
    //DeleteAnnVisitor visitor = new DeleteAnnVisitor();
    //spec.accept(visitor);

    // print as latex
    String contents = ((LatexString)
        manager.get(new Key(name, LatexString.class))).toString();
    source = new StringSource(contents);
    // MarkU: DEBUG
    if (name.contains("conjecture")) {
      System.out.println("reparsed "+name+"="+contents);
    }
    source.setMarkup(Markup.LATEX);

    // now reparse the LaTeX
    name = source.getName();
    manager = new SectionManager();
    manager.put(new Key(name, Source.class), source);
    spec = (Spec) manager.get(new Key(name, Spec.class));
    // MarkU: turn this off, so that conjecture names are preserved.
    //spec.accept(visitor);

    // print as Unicode, reparse, and return
    source = new StringSource(((UnicodeString)
      manager.get(new Key(name, UnicodeString.class))).toString());
    source.setMarkup(Markup.UNICODE);
    name = source.getName();
    manager = new SectionManager();
    manager.put(new Key(name, Source.class), source);
    return (Spec) manager.get(new Key(name, Spec.class));
  }
}
