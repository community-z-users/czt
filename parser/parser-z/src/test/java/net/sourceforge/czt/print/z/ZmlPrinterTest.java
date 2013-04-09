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

import java.net.URL;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
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
  /**
   *
   * @param url
   * @param manager0
   * @return
   * @throws Exception
   */
  @Override
  public Term parse(URL url, SectionManager manager0)
    throws Exception
  {
    Source source = new UrlSource(url);
    String name = SourceLocator.getSourceName(source.getName());
      
    SectionManager manager = manager0.clone();

    // parse
    manager.put(new Key<Source>(name, Source.class), source);
    @SuppressWarnings("unused")
	Spec spec = manager.get(new Key<Spec>(name, Spec.class));
    // We do not delete annotations, since conjecture names are
    // stored as annotations and we want to preserve those.

    // print as latex
    String contents = (manager.get(new Key<LatexString>(name, LatexString.class))).toString();
    source = new StringSource(contents);
    source.setMarkup(Markup.LATEX);

    // now reparse the LaTeX
    name = SourceLocator.getSourceName(source.getName());
    manager = manager0.clone();

    manager.put(new Key<Source>(name, Source.class), source);
    spec = manager.get(new Key<Spec>(name, Spec.class));

    // print as Unicode, reparse, and return
    source = new StringSource((manager.get(new Key<UnicodeString>(name, UnicodeString.class))).toString());
    source.setMarkup(Markup.UNICODE);
    name = SourceLocator.getSourceName(source.getName());
    manager = manager0.clone();

    manager.put(new Key<Source>(name, Source.class), source);
    return manager.get(new Key<Spec>(name, Spec.class));
  }

@Override
protected Dialect getDialect() {
	return Dialect.Z;
}
  
  
}
