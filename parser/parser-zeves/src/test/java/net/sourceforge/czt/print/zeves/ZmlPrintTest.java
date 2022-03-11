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

import java.net.URL;

import org.junit.Ignore;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.session.SectionManager;

/**
 *
 * @author Leo Freitas
 * @date Aug 10, 2011
 */
@Ignore
public class ZmlPrintTest 
 // extends AbstractParserTest
{
  //  @Override
  public Term parse(URL url, SectionManager manager0)
    throws Exception
  {
    return  null;
//    if (url.getFile().contains())
//    System.out.println("ZML print test for " + url);
//    Source source = new UrlSource(url);
//    String name = source.getName();
//    SectionManager manager = manager0.clone();
//
//    // parse
//    manager.put(new Key<Source>(name, Source.class), source);
//    Spec spec = manager.get(new Key<Spec>(name, Spec.class));
//    // We do not delete annotations, since conjecture names are
//    // stored as annotations and we want to preserve those.
//
//    // print as latex
//    String contents = manager.get(new Key<LatexString>(name, LatexString.class)).toString();
//    source = new StringSource(contents);
//    source.setMarkup(Markup.LATEX);
//
//    // now reparse the LaTeX
//    name = source.getName();
//    manager = manager0.clone();
//
//    manager.put(new Key<Source>(name, Source.class), source);
//    spec = manager.get(new Key<Spec>(name, Spec.class));
//
//    // print as Unicode, reparse, and return
//    source = new StringSource(manager.get(new Key<UnicodeString>(name, UnicodeString.class)).toString());
//    source.setMarkup(Markup.UNICODE);
//    name = source.getName();
//    manager = manager0.clone();
//
//    manager.put(new Key<Source>(name, Source.class), source);
//    return manager.get(new Key<Spec>(name, Spec.class));
  }
}
