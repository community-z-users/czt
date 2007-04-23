/*
  Copyright (C) 2006, 2007 Leo Freitas, Manuela Xavier
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
package net.sourceforge.czt.typecheck.circus;

import java.io.Writer;
import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.ast.LocAnn;

import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.print.circus.PrintUtils;

import net.sourceforge.czt.typecheck.circus.util.CarrierSet;

/**
 * A class for annotating terms associated with error messages.
 *
 * @author Leo Freitas
 * @author Manuela Xavier
 */
public class ErrorAnn
    extends net.sourceforge.czt.typecheck.z.ErrorAnn {
  
  private static String RESOURCE_NAME =
      "net.sourceforge.czt.typecheck.circus.TypeCheckResources";
  
  private static ResourceBundle RESOURCE_BUNDLE =
      ResourceBundle.getBundle(RESOURCE_NAME);
  
  public ErrorAnn(String errorMessage, Object [] params,
      SectionManager sectInfo, String sectName,
      LocAnn locAnn, Markup markup) {
    this(errorMessage, params, sectInfo, sectName, locAnn, null, markup);
  }
  
  public ErrorAnn(String errorMessage, Object [] params,
      SectionManager sectInfo, String sectName,
      LocAnn locAnn, Term term, Markup markup) {
    super(errorMessage, params, sectInfo, sectName, locAnn, term, markup);
  }
  
  protected CarrierSet getCarrierSet() {
    return new CarrierSet(true);
  }
  
  protected void print(Term term,
      Writer writer,
      SectionManager sectInfo,
      String sectName,
      Markup markup) {
    PrintUtils.print(term, writer, sectInfo, sectName, markup_);
  }
}
