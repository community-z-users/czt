/*
  Copyright (C) 2006, 2007 Leo Freitas
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
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.PerformanceSettings;

import net.sourceforge.czt.z.ast.LocAnn;

import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;

import net.sourceforge.czt.print.circus.PrintUtils;

import net.sourceforge.czt.typecheck.circus.util.CarrierSet;

/**
 * A class for annotating terms associated with error messages.
 *
 * @author Leo Freitas
 */
public class ErrorAnn
    extends net.sourceforge.czt.typecheck.z.ErrorAnn {
  
  private List<ErrorAnn> callErrors_ = new ArrayList<ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  
  private final static String RESOURCE_NAME =
      "net.sourceforge.czt.typecheck.circus.TypeCheckResources";
  
  private final static ResourceBundle RESOURCE_BUNDLE =
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
  
  @Override
  protected CarrierSet getCarrierSet() {
    return new CarrierSet(true);
  }
  
  @Override
  protected void print(Term term,
      Writer writer,
      SectionManager sectInfo,
      String sectName,
      Markup markup) {
    PrintUtils.print(term, writer, sectInfo, sectName, markup_);
  }
  
  /**
   * In the case of inner errors raised during postchecking for calls,
   * add them to the originating message.
   * 
   * @return the compound error string.
   */
  @Override
  public String getMessage()
  {
    StringBuilder result = new StringBuilder("\n"); // add an extra new line for error messages
    result.append(super.getMessage());
    for(ErrorAnn e : callErrors_)
    {
      result.append("\n------------------------------\n");
      result.append(e.getMessage());
    }
    if (!callErrors_.isEmpty())
    {
      result.append("\n------------------------------\n");
    }
    return result.toString();
  }
  
  protected List<ErrorAnn> callErrors()
  {
    return Collections.unmodifiableList(callErrors_);
  }
  
  protected void addCallErrors(List<ErrorAnn> list)
  {
    callErrors_.addAll(list);
  }
  
  protected void clearCallErrors()
  {
    callErrors_.clear();
  }

  @Override
  protected ResourceBundle getResourceBundle()
  {
    return RESOURCE_BUNDLE;
  }

  @Override
  public String getStringFromResourceBundle(String key)
  {
    return RESOURCE_BUNDLE.getString(key);
  }
}
