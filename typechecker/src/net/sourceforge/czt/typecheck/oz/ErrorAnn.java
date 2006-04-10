/*
  Copyright (C) 2004, 2005 Tim Miller
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
package net.sourceforge.czt.typecheck.oz;

import java.util.*;
import java.io.*;
import java.text.MessageFormat;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.print.oz.PrintUtils;
import net.sourceforge.czt.typecheck.oz.util.CarrierSet;

/**
 * A class for annotating terms associated with error messages.
 */
public class ErrorAnn
  extends net.sourceforge.czt.typecheck.z.ErrorAnn
{
  private static String RESOURCE_NAME =
    "net.sourceforge.czt.typecheck.oz.TypeCheckResources";
  private static ResourceBundle RESOURCE_BUNDLE =
    ResourceBundle.getBundle(RESOURCE_NAME);

  public ErrorAnn(String errorMessage, Object [] params,
                  SectionInfo sectInfo, String sectName,
                  LocAnn locAnn, Markup markup)
  {
    this(errorMessage, params, sectInfo, sectName, locAnn, null, markup);
  }

  public ErrorAnn(String errorMessage, Object [] params,
                  SectionInfo sectInfo, String sectName,
                  LocAnn locAnn, Term term, Markup markup)
  {
    super(errorMessage, params, sectInfo, sectName, locAnn, term, markup);
  }

  protected CarrierSet getCarrierSet()
  {
    return new CarrierSet(true);
  }

  protected void print(Term term,
                       Writer writer,
                       SectionInfo sectInfo,
                       String sectName,
                       Markup markup)
  {
    PrintUtils.print(term, writer, sectInfo, sectName, markup_);
  }
}

