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

package net.sourceforge.czt.typecheck.z;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.parser.util.ErrorType;

/**
 * Warnings environment to be added to the section involved. This is to enable
 * filtered warnings to be reported.
 *
 * @author Leo Freitas
 * @date Nov 9, 2011
 */
public class SectWarningsAnn {

  private final List<ErrorAnn> warnings_ = new ArrayList<ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
  
  public final List<? extends ErrorAnn> getWarnings()
  {
    return Collections.unmodifiableList(warnings_);
  }

  public boolean isEmpty()
  {
    return size() == 0;
  }

  public int size()
  {
    return warnings_.size();
  }
  
  protected void addWarning(ErrorAnn error)
  { 
    if (error.getErrorType().equals(ErrorType.ERROR))
      throw new IllegalArgumentException("Cannot add error as warning: " + error.toString());
    warnings_.add(error);
  }

  public static SectWarningsAnn create()
  {
    return new SectWarningsAnn();
  }
}
