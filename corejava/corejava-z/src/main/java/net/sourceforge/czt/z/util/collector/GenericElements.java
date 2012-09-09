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
package net.sourceforge.czt.z.util.collector;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.ast.ZNameList;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public abstract class GenericElements<R> extends BaseElements<R>
{

  // lists and collectors never null.
  private final List<ZName> fGenerics;

  /** Creates a new instance of GenericElements
   */
  protected GenericElements()
  {
    super();
    fGenerics = new ArrayList<ZName>();
  }

  protected void collectGenerics(ZNameList generics)
  {
    if (generics != null)
    {
      for (Name n : generics)
      {
        fGenerics.add(ZUtils.assertZName(n));
      }
    }
  }

  public List<ZName> getFormalParameters()
  {
    return Collections.unmodifiableList(fGenerics);
  }

  @Override
  public String toString()
  {
    return super.toString() + " " + (getFormalParameters().isEmpty() ? "" : getFormalParameters().toString());
  }
}
