/*
  Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.session;

import java.io.*;
import java.net.URL;
import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

public class WrappedSectionInfoRegistry
  implements SectionInfoRegistry
{
  private SectionInfoRegistry registry_;

  /**
   * A map from section name to ZSect.
   */
  private Map ast_ = new HashMap();

  public WrappedSectionInfoRegistry(SectionInfoRegistry registry)
  {
    if (registry == null) throw new NullPointerException();
    registry_ = registry;
  }

  /**
   * Returns a {@link ServiceCollection}.
   */
  public Collection getServices()
  {
    return registry_.getServices();
  }

  public Object getInfo(String sectionName, Class infoType)
  {
    ZSect sect = (ZSect) ast_.get(sectionName);
    if (sect == null) return registry_.getInfo(sectionName, infoType);
    Collection services = registry_.getServices();
    for (Iterator iter = services.iterator(); iter.hasNext(); ) {
      SectionInfoService service = (SectionInfoService) iter.next();
      if (infoType.equals(service.getInfoType())) {
        try {
          return service.run(sect);
        }
        catch (Exception e) {
          String message = "Error while applying service " + service +
            " to section " + sectionName + ": " + e.getMessage();
          CztLogger.getLogger(getClass()).warning(message);
        }
      }
    }
    return null;
  }

  public boolean isAvailable(String sectionName)
  {
    if (ast_.get(sectionName) != null) return true;
    return registry_.isAvailable(sectionName);
  }

  public boolean isAvailable(Class infoType)
  {
    return registry_.isAvailable(infoType);
  }

  /**
   * Adds all Z sections of the given specification.
   */
  public void add(Spec spec)
  {
    for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
      Sect sect = (Sect) iter.next();
      if (sect instanceof ZSect) {
        add((ZSect) sect);
      }
    }
  }

  /**
   * Adds a Z section.
   */
  public void add(ZSect sect)
  {
    ast_.put(sect.getName(), sect);
  }

  /**
   * Removes a Z section.
   */
  public ZSect remove(String name)
  {
    return (ZSect) ast_.remove(name);
  }
}
