/**
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
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

public class SimpleSectionInfoRegistry
  implements SectionInfoRegistry
{
  /**
   * A map from section name to ZSect.
   */
  private Map ast_ = new HashMap();

  /**
   * A map from Class to SectionInfoService.
   */
  private Map services_ = new HashMap();

  public void register(SectionInfoService service)
    throws AlreadyRegisteredException
  {
    Class infoType = service.getInfoType();
    if (services_.get(infoType) != null) {
      String message = "Cannot register " + service + "; " +
        "section information of type " + infoType +
        " is already provided by " + services_.get(infoType);
      throw new AlreadyRegisteredException(message);
    }
    services_.put(infoType, service);
  }

  public Object getInfo(String sectionName, Class infoType)
  {
    SectionInfoService service = (SectionInfoService) services_.get(infoType);
    ZSect sect = (ZSect) ast_.get(sectionName);
    if (service == null || sect == null) return null;
    return service.run(sect);
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

  public Set getSects()
  {
    return ast_.keySet();
  }
}
