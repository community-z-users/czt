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
import java.util.*;

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.z.ast.*;

/**
 * A simple section info registry that allows registration of services
 * as well as adding and removing Z sections.
 *
 * @author Petra Malik
 */
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

  /**
   * Returns a {@link ServiceCollection}.
   */
  public Collection getServices()
  {
    return new ServiceCollection();
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

  public void put(Key key, Object value, Set/*<Key>*/ dependencies)
  {
    if (value instanceof ZSect) {
      ZSect zSect = (ZSect) value;
      String name = zSect.getName();
      ast_.put(name, zSect);
      return;
    }
    throw new UnsupportedOperationException();
  }

  /**
   * Removes a Z section.
   */
  public ZSect remove(String name)
  {
    return (ZSect) ast_.remove(name);
  }

  /**
   * Handles access to services.
   *
   * @author Petra Malik
   */
  private class ServiceCollection
    extends AbstractCollection
  {
    /**
     * @throws NullPointerException if the object is <code>null</code>
     * @throws ClassCastException if the given object is not of type
     *         SectionInfoService.
     * @throws IllegalArgumentException if a different service
     *         that provides that type of information is already registered.
     */
    public boolean add(Object o)
    {
      SectionInfoService service = (SectionInfoService) o;
      Class infoType = service.getInfoType();
      SectionInfoService existingService =
        (SectionInfoService) services_.get(infoType);
      if (existingService != null) {
        if (existingService.equals(service)) return false;
        String message = "Cannot register " + service + "; " +
          "section information of type " + infoType +
          " is already provided by " + services_.get(infoType);
        throw new IllegalArgumentException(message);
      }
      services_.put(infoType, service);
      return true;
    }

    public Iterator iterator()
    {
      return services_.values().iterator();
    }

    public int size()
    {
      return services_.values().size();
    }
  }
}
