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

import net.sourceforge.czt.parser.util.*;
import net.sourceforge.czt.parser.z.*;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.*;

/**
 * Provides section information for the toolkit sections, including
 * the prelude.
 *
 * @author Petra Malik
 */
public final class ToolkitSectionInfoRegistry
  implements SectionInfoRegistry
{
  private static ToolkitSectionInfoRegistry instance_ = init();

  /**
   * A map from section name to ZSect.
   */
  private Map ast_ = new HashMap();

  /**
   * A map from Class to SectionInfoService.
   */
  private Map services_ = new HashMap();

  private static ToolkitSectionInfoRegistry init()
  {
    ToolkitSectionInfoRegistry result =
      new ToolkitSectionInfoRegistry();
    result.initServices();
    result.initSections();
    return result;
  }

  public static SectionInfoRegistry getInstance()
  {
    return instance_;
  }

  private void initServices()
  {
    SectionInfoService[] services = {
      new OpTableService(this),
      new DefinitionTableService(this),
      new LatexMarkupFunctionService(this)
    };

    for (int i = 0; i < services.length; i++) {
      Class infoType = services[i].getInfoType();
      services_.put(services[i].getInfoType(), services[i]);
    }
  }

  private void initSections()
  {
    String[] toolkitFiles = {
      "prelude.tex",
      "set_toolkit.tex",
      "relation_toolkit.tex",
      "function_toolkit.tex",
      "number_toolkit.tex",
      "sequence_toolkit.tex",
      "standard_toolkit.tex"
    };
    for (int i = 0; i < toolkitFiles.length; i++) {
      parse(toolkitFiles[i]);
    }
  }

  public void parse(String filename)
  {
    String message = "Parsing " + filename + " ... ";
    CztLogger.getLogger(ToolkitSectionInfoRegistry.class).info(message);
    try {
      URL url = getClass().getResource("/lib/" + filename);
      Spec spec = (Spec) ParseUtils.parse(url, this);
      for (Iterator iter = spec.getSect().iterator(); iter.hasNext(); ) {
        Object o = iter.next();
        if (o instanceof ZSect) {
          ZSect zSect = (ZSect) o;
          String name = zSect.getName();
          ast_.put(name, zSect);
          message = "Adding " + name + ".";
          CztLogger.getLogger(ToolkitSectionInfoRegistry.class).info(message);
        }
      }
    }
    catch (Exception e) {
      throw new CztException("Cannot parse toolkit " + filename, e);
    }
  }

  /**
   * Returns a {@link ServiceCollection}, that is a collection
   * that does not support adding elements.
   */
  public Collection getServices()
  {
    return new ServiceCollection();
  }

  public Object getInfo(String sectionName, Class infoType)
  {
    SectionInfoService service = (SectionInfoService) services_.get(infoType);
    ZSect sect = (ZSect) ast_.get(sectionName);
    if (service == null || sect == null) {
      String message =
        "Cannot get " + infoType.getName() +
        " for section '" + sectionName + "'";
      CztLogger.getLogger(ToolkitSectionInfoRegistry.class).warning(message);
      return null;
    }
    return service.run(sect);
  }

  public void put(Key key, Object value, Set/*<Key>*/ dependencies)
  {
    throw new UnsupportedOperationException();
  }

  /**
   * Delegates all calls to member variable <code>services_.values()</code>.
   *
   * @author Petra Malik
   */
  private class ServiceCollection
    extends AbstractCollection
  {
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
