/*
  Copyright (C) 2006, 2007 Petra Malik
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

package net.sourceforge.czt.zml;

import java.net.URL;

/**
 * A class that converts resources to valid URLs.
 *
 * @author Petra Malik
 */
public final class Resources
{
  private static String EXAMPLES = "examples/";
  private static String XSD_DIR = "xsd/";
  private static String Z_SCHEMA = "Z.xsd";
  private static String OZ_SCHEMA = "Object-Z.xsd";
  private static String TCOZ_SCHEMA = "TCOZ.xsd";
  private static String CIRCUS_SCHEMA = "Circus.xsd";
  private static String ZPATTERN_SCHEMA = "ZPattern.xsd";
  private static String CIRCUSPATTERN_SCHEMA = "CircusPattern.xsd";
  private static String CIRCUSTIME_SCHEMA = "CircusTime.xsd";
  private static String CIRCUSCONF_SCHEMA = "CircusConf.xsd";
  private static String ZEVES_SCHEMA = "ZEves.xsd";

  /**
   * Do not create instances of this class.
   */
  private Resources()
  {
  }

  public static URL getSchema(String schemaFileName)
  {
    return Resources.class.getResource(XSD_DIR + schemaFileName);
  }

  public static URL getZSchema()
  {
    return getSchema(Z_SCHEMA);
  }

  public static URL getOzSchema()
  {
    return getSchema(OZ_SCHEMA);
  }

  public static URL getTcozSchema()
  {
    return getSchema(TCOZ_SCHEMA);
  }

  public static URL getCircusSchema()
  {
    return getSchema(CIRCUS_SCHEMA);
  }

  public static URL getZpattSchema()
  {
    return getSchema(ZPATTERN_SCHEMA);
  }
  
  public static URL getCircusPattSchema()
  {
    return getSchema(CIRCUSPATTERN_SCHEMA);
  }

  public static URL getCircusTimeSchema()
  {
    return getSchema(CIRCUSTIME_SCHEMA);
  }

  public static URL getCircusConfSchema()
  {
    return getSchema(CIRCUSCONF_SCHEMA);
  }

  public static URL getZEvesSchema()
  {
    return getSchema(ZEVES_SCHEMA);
  }

  public static URL getExample(String dialect, String name)
  {
    return Resources.class.getResource(EXAMPLES + dialect + "/" + name);
  }

  public static URL getZExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "z/" + name);
  }

  public static URL getOzExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "oz/" + name);
  }

  public static URL getCircusExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "circus/" + name);
  }  

  public static URL getCircusTimeExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "circustime/" + name);
  }  

  public static URL getCircusConfExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "circusconf/" + name);
  }  

  public static URL getZEvesExample(String name)
  {
    return Resources.class.getResource(EXAMPLES + "zeves/" + name);
  }

}
