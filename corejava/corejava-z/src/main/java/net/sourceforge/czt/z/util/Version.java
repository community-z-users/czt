/*
  Copyright (C) 2005, 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

/**
 * Defines version and XML Schema file location information.
 *
 * @author Petra Malik
 */
public interface Version
{
  String Z_MAJOR_VERSION_NUMBER = "2";
  String Z_MINOR_VERSION_NUMBER = "1";

  String ZML_VERSION =
    Z_MAJOR_VERSION_NUMBER + "." + Z_MINOR_VERSION_NUMBER;
  String Z_SCHEMA_LOCATION =
    "http://czt.sourceforge.net/zml/Z_" + Z_MAJOR_VERSION_NUMBER +
    "_" + Z_MINOR_VERSION_NUMBER + ".xsd";
}
