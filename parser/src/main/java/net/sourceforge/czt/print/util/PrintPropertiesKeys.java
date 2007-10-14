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

package net.sourceforge.czt.print.util;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author Petra Malik
 */
public interface PrintPropertiesKeys
{
  /**
   * When set to <code>true</code>, the printer tools add
   * the id's of declaring and referencing names.
   */
  String PROP_PRINT_NAME_IDS = "print_name_ids";

  String PROP_Z_EVES = "print_z_eves";

  /**
   * The number of columns after which the pretty printer should
   * break the line (that is, insert a newline).
   */
  String PROP_TXT_WIDTH = "txt_width";
}
