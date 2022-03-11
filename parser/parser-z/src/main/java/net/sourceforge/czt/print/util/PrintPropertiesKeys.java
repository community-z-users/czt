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

  String PROP_PRINT_ZEVES = "print_z_eves";

  String PROP_PRINTING_STRUCTURED_GOAL =
          "print_structured_goal";

  String PROP_PRINTING_ONTHEFLY_SECTION_NAME =
          "print_unknown_section_name";

  /**
   * The number of columns after which the pretty printer should
   * break the line (that is, insert a newline).
   */
  String PROP_TXT_WIDTH = "print_txt_width";

  String PROP_TXT_TAB_SIZE = "print_tab_size";

  boolean PROP_PRINT_NAME_IDS_DEFAULT = false;
  boolean PROP_PRINT_ZEVES_DEFAULT    = false;
  int PROP_TXT_WIDTH_DEFAULT          = 80; // ?
  int PROP_TXT_TAB_SIZE_DEFAULT       = 4;
  boolean PROP_PRINTING_STRUCTURED_GOAL_DEFAULT = false;
  String PROP_PRINTING_ONTHEFLY_SECTION_NAME_DEFAULT = null;
}
