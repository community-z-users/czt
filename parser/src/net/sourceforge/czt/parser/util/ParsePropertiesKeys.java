/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.parser.util;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author Petra Malik
 */
public interface ParsePropertiesKeys
{
  /**
   * When set to <code>true</code>, the parser tools will extract
   * symbol characters COMMA, SEMICOLON, and FULL STOP from the
   * beginning and end of a WORD token to become WORDs themselves.
   * This is a planned change to the Z Standard; see also
   * the Draft Technical Corrigendum 1: Corrections,
   * including to use of Unicode, March 17th, 2006.
   * As of now, this has yet to be submitted for official ballot.
   */
  String PROP_EXTRACT_COMMA_OR_SEMI_FROM_DECORWORDS =
    "extract_comma_or_semi";

  /**
   * When set to <code>true</code>, the parser tools will ignore
   * unknown latex commands (that is, give a warning and use the name
   * of the command) instead of reporting an error.  Reporting an
   * error is Standard conforming but ignoring those unknown commands
   * is sometimes convenient.
   */
  String PROP_IGNORE_UNKNOWN_LATEX_COMMANDS = "ignore_unknow_latex_commands";
}
