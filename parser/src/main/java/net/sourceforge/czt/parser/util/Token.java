/*
  Copyright (C) 2006 Petra Malik
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
 * <p>A token is an object with a name and an optional spelling, which is
 * usually created by a lexer (or scanner) and subsequently used in a
 * parser.  A typical Z token is LPAREN, which is created when the
 * lexer finds a '('-character.  Another typical Z Token is DECORWORD,
 * which is created when the lexer finds a decorated word like "x?".
 * The DECORWORD token has usually a spelling associated, "x?" in the
 * example above.</p>
 *
 * <p>It is convenient to allow any Object to be used as a spelling
 * for a token.  For example, a NUMERAL token could have an Integer as
 * spelling.  The <code>toString()</code> method of the spelling
 * object should return the string from which the lexer created this
 * token.
 *
 * @author Petra Malik
 */
public interface Token
{
  String getName();
  Object getSpelling();
  String spelling();
  NewlineCategory getNewlineCategory();
}
