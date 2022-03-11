/*
  Copyright (C) 2007 Leo Freitas
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

package net.sourceforge.czt.typecheck.zeves;

/**
 * <P>Contains String constants for the keys used in parse properties.</P>
 *
 * <P>The behaviour of the CZT parser utilities (scanner, parser, etc.)
 * can be configured via Properties.  This interface provides the String
 * constants that are currently supported by the parser utilities.</P>
 *
 * @author Leo Freitas
 */
public interface TypecheckPropertiesKeys
  extends net.sourceforge.czt.typecheck.z.TypecheckPropertiesKeys
{
  WarningManager.WarningOutput PROP_TYPECHECK_WARNINGS_OUTPUT_ZEVES_DEFAULT = WarningManager.WarningOutput.HIDE;
}
