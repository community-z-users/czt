/*
  Copyright (C) 2010 Leo Freitas
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

package net.sourceforge.czt.print.z;

/**
 * LaTeX printing section manager's property keys.
 * @author Leo
 */
public interface LatexPrinterPropertyKeys {

  /**
   * When this property is <code>true</code>, the LaTeX printing adds preamble/postscript
   * to LaTeX output in order to enable LaTeX compilation. Set to false when processing
   * multiple LaTeX printing for a single file.
   * DEFAULT = true; TYPE = boolean
   */
  String PROP_LATEXPRINTER_WRAPPING =
    "latexprinter_wrapping";

  boolean PROP_LATEXPRINTER_WRAPPING_DEFAULT = false;
}
