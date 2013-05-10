/*
  Copyright (C) 2004, 2005, 2006 Petra Malik, Leo Freitas
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

package net.sourceforge.czt.print.circustime;

import java.io.Writer;

import net.sourceforge.czt.session.Dialect;

/**
 * Print Z specifications in Unicode.
 * This class adds the functionality to print Z/Circus tokens in unicode
 * to the PrintWriter class.
 *
 * @author Petra Malik, Leo Freitas
 */
public class UnicodePrinter
  extends net.sourceforge.czt.print.z.UnicodePrinter
{
  /**
   * Create a new PrintWriter, without automatic line flushing.
   *
   * @param out a character-output stream.
   */
  public UnicodePrinter(Writer out)
  {
    super(out);
  }

  /**
   * Create a new PrintWriter.
   *
   * @param out a character-output stream.
   * @param autoFlush a boolean; if true, the println() methods
   *                  will flush the output buffer
   */
  public UnicodePrinter(Writer out, boolean autoFlush)
  {
    super(out, autoFlush);
  }
  
	@Override
	public Dialect getDialect() {
		return Dialect.CIRCUSTIME;
	}

}
