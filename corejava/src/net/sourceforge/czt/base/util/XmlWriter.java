/*
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.base.util;

import java.io.OutputStream;
import java.io.Writer;
import net.sourceforge.czt.base.ast.Term;

/**
 * Provides methods for writing XML data.
 *
 * @author Petra Malik
 * @czt.todo Provide Exceptions that can be thrown
 *           in case the marshalling was unseccessful.
 */
public interface XmlWriter
{
  /**
   * Marshalles a Term into the specified Writer.
   *
   * @param term    the Term to be marshalled.
   * @param writer  the Writer used for marshalling.
   * @throws NullPointerException if <code>term</code>
   *         or <code>writer</code> is <code>null</code>.
   */
  public void write(Term term, Writer writer);

  /**
   * Marshalles a Term into the specified stream.
   *
   * @param term    the Term to be marshalled.
   * @param stream  the OutputStream used for marshalling.
   * @throws NullPointerException if <code>term</code>
   *         or <code>stream</code> is <code>null</code>.
   */
  public void write(Term term, OutputStream stream);
}
