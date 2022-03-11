/*
  Copyright (C) 2003, 2004 Mark Utting
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
 */
public interface XmlWriter
{
  /**
   * Returns the output encoding to use when marshalling the XML data.
   * "UTF-8" is used by default if this property has not been set.
   */
  String getEncoding();

  /**
   * Sets the output encoding to use when marshalling the XML data.
   * "UTF-8" is used by default if this property has not been set.
   */
  void setEncoding(String encoding);

  /**
   * Marshalles a Term into the specified Writer.
   *
   * @param term    the Term to be marshalled.
   * @param writer  the Writer used for marshalling.
   * @throws MarshalException if an error has occured during marshalling.
   * @throws NullPointerException if <code>term</code>
   *         or <code>writer</code> is <code>null</code>.
   */
  void write(Term term, Writer writer)
    throws MarshalException;

  /**
   * Marshalles a Term into the specified stream.
   *
   * @param term    the Term to be marshalled.
   * @param stream  the OutputStream used for marshalling.
   * @throws MarshalException if an error has occured during marshalling.
   * @throws NullPointerException if <code>term</code>
   *         or <code>stream</code> is <code>null</code>.
   */
  void write(Term term, OutputStream stream)
    throws MarshalException;
}
