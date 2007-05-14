/*
  Copyright 2003, 2004, 2006 Mark Utting
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

import java.io.File;
import java.io.InputStream;
import org.xml.sax.InputSource;

import net.sourceforge.czt.base.ast.Term;

/**
 * <p>An XML reader.  It can read XML from a file or a stream
 * and converts it into an AST.</p>
 *
 * @author Petra Malik
 * @czt.todo Provide Exceptions that can be thrown
 *           in case the unmarshalling was unseccessful.
 */
public interface XmlReader
{
  /**
   * Unmarshalles XML data from the specified file and
   * returns the root term.
   *
   * @param file  the file to be unmarshalled.
   * @return the root element of the unmarshalled file.
   * @throws NullPointerException if <code>file</code>
   *                              is <code>null</code>.
   */
  Term read(File file)
    throws UnmarshalException;

  /**
   * Unmarshalles XML data from the specified source and
   * returns the root Term.
   * @param input  the source to be unmarshalled.
   * @return the root element of the unmarshalled file.
   * @throws NullPointerException if <code>file</code>
   *                              is <code>null</code>.
   */
  Term read(InputSource input)
    throws UnmarshalException;

  /**
   * Unmarshalles XML data from the specified input stream and
   * returns the root term.
   *
   * @param stream  the input stream used for unmarshalling.
   * @return the root element of the unmarshalled file.
   * @throws NullPointerException if <code>stream</code>
   *                              is <code>null</code>.
   */
  Term read(InputStream stream)
    throws UnmarshalException;
}
