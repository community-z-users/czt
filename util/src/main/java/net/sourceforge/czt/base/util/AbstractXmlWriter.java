/*
Copyright 2004 Mark Utting
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
import java.io.OutputStreamWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;

import net.sourceforge.czt.base.ast.Term;

/**
 * This class provides a skeletal implementation of the XmlWriter interface.
 * To implement an XmlWriter, the programmer needs only to extend this class
 * and provide implementations for the write(Term, Writer) method.
 *
 * @author Petra Malik
 */
public abstract class AbstractXmlWriter
  implements XmlWriter
{
  private String encoding_ = "UTF-8";

  @Override
  public String getEncoding()
  {
    return encoding_;
  }

  @Override
  public void setEncoding(String encoding)
  {
    encoding_ = encoding;
  }

  @Override
  public abstract void write(Term term, Writer writer)
    throws MarshalException;

  @Override
  public void write(Term term, OutputStream stream)
    throws MarshalException
  {
    try {
      write(term, new OutputStreamWriter(stream, encoding_));
    }
    catch (UnsupportedEncodingException e)
    {
      throw new MarshalException(e);
    }
  }
}
