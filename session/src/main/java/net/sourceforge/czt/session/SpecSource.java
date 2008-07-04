/*
  Copyright (C) 2008 Ian Toyn
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

package net.sourceforge.czt.session;

import java.io.InputStream;
import java.io.Reader;
import java.io.IOException;
import net.sourceforge.czt.specreader.SpecReader;
import net.sourceforge.czt.specreader.CyclicSectionsException;
import net.sourceforge.czt.specreader.DupSectionNameException;
import net.sourceforge.czt.specreader.IllegalAnonSectionException;
import net.sourceforge.czt.specreader.SectionNotFoundException;

/**
 * A source that provides a whole spec.
 */
public class SpecSource
  extends Source
{
  private String filename_;
  private boolean isBufferingWanted_;
  private boolean isNarrativeWanted_;

  /**
   * @param filename the file from which to start reading the spec
   * @throws NullPointerException if filename is <code>null</code>.
   */
  public SpecSource(String filename, boolean isBufferingWanted, boolean isNarrativeWanted)
  {
    if (filename == null) throw new NullPointerException();
    filename_ = filename;
    isBufferingWanted_ = isBufferingWanted;
    isNarrativeWanted_ = isNarrativeWanted;
    setName(filename);
  }

  protected InputStream getStream()
  {
    throw new UnsupportedOperationException();
  }

  public Reader getReader()
    throws IOException
  {
    try {
      return new SpecReader(filename_, isBufferingWanted_, isNarrativeWanted_);
    }
    catch (CyclicSectionsException e) {
      throw new IOException(e.toString(), e);
    }
    catch (DupSectionNameException e) {
      throw new IOException(e.toString(), e);
    }
    catch (IllegalAnonSectionException e) {
      throw new IOException(e.toString(), e);
    }
    catch (SectionNotFoundException e) {
      throw new IOException(e.toString(), e);
    }
  }

  public String toString()
  {
    String result = getName();
    if (result == null) result = "SpecSource";
    return result;
  }
}
