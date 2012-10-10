/*
  Copyright (C) 2003, 2004, 2005 Tim Miller
  Copyright (C) 2007 Petra Malik
  This file is part of the CZT project.

  The CZT project contains free software;
  you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.parser.z;

import java.math.BigInteger;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.LocInfo;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.z.ast.LocAnn;
import net.sourceforge.czt.z.util.Factory;

/**
 * A class recording parser state related information.
 */
public class ParserState
{
  /** The type of the previous chain relation e.g. MEM, EQUALS, IP */
  private int previousChain_ = -1;
  private Factory factory_ = new Factory();
  private final Source loc_;
  private String sectName_ = null;

  public ParserState(Source source)
  {
    loc_ = source;
  }

  public void setPreviousChain(int previousChain)
  {
    previousChain_ = previousChain;
  }

  public boolean isPreviousChain(int value)
  {
    return previousChain_ == value;
  }

  public String getCurrentSectName()
  {
    return sectName_;
  }

  public void setCurrentSectName(String v)
  {
    sectName_ = v;
  }

  /**
   * Refactored from Parser.xml to ParserState.java
   * so that ParserState methods can not only create
   * elements but also add location information. Parser.xml
   * initialises getLoc() to be the same as the parsing source.
   * @return
   */
  public String getLoc()
  {
    return loc_.toString();
  }
  
  public LocAnn toLocAnn(LocInfo locInfo, boolean usePhysicalLoc)
  {
    LocAnn locAnn = factory_.createLocAnn();
    if (usePhysicalLoc)
    {
      locAnn.setLoc(getLoc());
    }
    if (locInfo.getLine() >= 0) {
      locAnn.setLine(BigInteger.valueOf(locInfo.getLine()));
    }
    if (locInfo.getColumn() >= 0) {
      locAnn.setCol(BigInteger.valueOf(locInfo.getColumn()));
    }
    if (locInfo.getStart() >= 0) {
      locAnn.setStart(BigInteger.valueOf(locInfo.getStart()));
    }
    if (locInfo.getLength() >= 0) {
      locAnn.setLength(BigInteger.valueOf(locInfo.getLength()));
    }
    return locAnn;
  }
  
  public LocAnn toLocAnn(LocInfo locInfo)
  {
    return toLocAnn(locInfo, false);
  }

  public void addLocAnn(Term term, LocInfo locInfo)
  {
    if (locInfo != null) {
      LocAnn locAnn = term.getAnn(LocAnn.class);
      if (locAnn == null) {
        locAnn = factory_.createLocAnn();
        term.getAnns().add(locAnn);
      }
      locAnn.setLoc(getLoc());
      if (locInfo.getLine() >= 0) {
        locAnn.setLine(BigInteger.valueOf(locInfo.getLine()));
      }
      if (locInfo.getColumn() >= 0) {
        locAnn.setCol(BigInteger.valueOf(locInfo.getColumn()));
      }
      if (locInfo.getStart() >= 0) {
        locAnn.setStart(BigInteger.valueOf(locInfo.getStart()));
      }
      if (locInfo.getLength() >= 0) {
        locAnn.setLength(BigInteger.valueOf(locInfo.getLength()));
      }
    }
  }
}
