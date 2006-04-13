/*
  Copyright (C) 2005, 2006 Petra Malik
  This file is part of the czt project: http://czt.sourceforge.net

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

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Stack;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZChar;

/**
 * Note that the wordpart of a decorword can be empty,
 * which does not represent a DECORWORD in the ISO Z standard.
 *
 * @author Petra Malik
 */
public class Decorword
{
  private Factory factory_ = new Factory();
  private String name_;
  private String word_;
  private List<Stroke> strokes_ = new ArrayList<Stroke>();
  private LocInfo locInfo_;

  /**
   * @throws IllegalArgumentException if the list of strokes
                                      contains an unknown stroke type.
   */
  public Decorword(String word, List strokes, LocInfo locInfo)
  {
    this(word, strokes);
    locInfo_ = locInfo;
  }

  public Decorword(String word, List strokes)
  {
    word_ = word;
    strokes_.addAll(strokes);
    StringBuffer buffer = new StringBuffer();
    buffer.append(word);
    for (Iterator iter = strokes.iterator(); iter.hasNext(); ) {
      Stroke stroke = (Stroke) iter.next();
      if (stroke instanceof InStroke) {
        buffer.append(ZChar.INSTROKE);
      }
      else if (stroke instanceof OutStroke) {
        buffer.append(ZChar.OUTSTROKE);
      }
      else if (stroke instanceof NextStroke) {
        buffer.append(ZChar.PRIME);
      }
      else if (stroke instanceof NumStroke) {
        NumStroke numStroke = (NumStroke) stroke;
        buffer.append(ZChar.SE);
        buffer.append(numStroke.getDigit());
        buffer.append(ZChar.NW);
      }
      else {
        throw new IllegalArgumentException("Unexpected stroke");
      }
    }
    name_ = buffer.toString();
  }

  public Decorword(String decorword, LocInfo locInfo)
  {
    this(decorword);
    locInfo_ = locInfo;
  }

  public Decorword(String decorword)
  {
    name_ = decorword;
    ZChar[] zchars = ZChar.toZChars(decorword);
    int i;
    for (i = zchars.length - 1; i >= 0; i--) {
      ZChar zchar = zchars[i];
      if (ZChar.INSTROKE.equals(zchar)) {
        strokes_.add(0, factory_.createInStroke());
      }
      else if (ZChar.OUTSTROKE.equals(zchar)) {
        strokes_.add(0, factory_.createOutStroke());
      }
      else if (ZChar.PRIME.equals(zchar)) {
        strokes_.add(0, factory_.createNextStroke());
      }
      else if (i >= 2 &&
          ZChar.NW.equals(zchar) &&
          ZChar.isDigit(zchars[i - 1]) &&
          ZChar.SE.equals(zchars[i - 2])) {
        NumStroke numStroke =
          factory_.createNumStroke(new Integer(zchars[i - 1].toString()));
        strokes_.add(numStroke);
        i = i - 2;
      }
      else {
        break;
      }
    }
    StringBuffer result = new StringBuffer();
    for (int j = 0; j <= i; j++) {
      result.append(zchars[j].toString());
    }
    word_ = result.toString();
  }

  public String getName()
  {
    return name_;
  }

  public String getWord()
  {
    return word_;
  }

  public Stroke[] getStrokes()
  {
    return strokes_.toArray(new Stroke[0]);
  }

  /**
   * <p>Checks that in the word part of this decorword each SE
   * character has a following NW character, and each NE character has
   * a following SW character, and that these occur only in nested
   * pairs (see also Z Standard, first edition, 7.4.1).<p>
   *
   * @return the unmatched ZChar, or <code>null</code> if all wordglue
   *         characters match.
   */
  public ZChar check()
  {
    Stack<ZChar> stack = new Stack<ZChar>();
    ZChar[] zchars = ZChar.toZChars(word_);
    for(int i = 0; i < zchars.length; i++) {
      if (zchars[i].equals(ZChar.NE) || zchars[i].equals(ZChar.SE)) {
        stack.push(zchars[i]);
      }
      else if (zchars[i].equals(ZChar.NW) || zchars[i].equals(ZChar.SW)) {
        if (! stack.empty()) {
          ZChar zchar = stack.pop();
          boolean sub = zchars[i].equals(ZChar.NW) &&
          zchar.equals(ZChar.SE);
          boolean sup = zchars[i].equals(ZChar.SW) &&
          zchar.equals(ZChar.NE);
          if (! (sub || sup)) {
            return zchars[i];
          }
        }
      }
    }
    if (! stack.empty()) {
      return stack.pop();
    }
    return null;
  }

  public void setLocation(LocInfo locInfo)
  {
    locInfo_ = locInfo;
  }

  public LocInfo getLocation()
  {
    return locInfo_;
  }

  public String toString()
  {
    StringBuffer result = new StringBuffer();
    result.append(getWord());
    for (int i = 0; i < getStrokes().length; i++) {
      Stroke stroke = (Stroke) getStrokes()[i];
      if (stroke instanceof InStroke) {
        result.append(ZChar.INSTROKE);
      }
      else if (stroke instanceof OutStroke) {
        result.append(ZChar.OUTSTROKE);
      }
      else if (stroke instanceof NextStroke) {
        result.append(ZChar.PRIME);
      }
      else if (stroke instanceof NumStroke) {
        NumStroke numStroke = (NumStroke) stroke;
        result.append(ZChar.SE);
        result.append(numStroke.getDigit());
        result.append(ZChar.NW);
      }
      else {
        result.append(stroke.toString());
      }
    }
    return result.toString();
  }
}
