/*
  Copyright (C) 2005, 2006, 2007 Petra Malik
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

import java.util.Stack;

import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.PrintVisitor;
import net.sourceforge.czt.z.util.ZChar;

/**
 * Note that the wordpart of a decorword can be empty,
 * which does not represent a DECORWORD in the ISO Z standard.
 *
 * @author Petra Malik
 */
public class Decorword
{
  // the factory can be static - Leo 
  private final static Factory factory_ = new Factory();
  private String name_;
  private String word_;
  private ZStrokeList strokes_;
  private LocInfo locInfo_;
  
  private Object extraInfo_ = null;

  /**
   * @throws IllegalArgumentException if the list of strokes
                                      contains an unknown stroke type.
   */
  public Decorword(String word, ZStrokeList strokes, LocInfo locInfo)
  {
    this(word, strokes);
    locInfo_ = locInfo;
  }

  public Decorword(String word, ZStrokeList strokes)
  {
    word_ = word;
    strokes_ = strokes;
    name_ = word + strokes.accept(new PrintVisitor());
  }

  public Decorword(String decorword, LocInfo locInfo)
  {
    this(decorword);
    locInfo_ = locInfo;
  }

  public Decorword(String decorword)
  {
    name_ = decorword;
    strokes_ = factory_.createZStrokeList();
    word_ = factory_.getWordAndStrokes(decorword, strokes_);
  }

  public String getName()
  {
    return name_;
  }

  public String getWord()
  {
    return word_;
  }

  public ZStrokeList getStrokes()
  {
    return strokes_;
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
    for (int i = 0; i < zchars.length; i++) {
      if (zchars[i].equals(ZChar.NE) || zchars[i].equals(ZChar.SE)) {
        stack.push(zchars[i]);
      }
      else if (zchars[i].equals(ZChar.NW) || zchars[i].equals(ZChar.SW)) {
        if (! stack.empty()) {
          ZChar zchar = stack.pop();
          boolean sub = zchars[i].equals(ZChar.NW) && zchar.equals(ZChar.SE);
          boolean sup = zchars[i].equals(ZChar.SW) && zchar.equals(ZChar.NE);
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

  public <T> void setExtraInfo(T o)
  {
    extraInfo_ = o;
  }
  
  @SuppressWarnings("unchecked")
  public <T> T getExtraInfo()
  {
     return (T)extraInfo_;
  }  
  
  public String toString()
  {
    return name_;
  }
}
