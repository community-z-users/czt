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

package net.sourceforge.czt.parser.zeves;

import net.sourceforge.czt.parser.util.Decorword;
import net.sourceforge.czt.parser.util.LocInfo;

import net.sourceforge.czt.z.ast.*;

/**
 * Note that the wordpart of a decorword can be empty,
 * which does not represent a DECORWORD in the ISO Z standard.
 *
 * @author Petra Malik
 */
public class Proofword extends Decorword
{
  /**
   * @throws IllegalArgumentException if the list of strokes
                                      contains an unknown stroke type.
   */
  public Proofword(String word, ZStrokeList strokes, LocInfo locInfo)
  {
    super(word, strokes, locInfo);
  }

  public Proofword(String word, ZStrokeList strokes)
  {
    super(word, strokes);
  }

  public Proofword(String decorword, LocInfo locInfo)
  {
    super(decorword, locInfo);
  }

  public Proofword(String decorword)
  {
    super(decorword);
  }

 }
