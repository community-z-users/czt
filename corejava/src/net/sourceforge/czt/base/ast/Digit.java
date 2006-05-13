/*
  Copyright 2003, 2006 Mark Utting
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

package net.sourceforge.czt.base.ast;

public enum Digit
{
  ZERO(0),
  ONE(1),
  TWO(2),
  THREE(3),
  FOUR(4),
  FIVE(5),
  SIX(6),
  SEVEN(7),
  EIGHT(8),
  NINE(9);

  private int value_;

  private Digit(int value)
  {
    value_ = value;
  }

  public int getValue()
  {
    return value_;
  }

  /**
   * @param i the digit; must be between zero and nine.
   */
  public static Digit fromValue(int i)
  {
    if (i == 0) return ZERO;
    if (i == 1) return ONE;
    if (i == 2) return TWO;
    if (i == 3) return THREE;
    if (i == 4) return FOUR;
    if (i == 5) return FIVE;
    if (i == 6) return SIX;
    if (i == 7) return SEVEN;
    if (i == 8) return EIGHT;
    if (i == 9) return NINE;
    throw new IllegalArgumentException("Int value: " + i);
  }
}
