/*
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.parser.util;

/**
 * Tokens for an operator word.
 */
public final class OperatorTokenType
{
  /** Prefix unary relation. */
  public static final OperatorTokenType PREP = new OperatorTokenType("PREP");
  /** Prefix unary function or generic. */
  public static final OperatorTokenType PRE = new OperatorTokenType("PRE");
  /** Postfix unary relation. */
  public static final OperatorTokenType POSTP = new OperatorTokenType("POSTP");
  /** Postfix unary function or generic. */
  public static final OperatorTokenType POST = new OperatorTokenType("POST");
  /** Infix binary relation. */
  public static final OperatorTokenType IP = new OperatorTokenType("IP");
  /** Infix binary function or generic. */
  public static final OperatorTokenType I = new OperatorTokenType("I");
  /** Left bracket or nun-unary relation. */
  public static final OperatorTokenType LP = new OperatorTokenType("LP");
  /** Left bracket of non-unary function or generic. */
  public static final OperatorTokenType L = new OperatorTokenType("L");
  /** First word preceded by expression of non-unary relation. */
  public static final OperatorTokenType ELP = new OperatorTokenType("ELP");
  /** First word preceded by expression of non-unary function or generic. */
  public static final OperatorTokenType EL = new OperatorTokenType("EL");
  /** Right bracket preceded by expression of non-unary relation. */
  public static final OperatorTokenType ERP = new OperatorTokenType("ERP");
  /** Right bracket preceded by expression of non-unary function or generic. */
  public static final OperatorTokenType ER = new OperatorTokenType("ER");
  /** Right bracket preceded by list argument of non-unary relation. */
  public static final OperatorTokenType SRP = new OperatorTokenType("SRP");
  /**
   * Right bracket preceded by list argument
   * of non-unary function or generic.
   */
  public static final OperatorTokenType SR = new OperatorTokenType("SR");
  /**
   * Last word followed by expression and preceded by expression
   * of tertiary or higher relation.
   */
  public static final OperatorTokenType EREP = new OperatorTokenType("EREP");
  /**
   * Last word followed by expression and preceded by expression
   * of tertiary or higher function or generic.
   */
  public static final OperatorTokenType ERE = new OperatorTokenType("ERE");
  /**
   * Last word followed by expression and preceded by list argument
   * of tertiary or higher relation.
   */
  public static final OperatorTokenType SREP = new OperatorTokenType("SREP");
  /**
   * Last word followed by expression and preceded by list argument
   * of tertiary or higher function or generic.
   */
  public static final OperatorTokenType SRE = new OperatorTokenType("SRE");
  /**
   * Middle word preceded by expression of non-unary operator.
   */
  public static final OperatorTokenType ES = new OperatorTokenType("ES");
  /**
   * Middle word preceded by expression of non-unary function or generic.
   */
  public static final OperatorTokenType SS = new OperatorTokenType("SS");
  private final String name_;

  /**
   * Only this class can construct instances.
   */
  private OperatorTokenType(String name)
  {
    name_ = name;
  }

  public int hashCode()
  {
    return super.hashCode();
  }

  public boolean equals(java.lang.Object o)
  {
    return super.equals(o);
  }

  public String toString()
  {
    return name_;
  }

  public static OperatorTokenType fromString(String value)
  {
    if (value.equals("PREP")) {
      return PREP;
    }
    if (value.equals("PRE")) {
      return PRE;
    }
    if (value.equals("POSTP")) {
      return POSTP;
    }
    if (value.equals("POST")) {
      return POST;
    }
    if (value.equals("IP")) {
      return IP;
    }
    if (value.equals("I")) {
      return I;
    }
    if (value.equals("LP")) {
      return LP;
    }
    if (value.equals("L")) {
      return L;
    }
    if (value.equals("ELP")) {
      return ELP;
    }
    if (value.equals("EL")) {
      return EL;
    }
    if (value.equals("ERP")) {
      return ERP;
    }
    if (value.equals("ER")) {
      return ER;
    }
    if (value.equals("SRP")) {
      return SRP;
    }
    if (value.equals("SR")) {
      return SR;
    }
    if (value.equals("EREP")) {
      return EREP;
    }
    if (value.equals("ERE")) {
      return ERE;
    }
    if (value.equals("SREP")) {
      return SREP;
    }
    if (value.equals("SRE")) {
      return SRE;
    }
    if (value.equals("ES")) {
      return ES;
    }
    if (value.equals("SS")) {
      return SS;
    }
    throw new IllegalArgumentException();
  }
}
