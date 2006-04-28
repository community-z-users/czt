/*
  Copyright (C) 2004, 2005, 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.StringTokenizer;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;

/**
 * An operator name.
 */
public class OperatorName
{
  /**
   * The factory used when AST objects are created.
   */
  private static Factory factory_ = new Factory();

  /**
   * The string representation of this operator name as it is used
   * within the AST classes and without strokes.
   * For instance, " _ + _ ".
   */
  private String word_;

  /**
   * The list of decorations of this operator name.
   */
  private List strokes_ = null;

  /**
   * The string list representation of this operator name,
   * for instance ["_", "+", "_"] but without strokes.
   */
  private List<String> list_;

  /**
   * Creates a new operator name with the given name and strokes.
   *
   * @param name a name that does not contain decorations.
   * @throws OperatorNameException if the given name does not
   *         represent an operator name.
   */
  public OperatorName(String name, List strokes)
    throws OperatorNameException
  {
    word_ = name;
    strokes_ = strokes;
    list_ = wordToList(name);
  }

  /**
   * Creates a new operator name from the given name.
   *
   * @param name the name from which the operator name is constructed.
   * @throws OperatorNameException if the given name does not
   *         represent an operator name.
   */
  public OperatorName(ZDeclName name)
    throws OperatorNameException
  {
    this(name.getWord(), name.getStroke());
  }
  public OperatorName(ZRefName name)
    throws OperatorNameException
  {
    this(name.getWord(), name.getStroke());
  }

  /**
   * Create some operator name from a single operator word.
   *
   * @param name a name that does not contain decorations.
   * @param strokes the strokes of this operator name
   *                (can be <code>null</code>).
   * @param fixity must be INFIX, PREFIX, or POSTFIX.
   */
  public OperatorName(String name, List strokes, Fixity fixity)
    throws OperatorNameException
  {
    if (Fixity.INFIX.equals(fixity)) {
      word_ = ZString.ARG_TOK + name + ZString.ARG_TOK;
      strokes_ = strokes;
      list_ = wordToList(word_);
    }
    else if (Fixity.PREFIX.equals(fixity)) {
      word_ = name + ZString.ARG_TOK;
      strokes_ = strokes;
      list_ = wordToList(word_);
    }
    else if (Fixity.POSTFIX.equals(fixity)) {
      word_ = ZString.ARG_TOK + name;
      strokes_ = strokes;
      list_ = wordToList(word_);
    }
    else throw new UnsupportedOperationException();
  }

  /**
   * Creates a list representation of an operator name
   * and checks whether operator tokens and argument tokens
   * are alternatingly.
   */
  private static List<String> wordToList(String name)
    throws OperatorNameException
  {
    final String errorMessage = name + " is not an operator name.";
    List<String> result = new ArrayList<String>();
    StringTokenizer tokenizer = new StringTokenizer(name);
    Boolean expectArgument = null;

    while (tokenizer.hasMoreTokens()) {
      String token = tokenizer.nextToken();
      if (token != null && ! token.equals("")) {
        if (token.equals(ZString.ARG) || token.equals(ZString.LISTARG)) {
          if (Boolean.FALSE.equals(expectArgument)) {
            throw new OperatorNameException(errorMessage);
          }
          result.add(token);
          expectArgument = Boolean.FALSE;
        }
        else {
          if (Boolean.TRUE.equals(expectArgument)) {
            throw new OperatorNameException(errorMessage);
          }
          result.add(token);
          expectArgument = Boolean.TRUE;
        }
      }
    }
    if (result.size() <= 1) {
      throw new OperatorNameException(errorMessage);
    }
    return result;
  }

  /**
   * Transforms a list of strokes into a (unicode) string.
   */
  private static String strokeListToString(List strokes)
  {
    if (strokes == null) return "";
    StringBuffer result = new StringBuffer();
    for (Iterator iter = strokes.iterator(); iter.hasNext();)
    {
      Stroke stroke = (Stroke) iter.next();
      result.append(stroke.toString());
    }
    return result.toString();
  }

  public String getWord()
  {
    return word_;
  }

  public List getStroke()
  {
    return strokes_;
  }

  /**
   * Checks whether this operator is unary.
   * More precisely, this method checks whether this operator contains
   * exactly one argument.
   */
  public boolean isUnary()
  {
    final String ARG = ZString.ARG;
    final String LISTARG = ZString.LISTARG;
    final String first = list_.get(0);
    boolean sizeIsTwo = list_.size() == 2;
    boolean sizeIsThree = list_.size() == 3;
    boolean firstIsArg = first.equals(ARG) || first.equals(LISTARG);
    return sizeIsTwo || (sizeIsThree && ! firstIsArg);
  }

  public Fixity getFixity()
  {
    if (list_.size() < 2) {
      final String message =
        "A list of size smaller than two cannot occur in operator names.";
      throw new CztException(message);
    }
    final String ARG = ZString.ARG;
    final String LISTARG = ZString.LISTARG;
    final String first = list_.get(0);
    final String last = list_.get(list_.size() - 1);
    boolean firstIsArg = first.equals(ARG) || first.equals(LISTARG);
    boolean lastIsArg = last.equals(ARG) || last.equals(LISTARG);
    if (firstIsArg) {
      if (lastIsArg) return Fixity.INFIX;
      else           return Fixity.POSTFIX;
    }
    else {
      if (lastIsArg) return Fixity.PREFIX;
      else           return Fixity.NOFIX;
    }
  }

  public String[] getWords()
  {
    return list_.toArray(new String[0]);
  }

  public String toString()
  {
    return getWord();
  }

 public static class OperatorNameException
    extends Exception
  {
    public OperatorNameException()
    {
      super();
    }

    public OperatorNameException(String message)
    {
      super(message);
    }

    public OperatorNameException(String message, Throwable cause)
    {
      super(message, cause);
    }

    public OperatorNameException(Throwable cause)
    {
      super(cause);
    }
  }

  /**
   * A typesafe enumeration of fixity.
   */
  public static final class Fixity
  {
    public static final Fixity PREFIX = new Fixity("PREFIX");
    public static final Fixity POSTFIX = new Fixity("POSTFIX");
    public static final Fixity INFIX = new Fixity("INFIX");
    public static final Fixity NOFIX = new Fixity("NOFIX");
    private final String name_;

    /**
   * Only this class can construct instances.
   */
    private Fixity(String name)
    {
      name_ = name;
    }

    public String toString()
    {
      return name_;
    }

    public static Fixity fromString(java.lang.String value)
    {
      if (value.equals("PREFIX")) {
        return PREFIX;
      }
      if (value.equals("POSTFIX")) {
        return POSTFIX;
      }
      if (value.equals("INFIX")) {
        return INFIX;
      }
      if (value.equals("NOFIX")) {
        return NOFIX;
      }
      throw new IllegalArgumentException();
    }
  }
}
