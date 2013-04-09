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
   * The string representation of this operator name as it is used
   * within the AST classes and without strokes.
   * For instance, " _ + _ ".
   */
  private String word_;

  /**
   * The list of decorations of this operator name.
   */
  private StrokeList strokes_ = null;

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
  public OperatorName(String name, StrokeList strokes)
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
  public OperatorName(ZName name)
    throws OperatorNameException
  {
    this(name.getWord(), name.getStrokeList());
  }

  /**
   * Create some operator name from a single operator word.
   *
   * @param name a name that does not contain decorations.
   * @param strokes the strokes of this operator name
   *                (can be <code>null</code>).
   * @param fixity must be INFIX, PREFIX, or POSTFIX.
   * @throws net.sourceforge.czt.z.util.OperatorName.OperatorNameException
   */
  public OperatorName(String name, StrokeList strokes, Fixity fixity)
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

  public String getWord()
  {
    return word_;
  }

  public StrokeList getStrokes()
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

  public boolean isPostfix()
  {
    return Fixity.POSTFIX.equals(getFixity());
  }

  public boolean isPrefix()
  {
    return Fixity.PREFIX.equals(getFixity());
  }

  public boolean isInfix()
  {
    return Fixity.INFIX.equals(getFixity());
  }

  public String[] getWords()
  {
    return list_.toArray(new String[0]);
  }

  @Override
  public String toString()
  {
    return getWord();
  }

 public static class OperatorNameException
    extends Exception
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -5904605602162932380L;

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
}
