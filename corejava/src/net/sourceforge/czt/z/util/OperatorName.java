/**
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

package net.sourceforge.czt.z.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

/**
 * Responsible for transforming opnames to and from strings.
 */
public class OperatorName
{
  private static Factory factory_ = new Factory();

  /**
   * The string representation for this operator name,
   * without strokes.  For instance, " _ + _ ".
   */
  private String word_;

  /**
   * A list of String like, for instance, ["_", "+", "_"].
   */
  private List list_ = new ArrayList();

  /**
   * A list of Stroke.
   */
  private List strokes_ = null;

  public static void setFactory(Factory factory)
  {
    if (factory != null) {
      factory_ = factory;
    }
    else {
      throw new NullPointerException();
    }
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
      list_ = wordToList(word_);
      strokes_ = strokes;
    }
    else if (Fixity.PREFIX.equals(fixity)) {
      word_ = name + ZString.ARG_TOK;
      list_ = wordToList(word_);
      strokes_ = strokes;
    }
    else if (Fixity.POSTFIX.equals(fixity)) {
      word_ = ZString.ARG_TOK + name;
      list_ = wordToList(word_);
      strokes_ = strokes;
    }
    else throw new UnsupportedOperationException();
  }

  public OperatorName(Name name)
    throws OperatorNameException
  {
    this(name.getWord(), name.getStroke());
  }

  /**
   *
   * @param name a name that does not contain decorations.
   */
  public OperatorName(String name, List strokes)
    throws OperatorNameException
  {
    word_ = name;
    list_ = wordToList(name);
    strokes_ = strokes;
  }

  private List wordToList(String name)
    throws OperatorNameException
  {
    List result = new ArrayList();
    String[] split = name.split(ZString.OP_SEPARATOR);
    for (int i = 0; i < split.length; i++) {
      if (split[i] != null && ! split[i].equals("")) {
        String opPart = split[i];
        if (opPart.equals(ZString.ARG) || opPart.equals(ZString.LISTARG)) {
          result.add(split[i]);
        }
        else {
          DeclName declName = factory_.createDeclName(opPart);
          result.add(declName.getWord());
          checkStrokes(declName.getStroke());
        }
      }
    }
    if (result.size() <= 1) {
      throw new OperatorNameException(name + " is not an operator name.");
    }
    return result;
  }

  public OperatorName(List list)
    throws OperatorNameException
  {
    if (list.size() <= 1) {
      throw new OperatorNameException(list + " is not an operator name.");
    }
    list_ = list;
    StringBuffer name = new StringBuffer();
    for (Iterator iter = list.iterator(); iter.hasNext(); ) {
      String opPart = (String) iter.next();
      if (opPart.equals(ZString.ARG) ||
          opPart.equals(ZString.ARG_TOK)) {
        name.append(ZString.ARG_TOK);
      }
      else if (opPart.equals(ZString.LISTARG) ||
               opPart.equals(ZString.LISTARG_TOK)) {
        name.append(ZString.LISTARG_TOK);
      }
      else {
        DeclName declName = factory_.createDeclName(opPart);
        name.append(declName.getWord());
        checkStrokes(declName.getStroke());
      }
    }
    word_ = name.toString();
  }

  private void checkStrokes(List strokes)
    throws OperatorNameException
  {
    if (strokes_ == null) {
      strokes_ = strokes;
    }
    else if (! strokes_.equals(strokes)) {
      final String message =
        "The component names of an operator must have the " +
        "same decorations.";
      throw new OperatorNameException(message);
    }
  }

  public String getName()
  {
    return word_;
  }

  public List getStroke()
  {
    return strokes_;
  }

  /**
   * Returns whether the given string is an operator name.
   * More precisely, this method checks whether the given string
   * contains an OP_SEPARATOR.
   */
  public static boolean isOperatorName(String name)
  {
    for (int i = 0; i < name.length(); i++) {
      if (ZString.OP_SEPARATOR.equals(String.valueOf(name.charAt(i)))) {
        return true;
      }
    }
    return false;
  }

  /**
   * Checks whether this operator is unary.
   * More precisely, this method checks whether this operator contains
   * exactly one ARG or LISTARG.
   *
   * @czt.todo This method can be implemented in a more efficient way.
   */
  public boolean isUnary()
  {
    if (list_.size() < 2) {
      final String message =
        "A list of size smaller than two cannot occur in operator names.";
      throw new CztException(message);
    }
    final String ARG = ZString.ARG;
    final String LISTARG = ZString.LISTARG;
    final String first = (String) list_.get(0);
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
    final String first = (String) list_.get(0);
    final String last = (String) list_.get(list_.size() - 1);
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

  public String toString()
  {
    return getName();
  }

  /**
   * OperatorName(" _ + _ ") is translated into ["_", "+", "_"].
   */
  public Iterator iterator()
  {
    return list_.iterator();
  }

  public class OperatorNameException
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
