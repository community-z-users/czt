/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.zeves.util;

import java.net.InetAddress;
import java.net.UnknownHostException;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.RenameExpr;
import net.sourceforge.czt.z.ast.RenameList;
import net.sourceforge.czt.zeves.ast.InstantiationList;
import net.sourceforge.czt.zeves.ast.LabelAbility;
import net.sourceforge.czt.zeves.ast.LabelUsage;
import net.sourceforge.czt.zeves.ast.ZEvesLabel;
import net.sourceforge.czt.zeves.impl.ZEvesFactoryImpl;

/**
 *
 * @author Leo Freitas
 * @date Aug 4, 2011
 */
public final class ZEvesUtils
{

  private ZEvesUtils()
  {
  }

  public static final Factory FACTORY = createConsoleFactory();

  /**
   * Useful factory for debugging purposes. It prints ASCII names and
   * LocAnn offset by one in line/col count and no name IDs.
   * @return
   */
  public static Factory createConsoleFactory()
  {
    return createFactory(false, false, 1, 1);
  }

  /**
   * Create a factory tailored for either debugging or UI purposes. Various
   * parameters affect the base factory underlying print visitor's parameters.
   * @param printUnicode
   * @param printNameIds
   * @param printLocLineOffset
   * @param printLocColOffset
   * @return
   */
  public static Factory createFactory(boolean printUnicode, boolean printNameIds, int printLocLineOffset,
          int printLocColOffset)
  {
    // Make a factory that prints names in ASCII, not Unicode
    // (This is better for debugging and for console output).
    PrintVisitor printer = new PrintVisitor(printUnicode);
    printer.setPrintIds(printNameIds);
    printer.setOffset(printLocLineOffset, printLocColOffset);
    ZEvesFactoryImpl tmp = new ZEvesFactoryImpl();
    tmp.setToStringVisitor(printer);
    Factory result = new Factory(tmp);
    return result;
  }

  public static InstantiationList assertInstantiationList(Term term)
  {
    if (term instanceof InstantiationList)
    {
      return (InstantiationList) term;
    }
    final String message =
            "Expected a InstantiationList but found " + String.valueOf(term);
    throw new UnsupportedAstClassException(message);
  }

  public static InstantiationList assertRenameListAsInstantiationList(RenameExpr term)
  {
    RenameList result = term.getRenameList();
    if (result instanceof InstantiationList)
    {
      return (InstantiationList) result;
    }
    final String message = "Expected the Z/EVES instantiation list implementation of RenameList "
                           + " but found " + String.valueOf(result);
    throw new net.sourceforge.czt.base.util.UnsupportedAstClassException(message);
  }

  public static InstantiationList getInstantiationListFromExpr(Expr term)
  {
    InstantiationList result = null;
    if (term instanceof RenameExpr)
    {
      return assertRenameListAsInstantiationList((RenameExpr) term);
    }
    return result;
  }

  public static String getLocalHost()
  {
    try
    {
      return InetAddress.getLocalHost().getHostName();
    }
    catch (UnknownHostException e)
    {
      return "localhost";
    }
  }

  public static LabelAbility getDefaultAbility()
  {
    return LabelAbility.enabled;
  }

  public static LabelUsage getDefaultUsage()
  {
    return LabelUsage.none; 
  }

  public static ZEvesLabel getLabel(Term term)
  {
    ZEvesLabel result = null;
    //if (term instanceof Pred || term instanceof ConjPara)
    //{
    result = term.getAnn(ZEvesLabel.class);
    //}
    return result;
  }

  public static ZEvesLabel addDefaultZEvesLabelTo(Term term)
  {
    assert getLabel(term) == null : "adding default label for already labelled term " + term;
    String fromClsStr = term.getClass().getName();
    fromClsStr = fromClsStr.substring(fromClsStr.lastIndexOf(".")+1);
    // String thmName = fromClsStr + term.hashCode();
    // using just term.hashCode() sometimes gives a negative number, which Z/EVES does not accept
    // instead, go to unsigned Hex (as in Object.toString())
    String thmName = fromClsStr + Integer.toHexString(term.hashCode());
    ZEvesLabel label = FACTORY.createZEvesLabel(FACTORY.createZName(thmName), getDefaultAbility(), getDefaultUsage());
    term.getAnns().add(label);
    
    return label;
  }

  public static String getConcreteSyntaxSymbolShortDesc(ZEvesConcreteSyntaxSymbol sym)
  {
    StringBuilder rhs = new StringBuilder();
    rhs.append(sym.toString());
    ZEvesConcreteSyntaxSymbol other = sym.getOther();
    while (other != null)
    {
      other = other.getOther();
      rhs.append(" ");
      rhs.append(other.toString());
    }
    rhs.append(" ");
    rhs.append(sym.toString());
    return rhs.toString();
  }

  public static String getConcreteSyntaxSymbolLongDesc(ZEvesConcreteSyntaxSymbol sym)
  {
    StringBuilder rhs = new StringBuilder();
    rhs.append(sym.getDescription());
    ZEvesConcreteSyntaxSymbol other = sym.getOther();
    while (other != null)
    {
      other = other.getOther();
      rhs.append(" ");
      rhs.append(other.getDescription());
    }
    rhs.append(" ");
    rhs.append(sym.getDescription());
    return rhs.toString();
  }
}
