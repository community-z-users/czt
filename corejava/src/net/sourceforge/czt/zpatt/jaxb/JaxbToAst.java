
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

Copyright 2003 Mark Utting
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

package net.sourceforge.czt.zpatt.jaxb;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.util.ReflectiveVisitor;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.z.ast.*;

/**
 * The unmarshaller responsible for deserializing XML data.
 *
 * @author Gnast version 0.1
 */
public class JaxbToAst extends net.sourceforge.czt.z.jaxb.JaxbToAst
{
  protected ZpattFactory mZpattFactory_;

  public JaxbToAst()
  {
    mZpattFactory_ =
      new net.sourceforge.czt.zpatt.impl.ZpattFactoryImpl();
  }

  public JaxbToAst(net.sourceforge.czt.z.ast.ZFactory vZFactory, ZpattFactory vZpattFactory)
  {
    super(vZFactory);
    mZpattFactory_ = vZpattFactory;
  }

  private static Logger getLogger()
  {
    return Logger.getLogger("net.sourceforge.czt.zpatt.jaxb.JaxbToAst");
  }

  public Object visitObject(Object object)
  {
    getLogger().fine("Visit " + object.getClass().toString());
    if (object instanceof String
        || object instanceof Boolean
        || object instanceof List
        || object instanceof Integer
        || object instanceof java.math.BigInteger) {
      return object;
    }
    throw new UnsupportedOperationException("Unexpected element "
                                            + object.getClass().getName());
  }

  public Object visitJokerExpr(net.sourceforge.czt.zpatt.jaxb.gen.JokerExpr jaxbObject)
  {
    getLogger().entering("JaxbToAst", "visitJokerExpr", jaxbObject);
    String name =
      (String) dispatch(jaxbObject.getName());
    JokerExpr erg = mZpattFactory_.createJokerExpr(name);
    getLogger().exiting("JaxbToAst", "visitJokerExpr", erg);
    return erg;
  }

  public Object visitSubstitute(net.sourceforge.czt.zpatt.jaxb.gen.Substitute jaxbObject)
  {
    getLogger().entering("JaxbToAst", "visitSubstitute", jaxbObject);
    java.util.List expr = new java.util.Vector();
    for (Iterator iter = jaxbObject.getExpr().iterator(); iter.hasNext();) {
      Object obj = iter.next();
      Object o = dispatch(obj);
      expr.add(o);
    }
    java.util.List pred = new java.util.Vector();
    for (Iterator iter = jaxbObject.getPred().iterator(); iter.hasNext();) {
      Object obj = iter.next();
      Object o = dispatch(obj);
      pred.add(o);
    }
    Substitute erg = mZpattFactory_.createSubstitute(expr, pred);
    getLogger().exiting("JaxbToAst", "visitSubstitute", erg);
    return erg;
  }

  public Object visitJokerPred(net.sourceforge.czt.zpatt.jaxb.gen.JokerPred jaxbObject)
  {
    getLogger().entering("JaxbToAst", "visitJokerPred", jaxbObject);
    String name =
      (String) dispatch(jaxbObject.getName());
    JokerPred erg = mZpattFactory_.createJokerPred(name);
    getLogger().exiting("JaxbToAst", "visitJokerPred", erg);
    return erg;
  }

  public Object visitSubstList(net.sourceforge.czt.zpatt.jaxb.gen.SubstList jaxbObject)
  {
    getLogger().entering("JaxbToAst", "visitSubstList", jaxbObject);
    java.util.List substitute = new java.util.Vector();
    for (Iterator iter = jaxbObject.getSubstitute().iterator(); iter.hasNext();) {
      Object obj = iter.next();
      Object o = dispatch(obj);
      substitute.add(o);
    }
    SubstList erg = mZpattFactory_.createSubstList(substitute);
    getLogger().exiting("JaxbToAst", "visitSubstList", erg);
    return erg;
  }
}
