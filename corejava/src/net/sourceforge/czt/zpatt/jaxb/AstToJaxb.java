
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstToJaxb.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.zpatt.jaxb;

import java.util.*;
import java.util.logging.Logger;

import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.base.ast.Term;

import net.sourceforge.czt.z.jaxb.gen.*;
import net.sourceforge.czt.zpatt.jaxb.gen.*;
import org.w3._2001.xmlschema.*;

/**
 * The marshaller responsible for serializing XML data.
 *
 * @author Gnast version 0.1
 */
public class AstToJaxb
  extends net.sourceforge.czt.z.jaxb.AstToJaxb
  implements net.sourceforge.czt.zpatt.visitor.ZpattVisitor,
             net.sourceforge.czt.base.visitor.TermVisitor
{

  /**
   * The ObjectFactory instances for generating Jaxb objects.
   */
  private net.sourceforge.czt.zpatt.jaxb.gen.ObjectFactory
    objectFactory_ = new net.sourceforge.czt.zpatt.jaxb.gen.ObjectFactory();
  private net.sourceforge.czt.z.jaxb.gen.ObjectFactory
    annsObjectFactory_ = new net.sourceforge.czt.z.jaxb.gen.ObjectFactory();
  private org.w3._2001.xmlschema.ObjectFactory
    anyTypeObjectFactory_ = new org.w3._2001.xmlschema.ObjectFactory();

  /**
   * A map that maps id's to the corresponding Object.
   */
  private Map hash_ = new HashMap();

  private String getClassName()
  {
    return "net.sourceforge.czt.zpatt.jaxb.AstToJaxb";
  }

  private Logger getLogger()
  {
    return Logger.getLogger(getClassName());
  }

  public Object visitTerm(Term zedObject)
  {
    throw(new UnsupportedOperationException("Unexpected element "
                                            + zedObject.getClass().getName()));
  }


  public Object visitPredTransform(net.sourceforge.czt.zpatt.ast.PredTransform zedObject)
  {
    getLogger().entering(getClassName(), "visitPredTransform", zedObject);

    PredTransform jaxbObject = null;
    try {
      jaxbObject = objectFactory_.createPredTransformElement();
      if (!createElement_) {
        jaxbObject = objectFactory_.createPredTransform();
      }
      createElement_ = true;
      if (zedObject.getLeftPred() != null) {
        Term term = zedObject.getLeftPred();
        jaxbObject.setLeftPred((Pred) term.accept(this));
      }
      createElement_ = true;
      if (zedObject.getRightPred() != null) {
        Term term = zedObject.getRightPred();
        jaxbObject.setRightPred((Expr) term.accept(this));
      }
    }
    catch (Exception exception) {
      String message =
        "class AstToJaxb: "
        + "Cannot transform a PredTransform to the corresponding "
        + "Jaxb class";
      throw new CztException(message, exception);
    }

    getLogger().exiting(getClassName(), "visitPredTransform", jaxbObject);
    createElement_ = true;
    return jaxbObject;
  }

  public Object visitJokerExpr(net.sourceforge.czt.zpatt.ast.JokerExpr zedObject)
  {
    getLogger().entering(getClassName(), "visitJokerExpr", zedObject);

    JokerExpr jaxbObject = null;
    try {
      jaxbObject = objectFactory_.createJokerExprElement();
      if (!createElement_) {
        jaxbObject = objectFactory_.createJokerExpr();
      }
      createElement_ = false;
      if (zedObject.getName() != null) {
        jaxbObject.setName(zedObject.getName());
      }
    }
    catch (Exception exception) {
      String message =
        "class AstToJaxb: "
        + "Cannot transform a JokerExpr to the corresponding "
        + "Jaxb class";
      throw new CztException(message, exception);
    }

    getLogger().exiting(getClassName(), "visitJokerExpr", jaxbObject);
    createElement_ = true;
    return jaxbObject;
  }

  public Object visitJokerPred(net.sourceforge.czt.zpatt.ast.JokerPred zedObject)
  {
    getLogger().entering(getClassName(), "visitJokerPred", zedObject);

    JokerPred jaxbObject = null;
    try {
      jaxbObject = objectFactory_.createJokerPredElement();
      if (!createElement_) {
        jaxbObject = objectFactory_.createJokerPred();
      }
      createElement_ = false;
      if (zedObject.getName() != null) {
        jaxbObject.setName(zedObject.getName());
      }
    }
    catch (Exception exception) {
      String message =
        "class AstToJaxb: "
        + "Cannot transform a JokerPred to the corresponding "
        + "Jaxb class";
      throw new CztException(message, exception);
    }

    getLogger().exiting(getClassName(), "visitJokerPred", jaxbObject);
    createElement_ = true;
    return jaxbObject;
  }

  public Object visitExprTransform(net.sourceforge.czt.zpatt.ast.ExprTransform zedObject)
  {
    getLogger().entering(getClassName(), "visitExprTransform", zedObject);

    ExprTransform jaxbObject = null;
    try {
      jaxbObject = objectFactory_.createExprTransformElement();
      if (!createElement_) {
        jaxbObject = objectFactory_.createExprTransform();
      }
      createElement_ = true;
      if (zedObject.getLeftExpr() != null) {
        Term term = zedObject.getLeftExpr();
        jaxbObject.setLeftExpr((Expr) term.accept(this));
      }
      createElement_ = true;
      if (zedObject.getRightExpr() != null) {
        Term term = zedObject.getRightExpr();
        jaxbObject.setRightExpr((Expr) term.accept(this));
      }
    }
    catch (Exception exception) {
      String message =
        "class AstToJaxb: "
        + "Cannot transform a ExprTransform to the corresponding "
        + "Jaxb class";
      throw new CztException(message, exception);
    }

    getLogger().exiting(getClassName(), "visitExprTransform", jaxbObject);
    createElement_ = true;
    return jaxbObject;
  }

  public Object visitTransformList(net.sourceforge.czt.zpatt.ast.TransformList zedObject)
  {
    getLogger().entering(getClassName(), "visitTransformList", zedObject);

    TransformList jaxbObject = null;
    try {
      jaxbObject = objectFactory_.createTransformListElement();
      if (!createElement_) {
        jaxbObject = objectFactory_.createTransformList();
      }
      {
        List list = zedObject.getTransform();
        List newlist = jaxbObject.getTransform();
        for (Iterator iter = list.iterator(); iter.hasNext();) {
          Object o = iter.next();
          if (o instanceof Term) {
            createElement_ = true;
            o = ((Term) o).accept(this);
          }
          newlist.add(o);
        }
      }
    }
    catch (Exception exception) {
      String message =
        "class AstToJaxb: "
        + "Cannot transform a TransformList to the corresponding "
        + "Jaxb class";
      throw new CztException(message, exception);
    }

    getLogger().exiting(getClassName(), "visitTransformList", jaxbObject);
    createElement_ = true;
    return jaxbObject;
  }
}
