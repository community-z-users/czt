/**
Copyright 2003 Mark Utting
This file is part of the CZT project.

The CZT project contains free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 2 of the License, or
(at your option) any later version.

The CZT project is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with CZT; if not, write to the Free Software
Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/
package net.sourceforge.czt.z2b;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;

import net.sourceforge.czt.z2b.*;


/**
 * This class provides a factory for creating Z AST terms.
 *
 * @author Mark Utting
 */
public class Create
{
  private static Factory factory_ 
    = new Factory();

  /** Set the factory that is used to create various AST terms. */
  public static void setFactory(ZFactory factory) {
    factory_ = new Factory(factory);
  }

  /** Returns the factory that is used to create various AST terms. */
  public static Factory getFactory() {
    return factory_;
  }

  /** Create a simple AndPred.
   *  If either argument is null, it is ignored.
   */
  public static Pred andPred(Pred p1, Pred p2) {
    if (p1 == null)
      return p2;
    if (p2 == null)
      return p1;
    return factory_.createAndPred(p1,p2,And.Wedge);
  }

  /** Create an equality between a name and expression */
  public static Pred eqPred(ZDeclName n, Expr e) {
    ZRefName eq = factory_.createZRefName();
    eq.setWord("=");
    // TODO: it would be nice to do eq.setDeclName(defn of equality)
    return factory_.createMemPred(factory_.createTupleExpr(refExpr(n), e), 
				  refExpr(eq), 
				  Boolean.TRUE);
  }
  public static Pred eqPred(ZRefName n, Expr e) {
    ZRefName eq = factory_.createZRefName();
    eq.setWord("=");
    // TODO: it would be nice to do eq.setDeclName(defn of equality)
    return factory_.createMemPred(factory_.createTupleExpr(refExpr(n), e), 
				  refExpr(eq), 
				  Boolean.TRUE);
  }

  /** Creates a RefName from a String */
  public static ZRefName refName(String name) {
    // TODO: this could/should strip decorations off name and
    //        put them into the Stroke list.
    return factory_.createZRefName(name, new ArrayList(), null);
  }

  /** Creates a RefName to a given Name (which may be any kind of Name) */
  public static ZRefName refName(ZRefName n) {
    return factory_.createZRefName(n.getWord(), n.getStroke(), n.getDecl());
  }
  public static ZRefName refName(ZDeclName n) {
    return factory_.createZRefName(n.getWord(), n.getStroke(), n);
  }

  /** Creates a RefExpr to a given Name */
  public static RefExpr refExpr(ZDeclName n) {
    ZExprList zExprList = factory_.createZExprList();
    return factory_.createRefExpr(refName(n), zExprList, Boolean.FALSE);
  }
  public static RefExpr refExpr(ZRefName n) {
    ZExprList zExprList = factory_.createZExprList();
    return factory_.createRefExpr(refName(n), zExprList, Boolean.FALSE);
  }


  /** Prime a Name */
  public static ZRefName prime(String name) {
    ZRefName n2 = Create.refName(name);
    n2.getStroke().add(factory_.createNextStroke());
    return n2;
  }
}
