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

import net.sourceforge.czt.z2b.*;


/**
 * This class provides static utility functions for creating Z AST terms.
 *
 * @author Mark Utting
 */
public class Create
{
  private static ZFactory factory_ 
      = new net.sourceforge.czt.z.impl.ZFactoryImpl();

  /** Set the factory that is used to create various AST terms. */
  public static void setFactory(ZFactory factory) {
    factory_ = factory;
  }


  /** Create a simple AndPred.
   *  If either argument is null, it is ignored.
   */
  public static Pred andPred(Pred p1, Pred p2) {
    if (p1 == null)
      return p2;
    if (p2 == null)
      return p1;
    return factory_.createAndPred(p1,p2,Op.And);
  }

  /** Create an ImpliesPred
   */
  public static Pred impliesPred(Pred p1, Pred p2) {
    return factory_.createImpliesPred(p1,p2);
  }

  /** Create an equality between a name and expression */
  public static Pred eqPred(Name n, Expr e) {
    RefName eq = factory_.createRefName();
    eq.setWord("=");
    // TODO: it would be nice to do eq.setDeclName(defn of equality)
    return factory_.createMemPred(pair(refExpr(n),e), 
				  refExpr(eq), 
				  Boolean.TRUE);
  }

  /** Create a MemPred for a name and expression */
  public static Pred memPred(Name n, Expr e) {
    return factory_.createMemPred(refExpr(n), e, Boolean.FALSE);
  }

  /** Creates a Pair */
  public static TupleExpr pair(Expr left, Expr right) {
    TupleExpr pair = factory_.createTupleExpr();
    pair.getExpr().add(left);
    pair.getExpr().add(right);
    return pair;
  }

  /** Creates a RefExpr to a given Name */
  public static RefExpr refExpr(Name n) {
    DeclName decl = null;
    if (n instanceof DeclName)
      decl = (DeclName)n;
    RefName ref = factory_.createRefName(n.getWord(), n.getStroke(), decl);
    RefExpr e = factory_.createRefExpr(ref, new ArrayList(), Boolean.FALSE);
    return e;
  }
}

