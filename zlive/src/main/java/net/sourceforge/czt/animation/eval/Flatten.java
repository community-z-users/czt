/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
// TODO: change pred methods to be type void.
package net.sourceforge.czt.animation.eval;

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.czt.animation.eval.flatpred.FlatPredList;
import net.sourceforge.czt.base.util.UnsupportedAstClassException;
import net.sourceforge.czt.parser.util.DefinitionTable;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.InclDecl;
import net.sourceforge.czt.z.ast.Name;
import net.sourceforge.czt.z.ast.NameTypePair;
import net.sourceforge.czt.z.ast.PowerType;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.SchemaType;
import net.sourceforge.czt.z.ast.Signature;
import net.sourceforge.czt.z.ast.Type;
import net.sourceforge.czt.z.ast.TypeAnn;
import net.sourceforge.czt.z.ast.VarDecl;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/** Flattens a Pred/Expr term into a list of FlatPred objects.
 *  The visit* methods add subclasses of Pred or Expr into the list flat_.
 *  Each visit*Expr method returns a Name, which is the name of the
 *  variable that will contain the result of the expression after evaulation.
 *  Each visit*Pred method returns null.
 *  <p>
 *  The ZLive parameter to the constructor is used to access the
 *  section manager (to get the current context of the expr/pred).
 */
public class Flatten
{
  /** A reference to the main animator object, so that we can
      access all kinds of settings, tables and section manager etc.
  */
  private ZLive zlive_;

  public Flatten(ZLive zlive)
  {
    zlive_ = zlive;
  }

  /** Flattens the toFlatten predicate into a list of FlatPred predicates.
   *  @param  toFlatten The Pred to flatten.
   *  @param  destination Generated FlatPred objects are appended to this list.
   */
  public void flattenPred(Pred toFlatten, FlatPredList destination)
    throws CommandException
  {
    String currSect = zlive_.getCurrentSection();
    Key<DefinitionTable> key = new Key<DefinitionTable>(currSect, DefinitionTable.class);
    DefinitionTable table = zlive_.getSectionManager().get(key);
    FlattenVisitor visitor = new FlattenVisitor(zlive_, destination, table);
    toFlatten.accept(visitor);
  }

  /** Flattens the toFlatten expression into a list of FlatPred predicates.
   *  @param  toFlatten An Expr to flatten.
   *  @param  destination Generated FlatPred objects are appended to this list.
   *  @return The name of the variable that will contain the result,
   *          after evaluation.
   */
  public ZName flattenExpr(Expr toFlatten, FlatPredList destination)
    throws CommandException
  {
    String currSect = zlive_.getCurrentSection();
    Key<DefinitionTable> key = new Key<DefinitionTable>(currSect, DefinitionTable.class);
    DefinitionTable table = zlive_.getSectionManager().get(key);
    FlattenVisitor visitor = new FlattenVisitor(zlive_, destination, table);
    return toFlatten.accept(visitor);
  }

  /** Constructs a characteristic tuple.
   *  TODO: make this handle schemas etc. properly.
   *
   * @param decls  List of declarations.
   * @return       The characteristic tuple.
   */
  public static Expr charTuple(Factory factory, List<Decl> decls)
  {
    Expr expr = null;
    List<ZName> names = declNames(decls);
    if (names.size() == 0)
      throw new EvalException("empty set comprehension!");
    else if (names.size() == 1) {
      ZName refName = factory.createZName(names.get(0));
      expr = factory.createRefExpr(refName);
    }
    else {
      // Make a real tuple!
      ZExprList refExprs = factory.createZExprList();
      for (ZName name : names) {
        ZName tmpName = factory.createZName(name);
        refExprs.add(factory.createRefExpr(tmpName));
      }
      expr = factory.createTupleExpr(refExprs);
    }
    return expr;
  }

  /** An auxiliary method for getting all the names in a list of Decl. */
  public static List<ZName> declNames(List<Decl> decls) {
    List<ZName> result = new ArrayList<ZName>();
    for (Decl decl : decls) {
      if (decl instanceof VarDecl) {
        VarDecl vdecl = (VarDecl) decl;
        for (Name name : vdecl.getName()) {
          if (name instanceof ZName)
            result.add((ZName)name);
          else
            throw new UnsupportedAstClassException("illegal Name " + name);
        }
      }
      else if (decl instanceof ConstDecl) {
        ConstDecl cdecl = (ConstDecl) decl;
        ZName name = cdecl.getZName();
        result.add(name);
      }
      else if (decl instanceof InclDecl) {
        InclDecl inclDecl = (InclDecl) decl;
        TypeAnn typeAnn = (TypeAnn) inclDecl.getExpr().getAnn(TypeAnn.class);
        Type type = typeAnn.getType();
        type = ((PowerType) type).getType();
        Signature sig = ((SchemaType) type).getSignature();
        for (NameTypePair nameType : sig.getNameTypePair()) {
          ZName name = (ZName) nameType.getName();
          result.add(name);
        }
      }
      else {
        throw new EvalException("Unknown kind of Decl: " + decl);
      }
    }
    return result;
  }
}

