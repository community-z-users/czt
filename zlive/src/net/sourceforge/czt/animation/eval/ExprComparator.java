/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2006 Mark Utting

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
package net.sourceforge.czt.animation.eval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;

/** A comparator for evaluated Z expressions.
 *  The compare method defines a total order over evaluated Z expressions,
 *  such that the inferred equivalence relation is semantic equality
 *  of the Z expressions.
 * 
 * @author marku
 */
public class ExprComparator implements Comparator<Expr>
{
  // TODO: handle members of given types
  private static final int NUMEXPR = 1;
  private static final int FREETYPE0 = 2; // a branch with no expression
  private static final int FREETYPE1 = 3; // a branch with an expression
  private static final int TUPLEEXPR = 4;
  private static final int BINDEXPR = 5;
  private static final int SETEXPR = 6;

  public static final int LESSTHAN = -1;
  public static final int EQUAL = 0;
  public static final int GREATERTHAN = 1;

  /** A comparator that compares just the name part of ConstDecls.
   *  This is useful for sorting lists of ConstDecl objects.
   */
  private static class ConstDeclComparator implements Comparator<ConstDecl>
  {
    public int compare(ConstDecl cdecl0, ConstDecl cdecl1)
    {
      String name0 = cdecl0.getZDeclName().toString();
      String name1 = cdecl1.getZDeclName().toString();
      return name0.compareTo(name1);
    }
  }
  
  private static ConstDeclComparator constDeclSorter = new ConstDeclComparator();

  /** Converts an integer difference into -1, 0, or +1. */
  public int sign(int difference)
  {
    if (difference < 0)
      return LESSTHAN;
    if (difference > 0)
      return GREATERTHAN;
    return EQUAL;
  }

  /* This orders evaluated ZLive expressions.
   * @throws RuntimeException if 
   * @see java.util.Comparator#compare(T, T)
   */
  public int compare(Expr arg0, Expr arg1)
  {
    int type0 = exprType(arg0);
    int type1 = exprType(arg1);
    int result = sign(type0 - type1);
    if (result == EQUAL) {
      switch (type0) {
        case NUMEXPR:
          NumExpr num0 = (NumExpr)arg0;
          NumExpr num1 = (NumExpr)arg1;
          result = sign(num0.getValue().compareTo(num1.getValue()));
          break;

        case FREETYPE0:
        case FREETYPE1:
          Branch free0 = (Branch)arg0;
          Branch free1 = (Branch)arg1;
          String name0 = free0.getZDeclName().toString();
          String name1 = free1.getZDeclName().toString();
          result = sign(name0.compareTo(name1));
          if (result == EQUAL && type0 == FREETYPE1)
            result = compare(free0.getExpr(), free1.getExpr());
          break;

        case TUPLEEXPR:
          ZExprList tuple0 = ((TupleExpr)arg0).getZExprList();
          ZExprList tuple1 = ((TupleExpr)arg1).getZExprList();
          result = sign(tuple0.size() - tuple1.size());
          if (result == EQUAL) {
            int size = tuple0.size();
            for (int i=0; result==EQUAL && i<size; i++)
              result = compare(tuple0.get(i), tuple1.get(i));
          }
          break;

        case BINDEXPR:
          ZDeclList decls0 = ((BindExpr)arg0).getZDeclList();
          ZDeclList decls1 = ((BindExpr)arg1).getZDeclList();
          result = sign(decls0.size() - decls1.size());
          if (result == EQUAL) {
            // sort the names, then compare them one by one.
            int size = decls0.size();
            List<ConstDecl> binding0 = new ArrayList<ConstDecl>(size);
            List<ConstDecl> binding1 = new ArrayList<ConstDecl>(size);
            for (int i=0; i<size; i++) {
              binding0.add((ConstDecl)decls0.get(i));
              binding1.add((ConstDecl)decls1.get(i));
            }
            Collections.sort(binding0, constDeclSorter);
            Collections.sort(binding1, constDeclSorter);
            
            // compare all the names
            for (int i=0; result==EQUAL && i<size; i++) {
              String n0 = binding0.get(i).getZDeclName().toString();
              String n1 = binding1.get(i).getZDeclName().toString();
              result = sign(n0.compareTo(n1));
            }
            
            // compare all the values
            for (int i=0; result==EQUAL && i<size; i++)
              result = compare(binding0.get(i).getExpr(), binding1.get(i).getExpr());
          }
          break;

        case SETEXPR:
          EvalSet set0 = (EvalSet)arg0;
          EvalSet set1 = (EvalSet)arg1;
          System.out.println("set compare: "+set0+", "+set1);
          result = sign(set0.size() - set1.size());
          if (result == EQUAL) {
            Iterator<Expr> members0 = set0.iterator();
            Iterator<Expr> members1 = set1.iterator();
            while (result == EQUAL && members0.hasNext()) {
              assert members1.hasNext();
              Expr mem0 = members0.next();
              Expr mem1 = members1.next();
              System.out.println("set compare members: "+mem0+", "+mem1);
              result = compare(mem0, mem1);
            }
            assert members0.hasNext() == members1.hasNext();
          }
          break;

        default:
          throw new RuntimeException("Unknown expr type "+type0);
      }
    }
    return result;
  }

  /** Maps evaluated expressions into equivalence classes.
   *  This is used to order expressions, from simplest to more complex.
   *  It must also respect the semantics of Z equality.
   *  For example, this means that all kinds of sets must be in the
   *  same equivalence class, even if they have different implementations.
   *
   * @throws RuntimeException if it e is an unknown kind of
   *  Expr to ZLive, or if it is not fully evaluated.
   *
   * @param e The expression to classify.
   * @return  The (non-negative) equivalence class of the expression.
   */
  public static int exprType(Object e)
  {
    if (e instanceof NumExpr)
      return NUMEXPR;
    if (e instanceof Branch) {
      if (((Branch)e).getExpr() == null)
        return FREETYPE0;
      else
        return FREETYPE1;
    }
    if (e instanceof TupleExpr)
      return TUPLEEXPR;
    if (e instanceof BindExpr)
      return BINDEXPR;
    if (e instanceof EvalSet)
      return SETEXPR;
    throw new RuntimeException("Unknown/unevaluated expr type: "+e.getClass());
  }
}
