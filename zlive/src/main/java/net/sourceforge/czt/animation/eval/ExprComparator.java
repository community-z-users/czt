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

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;

import net.sourceforge.czt.animation.eval.flatpred.FlatGivenSet;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.GivenValue;
import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.Branch;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.TupleExpr;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZExprList;
import net.sourceforge.czt.z.util.PrintVisitor;

/** A comparator for evaluated Z expressions.
 *  The compare method defines a total order over evaluated Z expressions,
 *  such that the inferred equivalence relation is semantic equality
 *  of the Z expressions.  This class uses the singleton pattern,
 *  so use the create() method to get an instance.
 *  
 *  TODO: handle members of given types.
 *  
 *  TODO: allow infinite sets to be compared against finite ones.
 * 
 * @author marku
 */
public class ExprComparator implements Comparator<Expr>, Serializable
{
  private static final long serialVersionUID = -593644926294937817L;
  
  private static final int NUMEXPR = 1;
  private static final int GIVENVALUE = 2;
  private static final int GIVENSET = 3;
  private static final int FREETYPE0 = 4; // a branch with no expression
  private static final int FREETYPE1 = 5; // a branch with an expression
  private static final int TUPLEEXPR = 6;
  private static final int BINDEXPR = 7;
  private static final int SETEXPR = 8;

  public static final int LESSTHAN = -1;
  public static final int EQUAL = 0;
  public static final int GREATERTHAN = 1;

  private static ExprComparator singleton_ = new ExprComparator();
  
  public static ExprComparator create()
  {
    return singleton_;
  }

  /** Use createComparator() to get an instance. */
  private ExprComparator()
  {
  }

  /** A comparator that compares just the name part of ConstDecls.
   *  This is useful for sorting lists of ConstDecl objects.
   */
  private static class ConstDeclComparator
  implements Comparator<ConstDecl>, Serializable
  {
    private static final long serialVersionUID = -7118907591680743993L;

    public int compare(ConstDecl cdecl0, ConstDecl cdecl1)
    {
      PrintVisitor printVisitor = new PrintVisitor(false);
      String name0 = cdecl0.getZName().accept(printVisitor);
      String name1 = cdecl1.getZName().accept(printVisitor);
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

  /** A convenience method that checks equality according to Z semantics.
   *  It is equivalent to create().compare(e1,e2) == 0.
   *
   * @param e1  An evaluated expression, such as an EvalSet
   * @param e2  Another evaluated expression.
   * @return true iff e1 and e2 are semantically equal.
   */
  public static boolean equalZ(Expr e1, Expr e2)
  {
    return singleton_.compare(e1,e2) == 0;
  }

  /* This orders evaluated ZLive expressions.
   * @throws RuntimeException if it sees an unknown/non-evaluated Expr.
   * @see java.util.Comparator#compare(T, T)
   */
  public int compare(Expr arg0, Expr arg1)
  {
    PrintVisitor printVisitor = new PrintVisitor(false);
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

        case GIVENVALUE:
          String given0 = ((GivenValue)arg0).getValue();
          String given1 = ((GivenValue)arg1).getValue();
          result = sign(given0.compareTo(given1));
          break;

        case GIVENSET:
          String givenset0 = ((FlatGivenSet)arg0).getName();
          String givenset1 = ((FlatGivenSet)arg1).getName();
          result = sign(givenset0.compareTo(givenset1));
          break;
          
        case FREETYPE0:
        case FREETYPE1:
          Branch free0 = (Branch)arg0;
          Branch free1 = (Branch)arg1;
          String name0 = free0.getZName().accept(printVisitor);
          String name1 = free1.getZName().accept(printVisitor);
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
              String n0 = binding0.get(i).getZName().accept(printVisitor);
              String n1 = binding1.get(i).getZName().accept(printVisitor);
              result = sign(n0.compareTo(n1));
            }
            
            // compare all the values
            for (int i=0; result==EQUAL && i<size; i++)
              result = compare(binding0.get(i).getExpr(),
                               binding1.get(i).getExpr());
          }
          break;

        case SETEXPR:
          EvalSet set0 = (EvalSet)arg0;
          EvalSet set1 = (EvalSet)arg1;
          //          System.out.println("Compare: set sizes "+set0.size()+", "+set1.size());
          result = sign(set0.size() - set1.size());
          if (result == EQUAL) {
            Iterator<Expr> members0 = set0.sortedIterator();
            Iterator<Expr> members1 = set1.sortedIterator();
            while (result == EQUAL && members0.hasNext()) {
              assert members1.hasNext();
              Expr mem0 = members0.next();
              Expr mem1 = members1.next();
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
    if (e instanceof GivenValue)
      return GIVENVALUE;
    if (e instanceof FlatGivenSet)
      return GIVENSET;
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
