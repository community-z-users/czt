/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

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

package net.sourceforge.czt.animation.gui.temp;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import net.sourceforge.czt.z.ast.BindExpr;
import net.sourceforge.czt.z.ast.ConstDecl;
import net.sourceforge.czt.z.ast.Decl;
import net.sourceforge.czt.z.ast.DeclList;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;

/**
 * Class representing Binding values in Z.
 */
public class ZBinding implements ZValue
{
  //private Map/*<String,ZValue>*/ binding_;
  private BindExpr expr_;

  private static Factory factory_;

  /**
   * Creates an empty binding.
   */
  public ZBinding()
  {
    //binding_ = new HashMap();
    factory_ = GaffeFactory.getFactory();
    expr_ = factory_.createBindExpr();
  }

  /**
   * Creates a binding from a <code>Map</code> from identifiers
   * (<code>String</code>) to values (<code>ZValue</code>).
   * @param binding The map to copy into the new binding.
   */
  public ZBinding(Map<String, ZValue> binding)
  {
    //binding_ = new HashMap(binding);
    factory_ = GaffeFactory.getFactory();
    expr_ = factory_.createBindExpr(this.mapToDeclList(binding));
  }

  /**
   * Create a binding from a expr
   * @param expr_ the BindExpr used to created the binding.
   */
  public ZBinding(BindExpr expr)
  {
    this.expr_ = expr;
  }

  /**
   * Equivalent to <code>Map.keySet()</code>.
   * @return The set of keys in the binding.
   */
  public Set<String> keySet()
  {
    //return binding_.keySet();
    Set<String> result = new HashSet<String>();
    for (Decl decl : expr_.getZDeclList()) {
      result.add(((ConstDecl) decl).getName().toString());
    }
    return result;
  }

  /**
   * Given an identifier, gets a value from the binding.
   * @param location The name of the value to get from the binding.
   * @return The value.
   */
  public ZValue get(String location)
  {
    //return (ZValue) binding_.get(location);
    ZName target = factory_.createZName(location);
    try {
      for (Decl decl : expr_.getZDeclList()) {
        ConstDecl tempDecl = (ConstDecl) decl;
        if (tempDecl.getZName().equals(target)) {
          return GaffeFactory.zValue(tempDecl.getExpr());
        }
      }
      return null;
    } catch (UnexpectedTypeException ute) {
      ute.printStackTrace();
      return null;
    }
  }

  /**
   * Test if this binding is equal to a given object.
   * @param obj The object to compare against.
   * @return <code>true</code> if <code>obj</code> is a ZBinding with the same
   *         mappings from name to value.
   */
  public boolean equals(Object obj)
  {
    //return obj instanceof ZBinding && ((ZBinding) obj).binding_.equals(binding_);
    return expr_.equals(((ZValue) obj).getExpr());
  }

  /**
   * @return This object's hash code.
   */
  public int hashCode()
  {
    return expr_.hashCode();
  }

  /**
   * Convert this binding to a string.
   * @return A string representation of this binding.
   */
  public String toString()
  {
    //String str = "ZBinding: {\n";
    //for (Iterator it = binding_.keySet().iterator(); it.hasNext();) {
    //  String key = (String) it.next();
    //  str += key + ": " + binding_.get(key) + "\n";
    //}
    //str += "}";
    //return str;
    return expr_.toString();
  }

  /**
   * Get the expr type representing the zvalue
   * @return the representing expr
   */
  public BindExpr getExpr()
  {
    return expr_;
  }

  /**
   * Transfer a map to a DeclList
   * @param binding the map to be transfered to DeclList
   * @return delList to create BindExpr
   */
  protected DeclList mapToDeclList(Map<String, ZValue> binding)
  {
    ZDeclList result = factory_.createZDeclList();
    for (String s : binding.keySet()) {
      ZName name = factory_.createZName(s);
      ZValue zValue = binding.get(s);
      if (zValue != null) {
        result.add((Decl) factory_.createConstDecl(name, binding.get(s)
            .getExpr()));
      }
      else {
        result.add((Decl) factory_.createConstDecl(name, null));
      }
    }
    return result;
  }

}
