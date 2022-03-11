/*
  Copyright (C) 2005, 2006 Petra Malik
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

package net.sourceforge.czt.rules.codegen;

import org.apache.xerces.xs.XSComplexTypeDefinition;

public class JokerClass
{
//  /*@ non_null */
//  private XSComplexTypeDefinition typeDef_;

  /*@ non_null */
  private String name_;

  /*@ requires typeDef != null; */
  public JokerClass(XSComplexTypeDefinition typeDef)
  {
//    typeDef_ = typeDef;
    name_ = typeDef.getName();
  }

  public String getName()
  {
    return name_;
  }

  public String getClassName()
  {
    return "Prover" + name_;
  }

  public String getBindingName()
  {
    return name_ + "Binding";
  }

  public String getClassBindingName()
  {
    return "Prover" + name_ + "Binding";
  }

  public String getTypeName()
  {
    if (name_.equals("JokerName")) return "Name";
    String result = name_.substring(5, name_.length());
    if (result.endsWith("List")) {
      result = result.substring(0, result.length() - 4);
    }
    return result;
  }

  public boolean isList()
  {
    return name_.endsWith("List");
  }
}
