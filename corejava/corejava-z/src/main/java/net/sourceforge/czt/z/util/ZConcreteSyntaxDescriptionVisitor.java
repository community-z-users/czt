/*
  Copyright (C) 2006 Mark Utting
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

package net.sourceforge.czt.z.util;

import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.util.Visitor;

/** This class is useful for creating human-readable summaries
 *  of AST nodes.  It is typically used to generate a short (or long)
 *  description of the currently selected AST node within a Z editor.
 *  <p>
 *  It uses a visitor to classify a given AST node 
 *  into a {@link ConcreteSyntaxSymbol}, then a resource bundle (the default 
 *  is "net.sourceforge.czt.z.util.LongDescriptionResourceBundle") 
 *  to translate this ConcreteSyntaxSymbol into a human-readable
 *  string that describes the kind of AST node.  It then appends to 
 *  this string the result of applying a `name visitor' to the AST node,
 *  so that we can see the main names declared/used that AST node.
 *  The default name visitor is {@link ZGetNameVisitor}.
 *  </p>
 * 
 * @author petra
 */
public class ZConcreteSyntaxDescriptionVisitor
  implements TermVisitor<String>
{
  private String resourceName_ =
    "net.sourceforge.czt.z.util.LongDescriptionResourceBundle";

  private Visitor<ConcreteSyntaxSymbol> visitor_ =
    new ConcreteSyntaxSymbolVisitor();

  private Visitor<String> nameVisitor_ = new ZGetNameVisitor();

  public ZConcreteSyntaxDescriptionVisitor()
  {
  }

  public ZConcreteSyntaxDescriptionVisitor(String resourceName)
  {
    resourceName_ = resourceName;
  }

  public Visitor<String> getNameVisitor()
  {
    return nameVisitor_;
  }

  public void setNameVisitor(Visitor<String> nameVisitor)
  {
    nameVisitor_ = nameVisitor;
  }

  public String visitTerm(Term term)
  {
    ConcreteSyntaxSymbol symbol = term.accept(visitor_);
    if (symbol != null) {
      String localized =
        ResourceBundle.getBundle(resourceName_).getString(symbol.toString());
      String name = term.accept(nameVisitor_);
      if (name != null) return localized + " \"" + name + "\"";
      else return localized;
    }
    return null;
  }
}
