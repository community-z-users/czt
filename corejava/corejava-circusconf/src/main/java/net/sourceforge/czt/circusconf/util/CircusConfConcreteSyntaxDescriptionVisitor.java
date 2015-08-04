/*
  Copyright (C) 2007 Mark Utting
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

package net.sourceforge.czt.circusconf.util;

import java.util.ResourceBundle;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.util.Visitor;

/**
 * @author Petra Malik
 */
public class CircusConfConcreteSyntaxDescriptionVisitor
  extends net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor
{
  private String resourceName_ =
    "net.sourceforge.czt.circustime.util.LongDescriptionResourceBundle";

  private final Visitor<CircusConfConcreteSyntaxSymbol> visitor_ =
    new CircusConfConcreteSyntaxSymbolVisitor();

  public CircusConfConcreteSyntaxDescriptionVisitor()
  {
    setNameVisitor(new CircusConfGetNameVisitor());
  }

  public CircusConfConcreteSyntaxDescriptionVisitor(String resourceName,
                                          String circusResourceName,
                                          String circustimeResourceName)
  {
    super(resourceName, circusResourceName);
    resourceName_ = circustimeResourceName;
    setNameVisitor(new CircusConfGetNameVisitor());
 }

  @Override
public String visitTerm(Term term)
  {
	  CircusConfConcreteSyntaxSymbol symbol = term.accept(visitor_);
    if (symbol != null) {
      String localized =
        ResourceBundle.getBundle(resourceName_).getString(symbol.toString());
      String name = term.accept(getNameVisitor());
      if (name != null) return localized + " \"" + name + "\"";
      else return localized;
    }
    return super.visitTerm(term);
  }
}
