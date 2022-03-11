/**
Copyright 2003 Mark Utting
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
package net.sourceforge.czt.parser.oz;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;

/**
 * <p>This class provides an example of a substitution visitor.
 * It substitutes each AndPred with an OrPred and each ForallPred
 * with an ExistsPred having the same children</p>
 *
 * @author Petra Malik
 */
public class JTreeVisitor
  implements TermVisitor<Object>
{
  public Object visitTerm(Term term)
  {
    List<Object> list = new ArrayList<Object>();
    Object[] children = term.getChildren();
    for (int i = 0; i < children.length; i++) {
      Object child = children[i];
      if (child instanceof Term) {
        list.add(((Term) child).accept(this));
      }
      else if (child instanceof List) {
        for (@SuppressWarnings("unchecked")
		Iterator<Object> iter = ((List<Object>) child).iterator(); iter.hasNext();) {
          Object object = iter.next();
          if (object instanceof Term) {
            Term t = (Term) object;
            list.add(t.accept(this));
          }
          else {
            list.add(object);
          }
        }
      }
      else if (child != null) {
        list.add(child);
      }
    }

    String objName = getBaseName(term);
    return new TermModel(objName, list);
  }

  private String getBaseName(Object o)
  {
    String result = null;

    String name = o.getClass().getName();
    result = name.substring(name.lastIndexOf(".") + 1, name.length());
    if (result.endsWith("Impl")) {
      result = result.substring(0, result.length() - 4);
    }
    return result;
  }
}
