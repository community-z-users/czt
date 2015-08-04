/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.util.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.visitor.*;
import net.sourceforge.czt.parser.util.OpTable;
import net.sourceforge.czt.util.CztException;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.visitor.*;

/**
 * A translator to Spivey Z AST.
 *
 * <ul>
 *   <li>create named schemas for schema expressions.</li>
 * </ul>
 *
 * @author Petra Malik
 */
public class ToSpiveyZVisitor
  implements TermVisitor<Object>,
             AxParaVisitor<Object>,
             RefExprVisitor<Object>,
             SchExprVisitor<Object>
{
  private static int count_ = 0;
  private Factory factory_ = new Factory();
  private List<Object> anns_;
  private Stack<Term> parents_ = new Stack<Term>();

  public Object visitTerm(Term term)
  {
    parents_.push(term);
    VisitorUtils.visitTerm(this, term);
    parents_.pop();
    return null;
  }

  public Object visitSchExpr(SchExpr schExpr)
  {
	if (anns_ == null) {
		throw new CztException("Invalid annotations; not yet loaded through visitAxPara");
	}
    Term parent = parents_.pop();
    if (! (parent instanceof ConstDecl)) {
      String name = getNextName();
      anns_.add(createSchema(name, schExpr));
      schExpr.getAnns().add(name);
      System.err.println(name + " created");
    }
    else {
      VisitorUtils.visitTerm(this, schExpr);
    }
    parents_.push(parent);
    return null;
  }

  public Object visitAxPara(AxPara axPara)
  {
    parents_.push(axPara);
    anns_ = axPara.getAnns();
    boolean defs = false;
    if (Box.OmitBox.equals(axPara.getBox())) {
      final List<Decl> decls = axPara.getZSchText().getZDeclList();
      for (Decl decl : decls) {
        final ConstDecl constDecl = (ConstDecl) decl;
        final TypeAnn typeAnn =
          (TypeAnn) constDecl.getExpr().getAnn(TypeAnn.class);
        Type type = typeAnn.getType();
        if (type instanceof PowerType) {
          PowerType powerType = (PowerType) type;
          if (powerType.getType() instanceof SchemaType) {
            defs = true;
          }
        }
      }
    }
    if (! defs) {
      VisitorUtils.visitTerm(this, axPara);
    }
    parents_.pop();
    return null;
  }

  /**
   * Visit the expression list only when explicit is true.
   */
  public Object visitRefExpr(RefExpr refExpr)
  {
    if (refExpr.getExplicit()) {
      VisitorUtils.visitTerm(this, refExpr);
    }
    return null;
  }
  
  protected static synchronized void countIncrement()
  {
	count_++;  
  }

  protected String getNextName()
  {
	String result = "cztschema" + count_;
	countIncrement();
	return result;
  }

  protected AxPara createSchema(String name, SchExpr schExpr)
  {
    Name declName = factory_.createZName(name);
    return factory_.createSchema(declName, schExpr.getSchText());
  }
}
