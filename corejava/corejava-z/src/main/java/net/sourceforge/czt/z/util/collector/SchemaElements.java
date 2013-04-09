/*
 * Copyright (C) 2011 Leo Freitas
 * This file is part of the CZT project.
 * 
 * The CZT project contains free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 * 
 * The CZT project is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with CZT; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */
package net.sourceforge.czt.z.util.collector;

import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Jul 25, 2011
 */
public class SchemaElements extends GenericElements<AxPara>
{

  private Expr fExpr;
  protected ExprCollector fExprCollector;

  /** Creates a new instance of SchemaElements
   * @param term
   */
  SchemaElements()
  {
    super();
    fExpr = null;
    fExprCollector = new ExprCollector();
  }

  @Override
  public void collect(AxPara term)
  {
    assert ZUtils.isSimpleSchema(term);
    setName(ZUtils.assertZName(ZUtils.getSchemaName(term)).getWord());
    collectGenerics(ZUtils.getSchemaZGenFormals(term));
    fExpr = ZUtils.getSchemaDefExpr(term);
  }

  public Expr getExpr()
  {
    return fExpr;
  }

  @Override
  public String toString()
  {
    return super.toString() + ": " + String.valueOf(fExpr);
  }


}
