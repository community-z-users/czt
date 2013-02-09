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

package net.sourceforge.czt.typecheck.zeves.util;

import net.sourceforge.czt.typecheck.z.util.UResult;
import net.sourceforge.czt.z.ast.Type2;

/**
 *
 * @author Leo Freitas
 * @date Nov 9, 2011
 */
public class UnificationEnv extends
        net.sourceforge.czt.typecheck.z.util.UnificationEnv {

  public UnificationEnv()
  {
    super();
  }

  public UnificationEnv(net.sourceforge.czt.typecheck.z.impl.Factory zFactory)
  {
    super(zFactory);
  }

  @Override
  public UResult unify(Type2 typeA, Type2 typeB)
  {
    UResult result = FAIL;
    // for ZEves, bindings are implicitly a power type already
    // this is mostly called as (vPowerType, type), where type
    // is a schema type, whereas the Z typechecker expects a
    // Power(SchemaType)
    if (isPowerType(typeA) && isSchemaType(typeB))
    {
      result = unify(powerType(typeA).getType(), schemaType(typeB));
    }
    else
    {
      result = super.unify(typeA, typeB);
    }
    return result;
  }
}
