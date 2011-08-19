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

package net.sourceforge.czt.vcg.z.feasibility;

import net.sourceforge.czt.vcg.util.VCNameFactory;
import net.sourceforge.czt.vcg.z.AbstractVC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.TruePred;

/**
 *
 * @author Leo Freitas
 * @date Dec 24, 2010
 */
public class FeasibilityVC extends AbstractVC<Pred> implements FeasibilityPropertyKeys
{

  public FeasibilityVC(long vcId, Para term, VCType type, Pred vc, VCNameFactory factory, String nameSuffix) throws VCCollectionException
  {
    super(vcId, term, type, vc, factory, nameSuffix);
  }

  public FeasibilityVC(long vcId, Para term, VCType type, Pred vc, VCNameFactory factory) throws VCCollectionException
  {
    super(vcId, term, type, vc, factory, VCG_FEASIBILITY_VCNAME_SUFFIX);
  }

  public FeasibilityVC(long vcId, Para term, VCType type, Pred vc, String nameSuffix) throws VCCollectionException
  {
    super(vcId, term, type, vc, nameSuffix);
  }

  public FeasibilityVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    super(vcId, term, type, vc, VCG_FEASIBILITY_VCNAME_SUFFIX);
  }

  @Override
  public boolean isTrivial()
  {
    return (getVC() instanceof TruePred);
  }
}
