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

package net.sourceforge.czt.vcg.z.refinement;

import net.sourceforge.czt.vcg.util.Definition;
import net.sourceforge.czt.vcg.z.VC;
import net.sourceforge.czt.vcg.z.VCCollectionException;
import net.sourceforge.czt.vcg.z.VCType;
import net.sourceforge.czt.vcg.z.feasibility.FeasibilityVCCollector;
import net.sourceforge.czt.vcg.z.transformer.refinement.ZPredTransformerRef;
import net.sourceforge.czt.z.ast.AxPara;
import net.sourceforge.czt.z.ast.Para;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.util.Factory;
import net.sourceforge.czt.z.util.ZUtils;

/**
 *
 * @author Leo Freitas
 * @date Aug 31, 2011
 */
public class RefinementVCCollector extends FeasibilityVCCollector implements RefinementPropertyKeys
{
  /**
   *
   */
  public RefinementVCCollector()
  {
    this(ZUtils.createConsoleFactory());
  }

  /** Creates a new instance of DCTerm
   * @param factory
   */
  public RefinementVCCollector(Factory factory)
  {
    super(factory);
    predTransformer_ = new ZPredTransformerRef(factory, this);
    predTransformer_.setApplyTransformer(PROP_VCG_REFINEMENT_APPLY_TRANSFORMERS_DEFAULT);
    setCreateZSchemas(PROP_VCG_REFINEMENT_CREATE_ZSCHEMAS_DEFAULT);
  }

  @Override
  protected VCCollectionException createVCCollectionException(final String message)
  {
    return new RefinementException(message);
  }

  @Override
  protected VCCollectionException createVCCollectionException(final String message, Throwable e)
  {
    return new RefinementException(message, e);
  }

  public interface VCNameSuffix
  {
    public String getVCNameSuffix();
  }

  @Override
  public VC<Pred> createVC(long vcId, Para term, VCType type, Pred vc) throws VCCollectionException
  {
    VCNameSuffix ns = term.getAnn(VCNameSuffix.class);
    if (getVCNameFactory() != null)
      if (ns != null)
        return new RefinementVC(vcId, term, type, vc, getVCNameFactory(), ns.getVCNameSuffix());
      else
        return new RefinementVC(vcId, term, type, vc, getVCNameFactory());
    else
      if (ns != null)
        return new RefinementVC(vcId,term, type, vc, ns.getVCNameSuffix());
      else
        return new RefinementVC(vcId, term, type, vc);
  }

  @Override
  protected void collectStateInfo(AxPara term, Definition termDef)
  {
    super.collectStateInfo(term, termDef);

  }

  @Override
  protected Pred handleSchema(Definition termDef)
  {
    return super.handleSchema(termDef);
  }
}
