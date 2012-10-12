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

package net.sourceforge.czt.typecheck.zeves.impl;

import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.util.Pair;
import net.sourceforge.czt.z.ast.ZSect;
import net.sourceforge.czt.zeves.ast.ProofScript;

/**
 *
 * @author Leo Freitas
 * @date Nov 17, 2011
 */
public class SectSummaryAnn extends net.sourceforge.czt.typecheck.z.impl.SectSummaryAnn
{
  public SectSummaryAnn(String sectName)
  {
    super(sectName);
  }

  @Override
  protected void doSummarise(SectionManager sm, ZSect zs)
  {
    super.doSummarise(sm, zs);
    summary_.add(Pair.getPair("Proof scripts", ProofScriptSummary.create(sm).count(zs)));
  }

  public static class ProofScriptSummary extends SubParaSummary
  {
    protected ProofScriptSummary(SectionManager sm)
    {
      super(sm, ProofScript.class);
    }

    public static Summarise create(SectionManager sm)
    {
      return new ProofScriptSummary(sm);
    }
  }
}
