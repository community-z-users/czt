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

package net.sourceforge.czt.parser.zeves;

import java.util.ArrayList;
import java.util.List;
import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.parser.util.InfoTable;
import net.sourceforge.czt.parser.util.ThmTable;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.WarningManager;
import net.sourceforge.czt.z.util.ZUtils;
import net.sourceforge.czt.zeves.ast.ProofScript;

/**
 *
 * @author Leo Freitas
 * @date Jul 13, 2011
 */
public class ProofTable  extends InfoTable
{

  private final SortedMap<ZName, ProofInfo> proofTable_ = new TreeMap<ZName, ProofInfo>(ZUtils.ZNAME_COMPARATOR);
  private final WarningManager wm_ = new WarningManager();

  public ProofTable(Dialect d, String section)
  {
    super(d, section);
  }

  /**
   *
   * @param <T>
   * @param table
   * @throws net.sourceforge.czt.parser.util.InfoTable.InfoTableException
   */
  @Override
  protected <T extends InfoTable> void addParentTable(T table)
    throws InfoTable.InfoTableException
  {
    addParentProofTable((ProofTable)table);
  }

  private void addParentProofTable(ProofTable parentTable)
   // throws ProofTableException
  {
    proofTable_.putAll(parentTable.proofTable_);
  }

  private void addTheorem(ZName name, ProofInfo info)
   // throws ProofTableException
  {
    if (proofTable_.get(name) != null) {
      String message = "Proof {0} defined more than once";
      wm_.warn(message, name);
//      throw new ProofTableException(message);
    }
    proofTable_.put(name, info);
  }

  public ProofInfo lookup(ZName name)
  {
    return proofTable_.get(name);
  }

  public void add(ProofScript para) throws ProofTableException
  {
    ZName proofName = para.getZName();
    if (proofName == null || proofName.getWord().isEmpty())
    {
      throw new ProofTableException(getDialect(), "Error: cannot add unnamed proof script to proof table.");
    }
    ProofInfo thmInfo = new ProofInfo(getSectionName(), para);
    addTheorem(proofName, thmInfo);
    return;
  }

  public List<ZName> checkAgainst(ThmTable thmTable)
  {
    List<ZName> unknown = new ArrayList<ZName>(proofTable_.keySet().size() / 2);
    for(ZName name : proofTable_.keySet())
    {
      final String word = name.getWord();
      // domain check (e.g., XXX\$domainCheck) conjectures are not explicitly declared
     if (!word.endsWith("$domainCheck") && thmTable.lookup(word) == null)
      {
        unknown.add(name);
      }
    }
    if (!unknown.isEmpty())
    {
      wm_.warn("Missing conjecture declaration for proof scripts {0}", unknown);
    }
    return unknown;
  }

  public void verifyConsistency(ThmTable thmTable)
          throws ProofTableException
  {
    List<ZName> result = checkAgainst(thmTable);
    if (!result.isEmpty())
    {
      throw new ProofTableException(getDialect(), "Missing conjecture declaration for proof scripts " + result);
    }
  }

  public static class ProofInfo extends InfoTable.Info
  {
    private final ProofScript para_;

    public ProofInfo(String section, ProofScript para)
    {
      super(section);
      para_ = para;
    }

    public ProofScript getProofScript()
    {
      return para_;
    }
  }

  public static class ProofTableException
    extends InfoTable.InfoTableException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -7146641664325911321L;

	public ProofTableException(Dialect d, String message)
    {
      super(d, message);
    }
  }
}

