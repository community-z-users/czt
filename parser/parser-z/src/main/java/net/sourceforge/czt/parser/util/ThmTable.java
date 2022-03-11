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
package net.sourceforge.czt.parser.util;

import java.util.SortedMap;
import java.util.TreeMap;

import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.util.CztLogger;
import net.sourceforge.czt.z.ast.ConjPara;

/**
 *
 * @author leo
 */
public class ThmTable extends InfoTable 
{
  
  private SortedMap<String, ThmInfo> thmTable_ = new TreeMap<String, ThmInfo>();

  public ThmTable(Dialect d, String section)
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
    addParentThmTable((ThmTable)table);
  }

  private void addParentThmTable(ThmTable parentTable)
    throws ThmTableException
  {
    thmTable_.putAll(parentTable.thmTable_);
  }
  
  private void addTheorem(String name, ThmInfo info)
    throws ThmTableException
  {
    if (thmTable_.get(name) != null) {
      String message = "Conjecture " + name + " defined more than once";
      CztLogger.getLogger(getClass()).warning(message);
      //throw new ThmTableException(message); Leave the duplication to be caught by the typechecker
    }
    thmTable_.put(name, info);
  }
  
  public ThmInfo lookup(String name)
  {
    return thmTable_.get(name);
  }
  
  public void add(ConjPara para) throws ThmTableException
  {
    String thmName = para.getName();
    if (thmName == null || thmName.isEmpty())
    {
      throw new ThmTableException(getDialect(), "Error: cannot add unnamed conjecture to conjecture table.");
    }    
    ThmInfo thmInfo = new ThmInfo(getSectionName(), para);
    addTheorem(thmName, thmInfo);
    return;
  }  
  
  public static class ThmInfo extends InfoTable.Info
  {
    private ConjPara para_;

    public ThmInfo(String section, ConjPara para)
    {
      super(section);
      para_ = para;
    }

    public ConjPara getConjPara()
    {
      return para_;
    }
  }
  
  public static class ThmTableException
    extends InfoTable.InfoTableException
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 2110188825241660479L;

	public ThmTableException(Dialect d, String message)
    {
      super(d, message);
    }
  }
}
