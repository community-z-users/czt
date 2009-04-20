/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.util;

import java.util.Collection;
import java.util.SortedMap;
import java.util.TreeMap;
import net.sourceforge.czt.z.ast.ConjPara;

/**
 *
 * @author leo
 */
public class ThmTable extends InfoTable 
{
  
  private SortedMap<String, ThmInfo> thmTable_ = new TreeMap<String, ThmInfo>();

  public ThmTable(String section, Collection<ThmTable> parents)
    throws InfoTable.InfoTableException
  {
    super(section);
    addParents(parents);
  }  
  
  /**
   * 
   * @param <T>
   * @param <E>
   * @param table
   * @throws E
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
      throw new ThmTableException(message);
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
      throw new ThmTableException("Error: cannot add unnamed conjecture to conjecture table.");
    }    
    ThmInfo thmInfo = new ThmInfo(getSection(), para);
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
    public ThmTableException(String message)
    {
      super(message);
    }
  }
}
