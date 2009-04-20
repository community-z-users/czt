/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package net.sourceforge.czt.parser.util;

import java.util.Collection;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.z.util.ZString;

/**
 *
 * @author leo
 */
public abstract class InfoTable {

  /**
   * Removes all decorations, that are strokes,
   * from a decorword and returns the word part.
   */
  public static String getWord(String decorword)
  {
    Decorword dw = new Decorword(decorword);
    return dw.getWord();
  }
  /**
   * The name of the section.
   */
  private String section_;
  
  /**
   *    
   * @param <E> 
   * @param section
   * @param parents
   * @throws net.sourceforge.czt.parser.util.InfoTable.InfoTableException
   */
  public InfoTable(String section) 
  {
    section_ = section;    
  }
  
  protected void addParents(Collection<? extends InfoTable> parents) 
    throws InfoTableException
  {
    if (parents != null) {
      for (InfoTable table : parents) {
        addParentTable(table);
      }
    }
  }
  
  protected abstract <T extends InfoTable> void addParentTable(T table) throws InfoTableException;
  
  public String getSection()
  {
    return section_;
  }

  public static abstract class Info
  {
    /**
     * The name of the section where this operator is defined.
     */
    private String section_;
    
    protected Info(String section)
    {
      section_ = section;
    }

    public String getSection()
    {
      return section_;
    }    
  }
  
  public static class InfoTableException extends CommandException 
  {
    public InfoTableException(String message)
    {
      super(message);
    }
  }
}
