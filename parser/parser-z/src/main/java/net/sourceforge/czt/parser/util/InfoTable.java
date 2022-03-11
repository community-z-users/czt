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

import java.util.Collection;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.Dialect;

/**
 * Base class for section management tables.
 * @author Leo Freitas
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
  private final String sectionName_;
  
  private final Dialect dialect_;
  
  /**
   * Creates an information table for a given section name. DO NOT have a constructor
   * for adding the parents - this could create incoherent initialisations due to the
   * order of construction in Java.
   * @param sectionName
   */
  public InfoTable(Dialect d, String sectionName)
  {
    if (d == null || sectionName == null) throw new NullPointerException();
    dialect_ = d;
    sectionName_ = sectionName;
  }
  
  public Dialect getDialect()
  {
	  return dialect_;
  }
  
  public final void addParents(Collection<? extends InfoTable> parents)
    throws InfoTableException
  {
    if (parents != null) {
      for (InfoTable table : parents) {
        addParentTable(table);
      }
    }
  }
  
  protected abstract <T extends InfoTable> void addParentTable(T table) throws InfoTableException;
  
  public String getSectionName()
  {
    return sectionName_;
  }

  public static abstract class Info
  {
    /**
     * The name of the section where this operator is defined.
     */
    private String sectionName_;
    
    protected Info(String sectionName)
    {
      assert sectionName != null;
      sectionName_ = sectionName;
    }

    public String getSectionName()
    {
      return sectionName_;
    }
    
    protected void setSectionName(String name)
    {
    	if (name == null) throw new NullPointerException("InfoTable.Info section name cannot be null");
    	sectionName_ = name;
    }
  }
  
  public static class InfoTableException extends CommandException 
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -8793516413277804774L;

	public InfoTableException(Dialect d, String message)
    {
      super(d, message);
    }

    public InfoTableException(Dialect d, String message, Throwable cause)
    {
      super(d, message, cause);
    }
  }
}
