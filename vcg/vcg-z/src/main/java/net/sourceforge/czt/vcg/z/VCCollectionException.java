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

package net.sourceforge.czt.vcg.z;

import net.sourceforge.czt.session.Dialect;

/**
 * TODO: should it include underlying VC?
 * @author Leo Freitas
 * @date Dec 24, 2010
 */
public class VCCollectionException extends VCGException
{
 /**
	 * 
	 */
	private static final long serialVersionUID = -495171216536668777L;

/** Creates a new instance of VCGException
   * @param message
   */
  public VCCollectionException(Dialect d, String message)
  {
     super(d, message);
  }

  public VCCollectionException(Dialect d, String message, Throwable cause)
  {
    super(d, message, cause);
  }

  public VCCollectionException(Dialect d, Throwable cause)
  {
    super(d, cause);
  }

  public VCCollectionException(Dialect d, String message, String origSectName, Throwable cause)
  {
    super(d, message, origSectName, cause);
  }
}
