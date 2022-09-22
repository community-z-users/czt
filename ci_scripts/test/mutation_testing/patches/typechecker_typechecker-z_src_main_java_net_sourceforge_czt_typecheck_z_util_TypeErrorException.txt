/*
  Copyright (C) 2005 Leo Freitas
  This file is part of the czt project.

  The czt project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The czt project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with czt; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.typecheck.z.util;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import net.sourceforge.czt.base.util.PerformanceSettings;
import net.sourceforge.czt.typecheck.z.ErrorAnn;
import net.sourceforge.czt.parser.util.CztErrorList;

/**
 *
 * @author Leo Freitas
 */
public class TypeErrorException extends net.sourceforge.czt.util.CztException
  implements CztErrorList {    
    
    /**
	 * 
	 */
	private static final long serialVersionUID = 32926149840525162L;
	private final List<ErrorAnn> fErrors = new ArrayList<ErrorAnn>(PerformanceSettings.INITIAL_ARRAY_CAPACITY);
    
    /** Creates a new instance of TypeErrorException
     * @param message 
     * @param errors
     */
    public TypeErrorException(String message, List<? extends ErrorAnn> errors) {
        super(message);
        fErrors.addAll(errors);
    }
    
    public TypeErrorException(String message, Throwable cause, List<? extends ErrorAnn> errors) {
        super(message,  cause);
        fErrors.addAll(errors);
    }
    
    public List<? extends ErrorAnn> errors() {
      return getErrors();
    }

    @Override
    public List<ErrorAnn> getErrors() {
      return Collections.unmodifiableList(fErrors);
    }

    @Override
    public String getMessage()
    {
      StringBuilder result = new StringBuilder(super.getMessage());
      for(ErrorAnn e : fErrors)
      {
        result.append("\n\t").append(e);
      }
      return result.toString();
    }
}
