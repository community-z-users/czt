/*
Copyright 2003 Mark Utting
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

package net.sourceforge.czt.zed.jaxb;

import java.io.IOException;
import java.io.OutputStream;
import java.io.Writer;
import java.util.*;
import java.util.logging.Logger;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Validator;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.zed.ast.Term;
import net.sourceforge.czt.zed.util.AstValidator;

/**
 * The Jaxb validator.
 *
 * @author Petra Malik
 */
public class JaxbValidator implements AstValidator
{
  private static final String sClassName = "JaxbValidator";
  private static final Logger sLogger =
    Logger.getLogger("net.sourceforge.czt.zed.jaxb." + sClassName);

  private Visitor mVisitor;

  public JaxbValidator(Visitor v)
  {
    mVisitor = v;
  }

  private Object toJaxb(Term term)
  {
    final String methodName = "toJaxb";
    sLogger.entering(sClassName, methodName, term);
    Object erg = term.accept(mVisitor);
    sLogger.exiting(sClassName, methodName, erg);
    return erg;
  }

  public boolean validate(Term term)
  {
    Object o = toJaxb(term);
    try {
      JAXBContext jc =
	JAXBContext.newInstance("net.sourceforge.czt.zed.jaxb.gen");
      Validator v = jc.createValidator();
      return v.validate(o);
    } catch(Exception e) {
      e.printStackTrace();
      return false;
    }
  }
}
