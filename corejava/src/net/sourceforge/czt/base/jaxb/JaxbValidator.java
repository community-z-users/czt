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

package net.sourceforge.czt.base.jaxb;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.Validator;

import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.util.AstValidator;

/**
 * The Jaxb validator.
 *
 * @author Petra Malik
 */
public class JaxbValidator implements AstValidator
{
  private Visitor visitor_;
  private String jaxbContextPath_;

  public JaxbValidator(Visitor v, String jaxbContextPath)
  {
    visitor_ = v;
    jaxbContextPath_ = jaxbContextPath;
  }

  private Object toJaxb(Term term)
  {
    Object erg = term.accept(visitor_);
    return erg;
  }

  public boolean validate(Term term)
  {
    Object o = toJaxb(term);
    try {
      JAXBContext jc =
        JAXBContext.newInstance(jaxbContextPath_);
      Validator v = jc.createValidator();
      return v.validate(o);
    } catch (Exception e) {
      e.printStackTrace();
      return false;
    }
  }
}
