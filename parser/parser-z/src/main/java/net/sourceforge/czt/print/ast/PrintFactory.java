/*
  Copyright (C) 2006 Petra Malik
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

package net.sourceforge.czt.print.ast;

import java.util.List;

import net.sourceforge.czt.base.impl.BaseFactory;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.util.OperatorName;

public class PrintFactory
  extends BaseFactory
{
  public Application createApplication()
  {
    return new Application(this);
  }

  public OperatorApplication createOperatorApplication(OperatorName opName,
                                                       List<Expr> args,
                                                       Precedence prec,
                                                       Assoc assoc)
  {
    return new OperatorApplication(this, opName, args, prec, assoc);
  }

  public PrintParagraph createPrintParagraph(List<?> something)
  {
    return new PrintParagraph(this, something);
  }

  public PrintExpression createPrintExpression(List<?> something)
  {
    return new PrintExpression(this, something);
  }

  public PrintPredicate createPrintPredicate(List<?> something,
                                             Precedence prec,
                                             Assoc assoc)
  {
    return new PrintPredicate(this, something, prec, assoc);
  }
}
