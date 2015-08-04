/*
  Copyright (C) 2008 Leo Freitas
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

package net.sourceforge.czt.circus.util;

import net.sourceforge.czt.circus.ast.ActionPara;
import net.sourceforge.czt.circus.ast.ChannelPara;
import net.sourceforge.czt.circus.ast.ChannelSetPara;
import net.sourceforge.czt.circus.ast.NameSetPara;
import net.sourceforge.czt.circus.ast.ProcessPara;
import net.sourceforge.czt.circus.ast.TransformerPara;
import net.sourceforge.czt.circus.visitor.ActionParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelParaVisitor;
import net.sourceforge.czt.circus.visitor.ChannelSetParaVisitor;
import net.sourceforge.czt.circus.visitor.NameSetParaVisitor;
import net.sourceforge.czt.circus.visitor.ProcessParaVisitor;
import net.sourceforge.czt.circus.visitor.TransformerParaVisitor;

/**
 * @author Petra Malik
 */
public class CircusGetNameVisitor
  extends net.sourceforge.czt.z.util.ZGetNameVisitor
  implements ChannelSetParaVisitor<String>,
             NameSetParaVisitor<String>,
             ActionParaVisitor<String>,
             ProcessParaVisitor<String>,
             ChannelParaVisitor<String>,
             TransformerParaVisitor<String>
{

  @Override
  public String visitChannelSetPara(ChannelSetPara term)
  {
    return visit(term.getName());
  }

  @Override
  public String visitNameSetPara(NameSetPara term)
  {
    return visit(term.getName());
  }

  @Override
  public String visitActionPara(ActionPara term)
  {
    return visit(term.getName());
  }

  @Override
  public String visitProcessPara(ProcessPara term)
  {
    return visit(term.getName());
  }

  @Override
  public String visitChannelPara(ChannelPara term)
  {
    return visit(term.getZDeclList());
  }

  @Override
  public String visitTransformerPara(TransformerPara term)
  {
    return visit(term.getName());
  }
}
