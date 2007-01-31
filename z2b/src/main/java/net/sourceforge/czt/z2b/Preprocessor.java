/*
  Copyright (C) 2007 Mark Utting
  This file is part of the CZT project.

  The CZT project contains free software; you can redistribute it and/or modify
  it under the terms of the GNU General Public License as published by
  the Free Software Foundation; either version 2 of the License, or
  (at your option) any later version.

  The CZT project is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with CZT; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
*/

package net.sourceforge.czt.z2b;

import java.io.*;
import java.util.logging.*;
import java.util.*;
import java.net.URL;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.base.util.*;
import net.sourceforge.czt.print.util.LatexString;
import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.ast.ProverFactory;
import net.sourceforge.czt.rules.Rewrite;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.RuleUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.FileSource;
import net.sourceforge.czt.session.Key;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.UrlSource;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.z.jaxb.JaxbXmlReader;
import net.sourceforge.czt.zpatt.util.Factory;

class Preprocessor
{
  private CopyVisitor copyVisitor_;
  private RuleTable rules_;

  Preprocessor()
  {
    try {
      Factory factory = new Factory(new ProverFactory());
      copyVisitor_ = new CopyVisitor(factory);
      SectionManager manager = new SectionManager("zpatt");
      Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
      manager.put(new Key("unfold", Source.class), unfoldSource);
      rules_ = (RuleTable) manager.get(new Key("unfold", RuleTable.class));
    }
    catch(CommandException e) {
      throw new RuntimeException(e);
    }
  }

  Term unfold(Term term, String section, SectionManager manager)
    throws CommandException
  {
    term = term.accept(copyVisitor_);
    return Rewrite.rewrite(manager, section, term, rules_);
  }
}
