/**
Copyright (C) 2004 Petra Malik
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

package net.sourceforge.czt.print.z;

import java.io.*;
import java.net.URL;

import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.parser.util.AbstractParserTest;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.util.ParseException;
import net.sourceforge.czt.z.ast.Spec;

/**
 * A (JUnit) test class for testing the zml to latex converter.
 *
 * @author Petra Malik
 */
public class ZmlToLatexTest
  extends AbstractParserTest
{
  public Term parse(URL url, SectionManager ignore)
    throws ParseException, IOException
  {
    SectionInfoRegistry toolkitInfo = ToolkitSectionInfoRegistry.getInstance();
    File tmpLatexFile = File.createTempFile("cztPrintTest", ".tex");
    tmpLatexFile.deleteOnExit();
    Spec spec = (Spec) ParseUtils.parse(url, toolkitInfo);
    WrappedSectionInfoRegistry tmpSectInfo =
      new WrappedSectionInfoRegistry(toolkitInfo);
    DeleteAnnVisitor visitor = new DeleteAnnVisitor();
    spec.accept(visitor);
    tmpSectInfo.add(spec);
    Writer writer = new FileWriter(tmpLatexFile);
    PrintUtils.printLatex(spec, writer, tmpSectInfo);
    writer.close();
    return ParseUtils.parse(tmpLatexFile.getAbsolutePath(), toolkitInfo);
  }
}
