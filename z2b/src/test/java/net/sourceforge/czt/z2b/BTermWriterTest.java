/**
Copyright (C) 2007 Mark Utting
This file is part of the CZT project.

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

package net.sourceforge.czt.z2b;

import java.io.*;

import junit.framework.*;

import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.CommandException;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.*;


/**
 * A (JUnit) test class for testing the BTermWriter class of Z2B
 *
 * @author Mark Utting
 */
public class BTermWriterTest
  extends TestCase
{
  private SectionManager sectman_;
  private BTermWriter termwriter_;
  private BWriter writer_;
  private StringWriter output_;

  public void setUp()
  {
    sectman_ = new SectionManager(Dialect.Z);
    output_ = new StringWriter();
    writer_ = new BWriter(output_, "UnitTest");
    termwriter_ = new BTermWriter(writer_);
  }

  private String getOutput()
  {
    String str = output_.toString();
    return str.substring(str.indexOf('\n')+1);
  }

  public void testExpr(String zexpr, String bexpr)
  throws IOException, CommandException
  {
    Source src = new StringSource(zexpr);
    Expr expr = ParseUtils.parseExpr(src, null, sectman_);
    termwriter_.printExpr(expr);
    assertEquals(bexpr, getOutput());
  }

  public void testPred(String zpred, String bpred)
  throws IOException, CommandException
  {
    Source src = new StringSource(zpred);
    Pred pred = ParseUtils.parsePred(src, null, sectman_);
    termwriter_.printPred(pred);
    assertEquals(bpred, getOutput());
  }
  
  public void testName() throws IOException, CommandException
  {
    testExpr("x", "x"); 
  }

  public void testArith() throws IOException, CommandException
  {
    testExpr("1+2*3 \\div 2", "1 + 2 * 3 / 2"); 
  }
  
  public void testArith2() throws IOException, CommandException
  {
    testExpr("(1+2)*3 \\mod 2", "(1 + 2) * 3 mod 2"); 
  }

  public void testForall() throws IOException, CommandException
  {
    testPred("(\\forall x:\\nat | x<10 @ x>5)",
        "!(x).(x : NAT & x < 10 => x > 5)");
  }

  public void testExists() throws IOException, CommandException
  {
    testPred("(\\exists x:\\nat | x<10 @ x>5)",
        "#(x).(x : NAT & x < 10 & x > 5)");
  }

  public void testLambda() throws IOException, CommandException
  {
    testExpr("(\\lambda x:\\nat | x<10 @ x+1)",
        "%(x).(x : NAT & x < 10 | x + 1)");
  }

  public void testSetComp1() throws IOException, CommandException
  {
    testExpr("\\{x:\\nat | x<10 \\}",
        "{x | x : NAT & x < 10}");
  }

  public void testProdExpr() throws IOException, CommandException
  {
    testExpr("\\nat \\cross \\nat \\cross \\nat",
             "NAT * (NAT * NAT)");
  }

  public void testTupleExpr() throws IOException, CommandException
  {
    testExpr("(1,2,3)",
             "1 |-> (2 |-> 3)");
  }

  public void testImage() throws IOException, CommandException
  {
    testExpr("f \\limg \\{ x \\} \\rimg", "f[{x}]");
  }

  public void testOpFront() throws IOException, CommandException
  {
    testExpr("front~x", "front(x)");
  }
}
