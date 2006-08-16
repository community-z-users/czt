package net.sourceforge.czt.rules.ast;

import java.io.StringWriter;
import java.io.Writer;

import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.ProverProviso;
import net.sourceforge.czt.rules.ProverUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.SchExpr;
import net.sourceforge.czt.z.ast.TruePred;
import net.sourceforge.czt.z.ast.ZDeclList;
import net.sourceforge.czt.z.ast.ZSchText;
import junit.framework.Assert;
import junit.framework.TestCase;

public class ProverCalculateProvisoTest extends TestCase
{
  ProverFactory factory_ = new ProverFactory();
  SectionManager sectman_ = new SectionManager();
  
  /** Convenience method for creating expressions for testing. */
  public Expr parseExpr(String latexString)
  {
    try {
      Source e = new StringSource(latexString);
      e.setMarkup(Markup.LATEX);
      return (Expr) ParseUtils.parseExpr(e, "zpattern\\_toolkit", sectman_);
    } catch (Exception e) {
      Assert.fail("Error parsing expr: " + latexString + ".  Error="+e);
    }
    // not reached
    return null;
  }
  
  protected void setUp() throws Exception
  {
    super.setUp();
  }

  protected void tearDown() throws Exception
  {
    super.tearDown();
  }

  private void doCheck(String input, String expect)
  {
    String sect = "zpattern_toolkit";
    Expr left = factory_.createJokerExpr("left");
    Expr right = parseExpr(input);
    ProverCalculateProviso proviso = 
      (ProverCalculateProviso) factory_.createCalculateProviso(null, left, right);
    proviso.check(sectman_, sect);
    assertEquals(ProverProviso.Status.PASS, proviso.getStatus());
    // check result
    Expr result = (Expr) ProverUtils.removeJoker(left);
    StringWriter swriter = new StringWriter();
    PrintUtils.printLatex(result, swriter, sectman_, sect);
    System.out.println("Result was:"+swriter.toString());
    assertEquals(expect, swriter.toString());
  }

  public void testCheckSchemaMinusFail()
  {
    // This will fail to unify, because the LHS is not a joker.
    Expr left = parseExpr("ShouldNotUnify");
    Expr right = parseExpr("[a:\\arithmos~; b:\\arithmos|true] "
                        + "\\schemaminus "
                        + " [c:\\arithmos~; b:\\arithmos|true]");
    ProverCalculateProviso proviso = (ProverCalculateProviso) factory_.createCalculateProviso(null, left, right);
    proviso.check(sectman_, "zpattern_toolkit");
    assertEquals(ProverProviso.Status.FAIL, proviso.getStatus());
  }

  public void testCheckSchemaMinus1()
  {
    doCheck("[a:\\arithmos~; b:\\arithmos|true] "
         + "\\schemaminus "
         + " [c:\\arithmos~; b:\\arithmos|true]",
         "[ a : \\arithmos | true ]");
  }
  
  public void testDecorExpr()
  {
    doCheck("[a:\\arithmos~; b:\\nat | a < b]~'",
            "[ a' : \\arithmos ; b' : \\nat | a' < b' ]");
  }

  public void testBindingEmpty()
  {
    doCheck("binding ~ [ | true]",
            "\\lblot \\rblot");
  }

  public void testBinding()
  {
    doCheck("binding ~ [a:\\arithmos~; b:\\nat | true]",
            "\\lblot a == a , b == b \\rblot");
  }

  public void testUnprefix1()
  {
    doCheck("S \\unprefix Schema", "chema");
  }

  public void testUnprefix2()
  {
    doCheck("\\Xi \\unprefix \\Xi Schema", "Schema");
  }
}
