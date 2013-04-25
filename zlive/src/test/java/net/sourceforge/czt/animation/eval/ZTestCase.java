/**
Copyright (C) 2004 Mark Utting
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

package net.sourceforge.czt.animation.eval;

import junit.framework.Assert;
import junit.framework.TestCase;
import net.sourceforge.czt.parser.z.ParseUtils;
import net.sourceforge.czt.session.Markup;
import net.sourceforge.czt.session.Source;
import net.sourceforge.czt.session.StringSource;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.NumExpr;
import net.sourceforge.czt.z.ast.Pred;
import net.sourceforge.czt.z.ast.ZName;
import net.sourceforge.czt.z.util.Factory;


/**
 * A subclass of JUnit TestCase which defines some Z syntax.
 * This class defines a large collection of convenient Z AST
 * values for use within tests.  For example, NumExprs from
 * -10 upto 30 (called in10, in9, ... i0, i1, ... i30),
 * the empty Envir (called empty) and ZNames x, y and z.
 *
 * @author Mark Utting
 */
public abstract class ZTestCase extends TestCase
{
  protected static ZLive zlive_ = new ZLive();
  
  protected Factory factory_ = zlive_.getFactory();

  /** The accuracy used to check number-of-solutions in Mode results. */
  protected final double ACCURACY = 0.01;

  /** An empty environment. */
  protected Envir empty = new Envir();
  
  // Some ZNames.
  protected ZName x = factory_.createZName("x");
  protected ZName y = factory_.createZName("y");
  protected ZName z = factory_.createZName("z");
  
  // convenient names for numbers -10 .. 30
  // some negative numbers
  protected NumExpr in10 = factory_.createNumExpr(-10);
  protected NumExpr in9 = factory_.createNumExpr(-9);
  protected NumExpr in8 = factory_.createNumExpr(-8);
  protected NumExpr in7 = factory_.createNumExpr(-7);
  protected NumExpr in6 = factory_.createNumExpr(-6);
  protected NumExpr in5 = factory_.createNumExpr(-5);
  protected NumExpr in4 = factory_.createNumExpr(-4);
  protected NumExpr in3 = factory_.createNumExpr(-3);
  protected NumExpr in2 = factory_.createNumExpr(-2);
  protected NumExpr in1 = factory_.createNumExpr(-1);
  protected NumExpr i0 = factory_.createNumExpr(0);
  protected NumExpr i1 = factory_.createNumExpr(1);
  protected NumExpr i2 = factory_.createNumExpr(2);
  protected NumExpr i3 = factory_.createNumExpr(3);
  protected NumExpr i4 = factory_.createNumExpr(4);
  protected NumExpr i5 = factory_.createNumExpr(5);
  protected NumExpr i6 = factory_.createNumExpr(6);
  protected NumExpr i7 = factory_.createNumExpr(7);
  protected NumExpr i8 = factory_.createNumExpr(8);
  protected NumExpr i9 = factory_.createNumExpr(9);
  protected NumExpr i10 = factory_.createNumExpr(10);
  protected NumExpr i11 = factory_.createNumExpr(11);
  protected NumExpr i12 = factory_.createNumExpr(12);
  protected NumExpr i13 = factory_.createNumExpr(13);
  protected NumExpr i14 = factory_.createNumExpr(14);
  protected NumExpr i15 = factory_.createNumExpr(15);
  protected NumExpr i16 = factory_.createNumExpr(16);
  protected NumExpr i17 = factory_.createNumExpr(17);
  protected NumExpr i18 = factory_.createNumExpr(18);
  protected NumExpr i19 = factory_.createNumExpr(19);
  protected NumExpr i20 = factory_.createNumExpr(20);
  protected NumExpr i21 = factory_.createNumExpr(21);
  protected NumExpr i22 = factory_.createNumExpr(22);
  protected NumExpr i23 = factory_.createNumExpr(23);
  protected NumExpr i24 = factory_.createNumExpr(24);
  protected NumExpr i25 = factory_.createNumExpr(25);
  protected NumExpr i26 = factory_.createNumExpr(26);
  protected NumExpr i27 = factory_.createNumExpr(27);
  protected NumExpr i28 = factory_.createNumExpr(28);
  protected NumExpr i29 = factory_.createNumExpr(29);
  protected NumExpr i30 = factory_.createNumExpr(30);
  
  /** Convenience method for creating expressions for testing. */
  public Expr parseExpr(String latexString)
  {
    try {
      Source e = new StringSource(latexString);
      e.setMarkup(Markup.LATEX);
      return (Expr) ParseUtils.parseExpr(e, null, zlive_.getSectionManager());
    } catch (Exception e) {
      Assert.fail("Error parsing expr: " + latexString + ".  Error="+e);
    }
    // not reached
    return null;
  }
  
  /** Convenience method for creating predicates for testing. */
  public Pred parsePred(String latexString)
  {
    try {
      Source e = new StringSource(latexString);
      e.setMarkup(Markup.LATEX);
      return (Pred) ParseUtils.parsePred(e, null, zlive_.getSectionManager());
    } catch (Exception e) {
      Assert.fail("Error parsing pred: " + latexString + ".  Error="+e);
    }
    // not reached
    return null;
  }
}




