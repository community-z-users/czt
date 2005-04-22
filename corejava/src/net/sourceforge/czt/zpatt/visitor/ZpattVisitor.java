
/******************************************************************************
DO NOT EDIT THIS FILE!  THIS FILE WAS GENERATED BY GNAST
FROM THE TEMPLATE FILE AstVisitor.vm.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

-------------------------------------------------------------------------------

Copyright 2003, 2004, 2005 Mark Utting
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
******************************************************************************/

package net.sourceforge.czt.zpatt.visitor;

import net.sourceforge.czt.zpatt.ast.*;

/**
 * An interface that collects all single visitor interfaces
 * contained in this package.
 *
 * @author Gnast version 0.1
 */
public interface ZpattVisitor
  extends
    net.sourceforge.czt.zpatt.visitor.JokerNameVisitor,
    net.sourceforge.czt.zpatt.visitor.PredSequentVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerExprVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerExprListBindingVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerExprBindingVisitor,
    net.sourceforge.czt.zpatt.visitor.LookupConstDeclProvisoVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerExprListVisitor,
    net.sourceforge.czt.zpatt.visitor.LookupPredProvisoVisitor,
    net.sourceforge.czt.zpatt.visitor.CalculateProvisoVisitor,
    net.sourceforge.czt.zpatt.visitor.SequentContextVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerNameBindingVisitor,
    net.sourceforge.czt.zpatt.visitor.DeductionVisitor,
    net.sourceforge.czt.zpatt.visitor.RuleVisitor,
    net.sourceforge.czt.zpatt.visitor.CheckProvisoVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerDeclListVisitor,
    net.sourceforge.czt.zpatt.visitor.BindingVisitor,
    net.sourceforge.czt.zpatt.visitor.TypeProvisoVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerDeclListBindingVisitor,
    net.sourceforge.czt.zpatt.visitor.JokersVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerPredVisitor,
    net.sourceforge.czt.zpatt.visitor.JokerPredBindingVisitor,
    net.sourceforge.czt.util.Visitor
{
}
