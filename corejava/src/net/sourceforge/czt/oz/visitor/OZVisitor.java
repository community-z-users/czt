
/*
THIS FILE WAS GENERATED BY GNAST.
ANY MODIFICATIONS TO THIS FILE WILL BE LOST UPON REGENERATION.

************************************************************

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
package net.sourceforge.czt.oz.visitor;

import net.sourceforge.czt.core.ast.*;
import net.sourceforge.czt.oz.ast.*;

/**
 * An interface that collects all single visitor interfaces
 * contained in this package.
 *
 * @author Gnast version 0.1
 */
public interface OZVisitor
  extends
    net.sourceforge.czt.oz.visitor.RenameListVisitor,
    net.sourceforge.czt.oz.visitor.ActualParametersVisitor,
    net.sourceforge.czt.oz.visitor.DistConjOpExprVisitor,
    net.sourceforge.czt.oz.visitor.BasicOpExprVisitor,
    net.sourceforge.czt.oz.visitor.MainOpExprVisitor,
    net.sourceforge.czt.oz.visitor.HideOpExprVisitor,
    net.sourceforge.czt.oz.visitor.StringListTypeVisitor,
    net.sourceforge.czt.oz.visitor.SeqOpExprVisitor,
    net.sourceforge.czt.oz.visitor.InheritedClassVisitor,
    net.sourceforge.czt.oz.visitor.DistChoiceOpExprVisitor,
    net.sourceforge.czt.oz.visitor.AssoParallelOpExprVisitor,
    net.sourceforge.czt.oz.visitor.StateVisitor,
    net.sourceforge.czt.oz.visitor.OpPromotionExprVisitor,
    net.sourceforge.czt.oz.visitor.ConjOpExprVisitor,
    net.sourceforge.czt.oz.visitor.ClassParaVisitor,
    net.sourceforge.czt.oz.visitor.ParenOpExprVisitor,
    net.sourceforge.czt.oz.visitor.OperationVisitor,
    net.sourceforge.czt.oz.visitor.LocalDefVisitor,
    net.sourceforge.czt.oz.visitor.OperationBoxVisitor,
    net.sourceforge.czt.oz.visitor.InitialStateVisitor,
    net.sourceforge.czt.oz.visitor.DistSeqOpExprVisitor,
    net.sourceforge.czt.oz.visitor.ScopeEnrichOpExprVisitor,
    net.sourceforge.czt.oz.visitor.SecondaryAttributesVisitor,
    net.sourceforge.czt.oz.visitor.RenameOpExprVisitor,
    net.sourceforge.czt.oz.visitor.ExChoiceOpExprVisitor,
    net.sourceforge.czt.oz.visitor.ParallelOpExprVisitor,
    net.sourceforge.czt.oz.visitor.FormalParametersVisitor,
    net.sourceforge.czt.util.Visitor
{
}
