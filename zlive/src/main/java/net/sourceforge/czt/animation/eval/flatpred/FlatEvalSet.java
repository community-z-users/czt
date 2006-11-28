/*
  ZLive - A Z animator -- Part of the CZT Project.
  Copyright 2004 Mark Utting

  This program is free software; you can redistribute it and/or
  modify it under the terms of the GNU General Public License
  as published by the Free Software Foundation; either version 2
  of the License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful,
  but WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
  GNU General Public License for more details.

  You should have received a copy of the GNU General Public License
  along with this program; if not, write to the Free Software
  Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
*/
package net.sourceforge.czt.animation.eval.flatpred;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.SortedSet;
import java.util.TreeSet;

import net.sourceforge.czt.animation.eval.Envir;
import net.sourceforge.czt.animation.eval.ExprComparator;
import net.sourceforge.czt.animation.eval.result.EvalSet;
import net.sourceforge.czt.animation.eval.result.EvalSetVisitor;
import net.sourceforge.czt.base.ast.ListTerm;
import net.sourceforge.czt.base.ast.Term;
import net.sourceforge.czt.base.impl.ListTermImpl;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.Ann;
import net.sourceforge.czt.z.ast.Expr;
import net.sourceforge.czt.z.ast.ZName;

/** 
 */
public abstract class FlatEvalSet extends FlatPred
{  

}
