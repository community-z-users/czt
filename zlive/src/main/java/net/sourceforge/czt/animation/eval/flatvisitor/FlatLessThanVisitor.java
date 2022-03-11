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

package net.sourceforge.czt.animation.eval.flatvisitor;

import net.sourceforge.czt.animation.eval.flatpred.FlatLessThan;
import net.sourceforge.czt.util.Visitor;

/**
 * A FlatLessThan visitor.
 */
public interface FlatLessThanVisitor<R> extends Visitor<R>
{
  /**
   * Visits a FlatLessThan.
   * @param  term the FlatLessThan to be visited.
   * @return some kind of <code>Object</code>.
   */
  public R visitFlatLessThan(FlatLessThan term);
}
