/*
 * CztTreeNode.java
 * Copyright (C) 2006 Petra Malik
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 */
package zsidekick;

import javax.swing.text.Position;
import javax.swing.tree.DefaultMutableTreeNode;

import org.gjt.sp.jedit.Buffer;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.z.ast.*;

public class CztTreeNode
  extends DefaultMutableTreeNode
{
  private final static String SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.z.util.ShortDescriptionResourceBundle";
  private final static String ZPATT_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.zpatt.util.ShortDescriptionResourceBundle";
  private final static String CIRCUS_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.circus.util.ShortDescriptionResourceBundle";

  private final static Visitor<String> zShortDescriptionVisitor_ =
    new net.sourceforge.czt.zpatt.util.ConcreteSyntaxDescriptionVisitor(
            SHORT_DESCRIPTION_RESOURCE, ZPATT_SHORT_DESCRIPTION_RESOURCE);
  private final static Visitor<String> circusShortDescriptionVisitor_ =
    new net.sourceforge.czt.circus.util.ConcreteSyntaxDescriptionVisitor(
            SHORT_DESCRIPTION_RESOURCE, CIRCUS_SHORT_DESCRIPTION_RESOURCE);

  private final static Visitor<String> zLongDescriptionVisitor_ =
    new net.sourceforge.czt.zpatt.util.ConcreteSyntaxDescriptionVisitor();
  private final static Visitor<String> circusLongDescriptionVisitor_ =
    new net.sourceforge.czt.circus.util.ConcreteSyntaxDescriptionVisitor();

  private final static Visitor<Term[]> getChildrenVisitor_ =
    new GetChildrenVisitor();

  private Term term_;

  public CztTreeNode(Term term, String dialect, Buffer buffer)
  {
    super(new CztAsset(term.accept("circus".equals(dialect) ? circusShortDescriptionVisitor_ : zShortDescriptionVisitor_),
                       term.accept("circus".equals(dialect) ? circusLongDescriptionVisitor_ : zLongDescriptionVisitor_),
                       getStart(term, buffer),
                       getEnd(term, buffer)));
    term_ = term;
    if (buffer.getBooleanProperty("zsidekick.show-complete-tree")) {
      Object[] children = term.getChildren();
      for (Object o : children) {
        if (o instanceof Term) {
          add(new CztTreeNode((Term) o, dialect, buffer));
        }
      }
    }
    else {
      Term[] children = term.accept(getChildrenVisitor_);
      for (Term child : children) {
        add(new CztTreeNode(child, dialect, buffer));
      }
    }
  }

  static private Position getStart(Term term, Buffer buffer)
  {
    int start = 0;
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null) {
      if (locAnn.getStart() != null) {
        start = locAnn.getStart().intValue();
      }
      else {
        try {
          start = buffer.getLineStartOffset(locAnn.getLine().intValue() - 1)
            + locAnn.getCol().intValue();
        }
        catch(IndexOutOfBoundsException e) {
        }
        catch(NullPointerException e) {
        }
      }
    }
    return buffer.createPosition(start);
  }

  private static Position getEnd(Term term, Buffer buffer)
  {
    int end = buffer.getLength();
    LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
    if (locAnn != null &&
        locAnn.getStart() != null && locAnn.getStart().intValue() >= 0 &&
        locAnn.getLength() != null && locAnn.getLength().intValue() >= 0 &&
        locAnn.getEnd().intValue() <= buffer.getLength()) {
      end = locAnn.getEnd().intValue();
    }
    return buffer.createPosition(end);
  }
}
