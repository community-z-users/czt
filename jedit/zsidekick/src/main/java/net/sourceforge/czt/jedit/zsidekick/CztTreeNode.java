/*
 * CztTreeNode.java
 * Copyright (C) 2006, 2007 Petra Malik
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
package net.sourceforge.czt.jedit.zsidekick;

import javax.swing.text.Position;
import javax.swing.tree.DefaultMutableTreeNode;

import org.gjt.sp.jedit.Buffer;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.util.Visitor;
import net.sourceforge.czt.session.Dialect;
import net.sourceforge.czt.z.ast.*;
import org.gjt.sp.jedit.jEdit;

public class CztTreeNode
  extends DefaultMutableTreeNode
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 4294068596351724151L;
private final static String SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.z.util.ShortDescriptionResourceBundle";
  private final static String ZPATT_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.zpatt.util.ShortDescriptionResourceBundle";
  private final static String CIRCUS_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.circus.util.ShortDescriptionResourceBundle";
  private final static String ZEVES_SHORT_DESCRIPTION_RESOURCE =
    "net.sourceforge.czt.zeves.util.ShortDescriptionResourceBundle";

  private final static Visitor<String> zShortDescriptionVisitor_ =
    new net.sourceforge.czt.zpatt.util.ZPattConcreteSyntaxDescriptionVisitor(
            SHORT_DESCRIPTION_RESOURCE, ZPATT_SHORT_DESCRIPTION_RESOURCE);
  private final static Visitor<String> circusShortDescriptionVisitor_ =
    new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor(
            SHORT_DESCRIPTION_RESOURCE, CIRCUS_SHORT_DESCRIPTION_RESOURCE);
  private final static Visitor<String> zevesShortDescriptionVisitor_ =
    new net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxDescriptionVisitor(
            SHORT_DESCRIPTION_RESOURCE, ZEVES_SHORT_DESCRIPTION_RESOURCE);

  private final static Visitor<String> zLongDescriptionVisitor_ =
    new net.sourceforge.czt.zpatt.util.ZPattConcreteSyntaxDescriptionVisitor();
  private final static Visitor<String> circusLongDescriptionVisitor_ =
    new net.sourceforge.czt.circus.util.CircusConcreteSyntaxDescriptionVisitor();
  private final static Visitor<String> zevesLongDescriptionVisitor_ =
    new net.sourceforge.czt.zeves.util.ZEvesConcreteSyntaxDescriptionVisitor();


  private final static Visitor<Term[]> getChildrenVisitor_ =
    new GetChildrenVisitor();

  //private Term term_;

  public CztTreeNode(Term term, Dialect dialect, Buffer buffer)
  {
    super(createAsset(term, dialect, buffer));
   // term_ = term;
    if (dialect.isExtensionOf(Dialect.CIRCUS) || 
        jEdit.getBooleanProperty(ZSideKickPlugin.PROPERTY_PREFIX + ZSideKickPlugin.PROP_SHOW_COMPLETE_TREE)) {
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

  private static CztAsset createAsset(Term term, Dialect dialect, Buffer buffer)
  {
    String name = term.accept(Dialect.CIRCUS.equals(dialect) ?
                              circusShortDescriptionVisitor_ :
                              (Dialect.ZEVES.equals(dialect) ?
                              zevesShortDescriptionVisitor_ :
                              zShortDescriptionVisitor_));
    if (name == null) {
      name = term.getClass().toString();
    }
    String description = term.accept(Dialect.CIRCUS.equals(dialect) ?
                                     circusLongDescriptionVisitor_ :
                                      (Dialect.ZEVES.equals(dialect) ?
                                    zevesLongDescriptionVisitor_ :
                                     zLongDescriptionVisitor_));
    if (term.hasAnn(TypeAnn.class))
    {
      TypeAnn tn = term.getAnn(TypeAnn.class);
      description += " : " + tn.getType().toString();
    }
    if (description == null) {
      description = term.getClass().toString();
    }
    final Position startPos = getStart(term, buffer);
    final Position endPos = getEnd(term, buffer);
    return new CztAsset(name, description, startPos, endPos);
  }

  static private Position getStart(Term term, Buffer buffer)
  {
    int start = 0;
    LocAnn locAnn = term.getAnn(LocAnn.class);
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
    LocAnn locAnn = term.getAnn(LocAnn.class);
    if (locAnn != null &&
        locAnn.getStart() != null && locAnn.getStart().intValue() >= 0 &&
        locAnn.getLength() != null && locAnn.getLength().intValue() >= 0 &&
        locAnn.getEnd().intValue() <= buffer.getLength()) {
      end = locAnn.getEnd().intValue();
    }
    return buffer.createPosition(end);
  }
}
