/*
 * ZSideKickActions.java
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

import org.gjt.sp.jedit.*;
import sidekick.SideKickParsedData;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;

public class ZSideKickActions
{
  public static ParsedData getParsedData(View view)
  {
    final SideKickParsedData data = SideKickParsedData.getParsedData(view);
    if (data instanceof ParsedData) {
      return (ParsedData) data;
    }
    reportError(view, "Buffer hasn't been parsed by a CZT parser.");
    return null;
  }

  public static void toLatex(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key key = new Key(view.getBuffer().getPath(), LatexString.class);
      LatexString latex = (LatexString) manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding",
                               System.getProperty( "file.encoding"));
      buffer.setMode(latex.getExtension() + "latex");
      buffer.insert(0, latex.toString());
    }
  }

  public static void toOldLatex(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key key = new Key(view.getBuffer().getPath(), OldLatexString.class);
      OldLatexString latex = (OldLatexString) manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding",
                               System.getProperty( "file.encoding"));
      buffer.setMode(latex.getExtension() + "tex");
      buffer.insert(0, latex.toString());
    }
  }

  public static void toUnicode(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key key = new Key(view.getBuffer().getPath(), UnicodeString.class);
      UnicodeString unicode = (UnicodeString) manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding", "UTF-16");
      buffer.setMode(unicode.getExtension());
      buffer.insert(0, unicode.toString());
    }
  }

  public static void toXml(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key key = new Key(view.getBuffer().getPath(), XmlString.class);
      XmlString xml = (XmlString) manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding", "UTF-8");
      buffer.insert(0, xml.toString());
    }
  }

  public static WffHighlight getWffHighlight(View view)
  {
    for (Object o : view.getTextArea().getPainter().getExtensions()) {
      if (o instanceof WffHighlight) {
	return (WffHighlight) o;
      }
    }
    reportError(view, "No highlighter for wffs found.");
    return null;
  }

  public static void highlightNextWff(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      wffHighlight.next();
    }
  }

  public static void gotoDefinition(View view)
  {
    Term term = getWffHighlight(view).getSelectedWff();
    if (term instanceof ZRefName) {
      ZRefName refName = (ZRefName) term;
      DeclName declName = refName.getDecl();
      LocAnn locAnn = (LocAnn) declName.getAnn(LocAnn.class);
      if (locAnn != null && locAnn.getLoc() != null) {
        if (locAnn.getLoc().equals(view.getBuffer().getPath()) &&
            locAnn.getStart() != null) {
          view.getTextArea().setCaretPosition(locAnn.getStart());
        }
        else {
          String message = "Defined in " + locAnn.getLoc();
          if (locAnn.getLine() != null) message += " line " + locAnn.getLine();
          reportMessage(view, message);
        }
      }
      else {
        reportError(view,
                    "Could not find location information for declaring name");
      }
    }
    else {
      reportError(view, "Highlighted term is not a referencing name");
    }
  }

  public static void reportMessage(View view, String message)
  {
    view.getStatus().setMessage(message);
  }

  public static void reportError(View view, String message)
  {
    view.getStatus().setMessage(message);
    view.getToolkit().beep();
 }
}
