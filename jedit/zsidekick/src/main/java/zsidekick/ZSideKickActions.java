/*
 * ZSideKickActions.java
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
package zsidekick;

import java.io.File;
import java.io.StringWriter;

import java.util.Iterator;
import javax.swing.JOptionPane;
import net.sourceforge.czt.dc.z.DomainCheckUtils;
import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.Buffer;
import org.gjt.sp.jedit.textarea.*;
import sidekick.SideKickParsedData;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.print.z.*;

import net.sourceforge.czt.rules.CopyVisitor;
import net.sourceforge.czt.rules.RuleTable;
import net.sourceforge.czt.rules.UnboundJokerException;
import net.sourceforge.czt.rules.rewriter.RewriteVisitor;
import net.sourceforge.czt.rules.prover.ProofTree;
import net.sourceforge.czt.rules.prover.ProverUtils;
import net.sourceforge.czt.rules.rewriter.Strategies;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;

public class ZSideKickActions
  implements PrintPropertiesKeys
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
      Key<LatexString> key = new Key<LatexString>(view.getBuffer().getPath(), LatexString.class);
      LatexString latex = manager.get(key);
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
      Key<OldLatexString> key = new Key<OldLatexString>(view.getBuffer().getPath(), OldLatexString.class);
      OldLatexString latex = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding",
                               System.getProperty( "file.encoding"));
      buffer.setMode(latex.getExtension() + "latex");
      buffer.insert(0, latex.toString());
    }
  }

  public static void toUnicode(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      SectionManager manager = parsedData.getManager();
      Key<UnicodeString> key = new Key<UnicodeString>(view.getBuffer().getPath(), UnicodeString.class);
      UnicodeString unicode = manager.get(key);
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
      Key<XmlString> key = new Key<XmlString>(view.getBuffer().getPath(), XmlString.class);
      XmlString xml = manager.get(key);
      Buffer buffer = jEdit.newFile(view);
      buffer.setStringProperty("encoding", "UTF-8");
      buffer.insert(0, xml.toString());
    }
  }
  
  public static void domainCheck(View view)
    throws CommandException
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) 
    {      
      SectionManager manager = parsedData.getManager();
      Buffer buffer = parsedData.getBuffer();
      final String bufferPath = buffer.getPath(); // full qualified file name
      final File file = new File(bufferPath);
      final String name = file.getName(); // just last name of file
      final String path = file.getParent() != null ? file.getParent() : "."; // just the file directory
/*
      // TODO: DEBUG ONLY = REMOVE LATER
      if (path != null) {
        String oldpath = manager.getProperty("czt.path");
        String localpath = ((oldpath == null || oldpath.isEmpty() || oldpath.equals(path)) ? 
          path : oldpath  + File.pathSeparator + path);
        assert localpath != null;
        manager.setProperty("czt.path", localpath);
        JOptionPane.showMessageDialog(view, "CZT-path = " + localpath.replace(';', '\n'));
      }
      JOptionPane.showMessageDialog(view, "Buffer path = " + buffer.getPath() + 
        ";\nBuffer name = " + buffer.getName() +  // same as file.getName()
        ";\nFile path = " + path +
        ";\nFile name = " + name);      
      StringBuilder commands = new StringBuilder("SectionManager.Commands = {");
      Iterator<Class<?>> it = manager.getCommandKeys();
      while (it.hasNext())
      {
        Class<?> cls = it.next();
        Command cmd = manager.getCommand(cls);
        commands.append("\n\t " + cls.getSimpleName() + " = " + cmd.getClass().getName());
      }      
      commands.append("}");
      JOptionPane.showMessageDialog(view, commands.toString());
      // END TODO
*/
      try
      {
        /* OKAY = creates a new (unnamed) buffer with results -> doesn't parse
        DomainCheckUtils.getDCUtils().setSectionManager(manager);
        DomainCheckUtils.getDCUtils().printToFile(null, path, Markup.LATEX);
        CztPrintString result = DomainCheckUtils.getDCUtils().domainCheck(file);
        Buffer bufferDC = jEdit.newFile(view, path);
        jEdit.openFile(view, path)
        bufferDC.setStringProperty("encoding", System.getProperty( "file.encoding"));
        String mode = Markup.getMarkup(name).equals(Markup.LATEX) ? "latex" : "";
        buffer.setMode(result.getExtension() + mode);
        bufferDC.insert(0, result.toString());
        */
        final String dcFileName = DomainCheckUtils.getDCFilename(name);
        DomainCheckUtils.getDCUtils().setSectionManager(manager);
        DomainCheckUtils.getDCUtils().domainCheckToFile(file);
        Buffer bufferDC = jEdit.openFile(view, dcFileName);
        bufferDC.setStringProperty("encoding", System.getProperty( "file.encoding"));
        String mode = Markup.getMarkup(name).equals(Markup.LATEX) ? "latex" : "";
        buffer.setMode(manager.getDialect() + mode);
      }
      catch (CommandException e)
      {
        e.printStackTrace(System.err);
        //pwriter.close();        
        JOptionPane.showMessageDialog(view, "Could not calculate domain checks for " + name
          + ". Detailed error message:\n" + e.getMessage(), "Command Error!", JOptionPane.ERROR_MESSAGE);
      }
    }
  }

  public static WffHighlight getWffHighlight(View view)
  {
    ParsedData parsedData = getParsedData(view);
    if (parsedData != null) {
      return parsedData.getWffHighlight();
    }
    return null;
  }

  public static void highlightNextWff(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      wffHighlight.next();
      Term term = wffHighlight.getSelectedWff();
      if (term != null) {
        String message;
        ParsedData parsedData = getParsedData(view);
        if (parsedData == null)
          message = term.accept(new net.sourceforge.czt.z.util.ConcreteSyntaxDescriptionVisitor());
        else
        {
          Buffer buffer = getParsedData(view).getBuffer();
          Mode mode = buffer.getMode();
          if (mode != null && mode.getName() != null && mode.getName().startsWith("circus"))
            message = term.accept(new net.sourceforge.czt.circus.util.ConcreteSyntaxDescriptionVisitor());
          else
            message = term.accept(new net.sourceforge.czt.z.util.ConcreteSyntaxDescriptionVisitor());
        }
        view.getStatus().setMessage(message);
      }
    }
  }

  public static Term getSelectedTerm(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      return wffHighlight.getSelectedWff();
    }
    return null;
  }

  public static Type getTypeForCurrentWff(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term != null) {
        TypeAnn typeAnn = (TypeAnn) term.getAnn(TypeAnn.class);
        if (typeAnn != null) return typeAnn.getType();
        else reportError(view, "Selected formula doesn't have a type");
      }
      else reportError(view, "No formula selected");
    }
    return null;
  }

  public static void insertTypeForCurrentWff(View view)
  {
    Type type = getTypeForCurrentWff(view);
    if (type != null) {
      net.sourceforge.czt.base.util.PrintVisitor visitor = null;
      ParsedData parsedData = getParsedData(view);
      if (parsedData == null)
        visitor = new net.sourceforge.czt.z.util.PrintVisitor();
      else
      {
        Buffer buffer = parsedData.getBuffer();
        Mode mode = buffer.getMode();
        if (mode == null)
          visitor = new net.sourceforge.czt.z.util.PrintVisitor();
        else if (mode.getName().startsWith("circus"))
          visitor = new net.sourceforge.czt.circus.util.PrintVisitor();
        else if (mode.getName().startsWith("oz"))
          visitor = new net.sourceforge.czt.oz.util.PrintVisitor();
        else //if (mode.getName().startsWith("z"))
          visitor = new net.sourceforge.czt.z.util.PrintVisitor();
      }
      final String text = type.accept(visitor);
      final JEditTextArea textArea = view.getTextArea();
      final int caretPos = textArea.getCaretPosition();
      Selection selection = new Selection.Range(caretPos,
                                                caretPos + text.length());
      textArea.setSelectedText(text);
      textArea.setSelection(selection);
    }
  }

  /*
  public static void gotoDefinition(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof ZName) {
        ZRefName refName = (ZRefName) term;
        DeclName declName = refName.getDecl();
        if (declName != null) {
          LocAnn locAnn = (LocAnn) declName.getAnn(LocAnn.class);
          if (locAnn != null && locAnn.getLoc() != null) {
            if (locAnn.getLoc().equals(view.getBuffer().getPath()) &&
                locAnn.getStart() != null) {
              int pos = locAnn.getStart().intValue();
              view.getTextArea().setCaretPosition(pos);
            }
            else {
              String message = "Defined in " + locAnn.getLoc();
              if (locAnn.getLine() != null)
                message += " line " + locAnn.getLine();
              reportMessage(view, message);
            }
          }
          else {
            final String message =
              "Could not find location information for declaring name";
            reportError(view, message);
          }
        }
        else {
          final String message = "Could not find a declaration";
          reportError(view, message);
        }
      }
      else {
        reportError(view, "Highlighted term is not a referencing name");
      }
    }
  }
  */

  public static void prove(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Pred) {
        Pred pred = (Pred) term;
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            final String section = zSect.getName();
            try {
              RuleTable rules = 
                manager.get(new Key<RuleTable>(section, RuleTable.class));
              if (rules != null) {
                ProofTree.createAndShowGUI(
                  ProverUtils.createSequent(pred, true),
                  rules,
                  manager,
                  section);
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
              e.printStackTrace();
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        reportError(view, "Highlighted term is not a predicate");
      }
    }
  }

  public static void innermost(View view)
    throws UnboundJokerException
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      CopyVisitor copy = new CopyVisitor(ProverUtils.FACTORY);
      term = term.accept(copy);
      ParsedData parsedData = getParsedData(view);
      if (parsedData != null) {
        SectionManager manager = parsedData.getManager();
        ZSect zSect = wffHighlight.findZSectForCurrentWff();
        if (zSect != null) {
          String section = zSect.getName();
          try {
            RuleTable rules = 
              manager.get(new Key<RuleTable>(section, RuleTable.class));
            if (rules != null) {
              RewriteVisitor rewriter =
                new RewriteVisitor(rules, manager, section);
              Term result = Strategies.innermost(term, rewriter);
              if (! replaceWff(term, result, view, manager, section)) {
                reportError(view, "Rewriting failed");
              }
            }
            else {
              reportError(view, "Cannot find rules");
            }
          }
          catch (CommandException e) {
            e.printStackTrace();
            reportError(view, "Cannot get rule table");
          }
        }
        else {
          reportError(view, "Cannot find Z section for selected term");
        }
      }
    }
  }

  public static void interactive_rewrite(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Expr ||
          term instanceof Pred ||
          term instanceof SchText) {
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            String section = zSect.getName();
            try {
              RuleTable rules = 
                manager.get(new Key<RuleTable>(section, RuleTable.class));
              if (rules != null) {
                if (term instanceof Expr) {
                  ProofTree.createAndShowGUI(
                     ProverUtils.createRewriteSequent((Expr) term, true),
                     rules,
                     manager,
                     section);
                }
                else if (term instanceof Pred) {
                  ProofTree.createAndShowGUI(
                     ProverUtils.createRewriteSequent((Pred) term, true),
                     rules,
                     manager,
                     section);
                }
                else {
                  ProofTree.createAndShowGUI(                     
                     ProverUtils.createRewriteSequent((SchText) term, true),
                     rules,
                     manager,
                     section);
                }
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
              e.printStackTrace();
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        final String msg = "Highlighted term is neither a predicate " +
          "nor an expression nor a schema text";
        reportError(view, msg);
      }
    }
  }

  public static int getColumn(int pos, View view)
  {
    final JEditTextArea textArea = view.getTextArea();
    final int line = textArea.getLineOfOffset(pos);
    return pos - textArea.getLineStartOffset(line);
  }

  private static Markup getMarkup(View view)
  {
    String modeName = view.getBuffer().getMode().toString();
    return modeName.endsWith("latex") ? Markup.LATEX : Markup.UNICODE;
  }

  public static boolean replaceWff(Term oldTerm, Term newTerm, View view,
                                   SectionManager manager, String section)
  {
    if (newTerm != null && oldTerm != newTerm) {
      final LocAnn locAnn = (LocAnn) oldTerm.getAnn(LocAnn.class);
      final int start = locAnn.getStart().intValue();
      Selection selection =
        new Selection.Range(start,
                            start + locAnn.getLength().intValue());
      StringWriter writer = new StringWriter();
      try {
        PrintUtils.print(newTerm, writer, manager, section, getMarkup(view));
      }
      catch (Exception e) {
        e.printStackTrace();
        net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter jaxbWriter =
          new net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter();
        jaxbWriter.write(newTerm, writer);
      }
      replaceSelection(view, selection, writer.toString());
      return true;
    }
    return false;
  }

  public static void prettyPrint(View view, int width)
    throws Exception
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      ParsedData parsedData = getParsedData(view);
      if (parsedData != null) {
        SectionManager manager = parsedData.getManager();
        manager.setProperty(PROP_TXT_WIDTH, "" + width);
        ZSect zSect = wffHighlight.findZSectForCurrentWff();
        if (zSect != null) {
          String section = zSect.getName();
          final LocAnn locAnn = (LocAnn) term.getAnn(LocAnn.class);
          final int start = locAnn.getStart().intValue();
          Selection selection =
            new Selection.Range(start,
                                start + locAnn.getLength().intValue());
          StringWriter writer = new StringWriter();
          PrintUtils.print(term, writer, manager, section, getMarkup(view));
          replaceSelection(view, selection, writer.toString());
        }
      }
    }
  }

  public static void replaceSelection(View view,
                                      Selection selection,
                                      String text)
  {
    final JEditTextArea textArea = view.getTextArea();
    textArea.setSelection(selection);
    textArea.setSelectedText(text);
    int start = selection.getStart();
    Selection newSelection = new Selection.Range(start, start + text.length());
    textArea.setSelection(newSelection);
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
