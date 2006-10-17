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

import java.io.StringWriter;

import org.gjt.sp.jedit.*;
import org.gjt.sp.jedit.textarea.*;
import sidekick.SideKickParsedData;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.oz.util.*;
import net.sourceforge.czt.print.util.*;
import net.sourceforge.czt.print.z.PrintUtils;
import net.sourceforge.czt.rules.*;
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
      final String text = type.accept(new PrintVisitor());
      final JEditTextArea textArea = view.getTextArea();
      final int caretPos = textArea.getCaretPosition();
      Selection selection = new Selection.Range(caretPos,
                                                caretPos + text.length());
      textArea.setSelectedText(text);
      textArea.setSelection(selection);
    }
  }

  public static void gotoDefinition(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof ZRefName) {
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
              RuleTable rules = (RuleTable)
                manager.get(new Key(section, RuleTable.class));
              if (rules != null) {
                ProofTree.createAndShowGUI(
                  ProverUtils.createPredSequent(pred, true),
                  rules,
                  manager,
                  section);
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
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

  public static void rewrite(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Expr ||
          term instanceof Pred) {
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            String section = zSect.getName();
            try {
              RuleTable rules = (RuleTable)
                manager.get(new Key(section, RuleTable.class));
              if (rules != null) {
                Prover prover = new SimpleProver(rules, manager, section);
                Term result;
                if (term instanceof Pred) {
                  result = Rewrite.rewriteOnce((Pred) term, prover);
                }
                else {
                   result = Rewrite.rewriteOnce((Expr) term, prover);
                }
                if (! replaceWff(term, result, view, manager, section)) {
                  reportError(view, "Unfolding failed");
                }
              }
              else {
                reportError(view, "Cannot find rules");
              }
            }
            catch (CommandException e) {
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        final String msg =
          "Highlighted term is neither an expression nor a predicate";
        reportError(view, msg);
      }
    }
  }

  public static void interactive_rewrite(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Expr ||
          term instanceof Pred) {
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            String section = zSect.getName();
            try {
              RuleTable rules = (RuleTable)
                manager.get(new Key(section, RuleTable.class));
              if (rules != null) {
                if (term instanceof Expr) {
                  ProofTree.createAndShowGUI(
                     ProverUtils.createRewritePredSequent((Expr) term, true),
                     rules,
                     manager,
                     section);
                }
                else {
                  ProofTree.createAndShowGUI(                     
                     ProverUtils.createRewritePredSequent((Pred) term, true),
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
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        final String msg =
          "Highlighted term is neither an expression nor a predicate";
        reportError(view, msg);
      }
    }
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
        String modeName = view.getBuffer().getMode().toString();
        if (modeName.endsWith("latex")) {
          PrintUtils.printLatex(newTerm, writer, manager, section);
        }
        else {
          PrintUtils.printUnicode(newTerm, writer,
                                  manager, section);
        }
      }
      catch (Exception e) {
        e.printStackTrace();
        net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter jaxbWriter =
          new net.sourceforge.czt.zpatt.jaxb.JaxbXmlWriter();
        jaxbWriter.write(newTerm, writer);
      }
      final String text = writer.toString();
      final JEditTextArea textArea = view.getTextArea();
      final int caretPos = textArea.getCaretPosition();
      textArea.setSelection(selection);
      textArea.setSelectedText(text);
      selection = new Selection.Range(start,
                                      start + text.length());
      textArea.setSelection(selection);
      return true;
    }
    return false;
  }

  public static void unfold(View view)
  {
    WffHighlight wffHighlight = getWffHighlight(view);
    if (wffHighlight != null) {
      Term term = wffHighlight.getSelectedWff();
      if (term instanceof Expr) {
        ParsedData parsedData = getParsedData(view);
        if (parsedData != null) {
          SectionManager manager = parsedData.getManager();
          ZSect zSect = wffHighlight.findZSectForCurrentWff();
          if (zSect != null) {
            String section = zSect.getName();
            try {
              SectionManager ruleManager = new SectionManager("zpatt");
              Source unfoldSource = new UrlSource(RuleUtils.getUnfoldRules());
              ruleManager.put(new Key("unfold", Source.class), unfoldSource);
              RuleTable rules = (RuleTable)
                ruleManager.get(new Key("unfold", RuleTable.class));
              if (rules != null) {
                Prover prover = new SimpleProver(rules, manager, section);
                Term result = Rewrite.rewriteOnce((Expr) term, prover);
                if (! replaceWff(term, result, view, manager, section)) {
                  reportError(view, "Unfolding failed");
                }
              }
              else {
                reportError(view, "Cannot find unfold rules");
              }
            }
            catch (CommandException e) {
              reportError(view, "Cannot get rule table");
            }
          }
          else {
            reportError(view, "Cannot find Z section for selected term");
          }
        }
      }
      else {
        reportError(view, "Highlighted term is not an expression");
      }
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
