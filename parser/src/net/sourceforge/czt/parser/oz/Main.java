/**
   Copyright (C) 2003 Mark Utting
   This file is part of the czt project.

   The czt project contains free software;
   you can redistribute it and/or modify
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
package net.sourceforge.czt.parser.oz;

import java.io.*;
import java_cup.runtime.*;

import javax.swing.JFrame;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import java.util.*;

import net.sourceforge.czt.base.util.AstValidator;
import net.sourceforge.czt.oz.jaxb.JaxbValidator;
import net.sourceforge.czt.session.SectionManager;
import net.sourceforge.czt.z.ast.Spec;

/**
 * Opens a list of specifications and displays them as a tree.
 */
public class Main extends JPanel implements ActionListener
{
  //The dimensions of the window
  private static final int WIDTH = 700;
  private static final int HEIGHT = 600;

  //The specification being parsed.
  private Spec spec_ = null;

  public Main()
  {
    super(new BorderLayout());

    List libFiles = new ArrayList();
    /*
    libFiles.add("lib/prelude.tex");
    libFiles.add("lib/set_toolkit.tex");
    libFiles.add("lib/relation_toolkit.tex");
    libFiles.add("lib/function_toolkit.tex");
    libFiles.add("lib/number_toolkit.tex");
    libFiles.add("lib/sequence_toolkit.tex");
    libFiles.add("lib/standard_toolkit.tex");
    libFiles.add("lib/oz_toolkit.tex");
    */

    for (Iterator iter = libFiles.iterator(); iter.hasNext(); ) {
      String file = (String) iter.next();
      openAndAdd(file);
    }
  }

  /**
   *  Constructs the graph used by the model.
   */
  public TermModel getAst(String file)
  {
    try {
      //parse the specification
      Spec newSpec =
        (Spec) ParseUtils.parseLatexFile(file, new SectionManager());

      //validate the specification
      AstValidator validator = new JaxbValidator();
      validator.validate(newSpec);

      if (spec_ == null) {
        spec_ = newSpec;
      }
      else {
        spec_.getSect().addAll(newSpec.getSect());
      }

      JTreeVisitor visitor = new JTreeVisitor();
      return (TermModel) spec_.accept(visitor);
    }
    catch (Throwable e) {
      e.printStackTrace();
      return null;
    }
  }


  /**
   * Opens a file and adds it to the tree.
   */
  private void openAndAdd(String file)
  {
    //Construct the tree.
    AstTree tree = new AstTree(getAst(file));
    JScrollPane scrollPane = new JScrollPane(tree);
    scrollPane.setPreferredSize(new Dimension(WIDTH, HEIGHT));

    //Add everything to this panel.
    add(scrollPane, BorderLayout.CENTER);
  }

  /**
   * Create the GUI and show it.  For thread safety,
   * this method should be invoked from the
   * event-dispatching thread.
   */
  private static void createAndShowGUI(String [] args)
  {
    //Make sure we have nice window decorations.
    JFrame.setDefaultLookAndFeelDecorated(true);

    //Create and set up the window.
    JFrame frame = new JFrame("Ast");
    frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);

    //Create and set up the content pane.
    Main newContentPane = new Main();
    newContentPane.setOpaque(true); //content panes must be opaque
    frame.setContentPane(newContentPane);

    for (int i = 0; i < args.length; i++) {
      newContentPane.openAndAdd(args[i]);
    }

    //Display the window.
    frame.pack();
    frame.setVisible(true);
  }

  /**
   * Do nothing for the moment.
   */
  public void actionPerformed(ActionEvent ae)
  {
  }

  /**
   * Open the window and display the tree.
   */
  public static void main(final String[] args)
  {
    javax.swing.SwingUtilities.invokeLater(new Runnable() {
      public void run()
      {
        createAndShowGUI(args);
      }
    });
  }
}
