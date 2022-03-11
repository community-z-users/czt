/*
 GAfFE - A (G)raphical (A)nimator (F)ront(E)nd for Z - Part of the CZT Project.
 Copyright 2003 Nicholas Daley

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

package net.sourceforge.czt.animation.gui;

import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.beans.Beans;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;

import javax.swing.JButton;
import javax.swing.JFrame;
import javax.swing.JLabel;

import net.sourceforge.czt.animation.gui.design.DesignerCore;

/**
 ** The main class for GAfFE.
 ** Provides the main program, and the ability to select animate or design mode.
 */
public class Gaffe extends JFrame
{
  /**
	 * 
	 */
	private static final long serialVersionUID = 3146587470927203321L;

protected Gaffe()
  {
    this(new String[0]);
  };

  protected Gaffe(final String[] args)
  {
    setSize(300, 300);
    setTitle("GAfFE");
    setLocation(300,300);
    String iconPath = "net/sourceforge/czt/animation/gui/gaffe.gif";
    setIconImage(getToolkit().getImage(ClassLoader.getSystemResource(iconPath)));
    getContentPane().setLayout(new GridLayout(4, 1));
    getContentPane().add(
        new JLabel("Please choose animate or design mode:", JLabel.CENTER));
    JButton animate, design, quit;
    animate = new JButton("Animate");
    getContentPane().add(animate);
    animate.setMnemonic(KeyEvent.VK_A);
    design = new JButton("Design");
    getContentPane().add(design);
    design.setMnemonic(KeyEvent.VK_D);
    quit = new JButton("Quit");
    getContentPane().add(quit);
    quit.setMnemonic(KeyEvent.VK_Q);
    design.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent e)
      {
        dispose();
        DesignerCore.run(args);
      };
    });
    animate.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent e)
      {
        if (AnimatorCore.run(args) == 0)
          dispose();
      };
    });
    quit.addActionListener(new ActionListener()
    {
      public void actionPerformed(ActionEvent e)
      {
        dispose();
        System.exit(0);
      };
    });
    setDefaultCloseOperation(DISPOSE_ON_CLOSE);
  };

  private static String[] getArgsTail(String[] args)
  {
    //chop off args[0]
    return (String[]) Arrays.asList(args).subList(1, args.length).toArray(
        new String[0]);
  };

  public static void main(String[] args)
  {
    if (args.length > 0)
      if (args[0].equals("--design") || args[0].equals("-design")) {
        DesignerCore.run(getArgsTail(args));
        return;
      }
      else if (args[0].equals("--animate") || args[0].equals("-animate")) {
        if (AnimatorCore.run(getArgsTail(args)) < 0)
          System.exit(0);
        return;
      }
      else if (args[0].equals("--help") || args[0].equals("-help")) {
        System.err.println("Usage: gaffe [--design|--animate] <arguments>");
        System.err.println("  or:  gaffe --help");
        System.err.println();
        System.err.println("  --design\tdesign mode");
        System.err.println("  --animate\tanimate mode");
        System.err.println("  --help\tthis help page");
        System.err.println("  [otherwise]\trun gui chooser");
        return;
      };
    if (Beans.isGuiAvailable())
      (new Gaffe(args)).setVisible(true);
    else {
      BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
      System.err.println("Please choose (a)nimate, or (d)esign mode, "
          + "or (q)uit:");
      while (true) {
        String input;
        try {
          input = br.readLine().toLowerCase();
        } catch (IOException e) {
          System.err.println("IO Exception while reading input");
          System.err.println(e);
          return;
        };

        if (input.equals("q"))
          return;
        else if (input.equals("a")) {
          System.err
              .println("At present animate mode hasn't been implemented.");//Because there is no GUI.
          //xxx   AnimatorCore.run(args);
        }
        else if (input.equals("d")) {
          DesignerCore.run(args);
          return;
        }
      }
    }
  };
};
