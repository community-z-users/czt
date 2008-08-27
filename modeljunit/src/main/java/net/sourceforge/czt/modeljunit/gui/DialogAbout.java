
package net.sourceforge.czt.modeljunit.gui;

import java.awt.BorderLayout;
import java.awt.Frame;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;

import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.JTextArea;

import net.sourceforge.czt.modeljunit.Model;

@SuppressWarnings("serial")
public class DialogAbout extends JDialog
{
  public DialogAbout(Frame owner)
  {
    super(owner, "About", true);
    setLayout(new BorderLayout());
    String msg = new String("ModelJUnit GUI\n" + " Director: Mark Utting \n"
        + " Coding: Rong Yang\n" + " Version: " + Model.getVersion());
    JTextArea txt = new JTextArea(msg);
    txt.setEditable(false);
    txt.setBackground(this.getBackground());
    final JButton butOkey = new JButton("OK");
    ActionListener exit = new ActionListener()
    {
      public void actionPerformed(ActionEvent e)
      {
        dispose();
      }
    };
    butOkey.addActionListener(exit);
    JPanel p = new JPanel();

    WindowListener wl = new WindowAdapter()
    {
      public void windowOpened(WindowEvent e)
      {
        butOkey.requestFocus();
      }
    };
    this.addWindowListener(wl);
    p.add(txt, BorderLayout.CENTER);
    p.add(butOkey, BorderLayout.SOUTH);
    getContentPane().add(p);
    pack();
    setResizable(false);
  }
}
