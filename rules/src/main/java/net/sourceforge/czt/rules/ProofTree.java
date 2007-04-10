/*
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

package net.sourceforge.czt.rules;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.tree.*;

import net.sourceforge.czt.base.ast.*;
import net.sourceforge.czt.print.util.*;
//import net.sourceforge.czt.print.zpatt.PrintUtils;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.z.ast.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;

public class ProofTree
  extends JTree
{
  private JFrame frame_;
  private RuleTable rules_;
  private SectionManager manager_;
  private String section_;

  public ProofTree(JFrame frame,
                   PredSequent sequent,
                   RuleTable rules,
                   SectionManager manager,
                   String section)
  {
    frame_ = frame;
    rules_ = rules;
    manager_ = manager;
    section_ = section;

    TreeNode rootNode = new ProofNode(sequent);
    setModel(new DefaultTreeModel(rootNode));
    getSelectionModel().setSelectionMode(
                 TreeSelectionModel.SINGLE_TREE_SELECTION);
    addMouseListener(new PopupListener());
    DefaultTreeCellRenderer renderer = new Renderer();
    setCellRenderer(renderer);
  }

  public DefaultTreeModel getModel()
  {
    return (DefaultTreeModel) super.getModel();
  }

  /**
   * Doesn't change the children.
   */
  private boolean apply(Rule rule, ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor visitor = new CopyVisitor(factory);
    Rule copiedRule = (Rule) rule.accept(visitor);
    System.err.println("Rule jokers:");
    ProverUtils.printJokers(copiedRule);
    return SimpleProver.apply(copiedRule, sequent);
  }

  private void apply(String name, ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    if (apply(rules_.getRule(name), node)) {
      substituteNode(node, new ProofNode(sequent));
    }
  }

  private DefaultMutableTreeNode createNode(Sequent s)
  {
    if (s instanceof PredSequent) return new ProofNode((PredSequent) s);
    if (s instanceof ProverProviso) return new ProvisoNode((ProverProviso) s);
    throw new RuntimeException("Unexpted sequent " + s.getClass());
  }

  private void whyNot(String name, ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor visitor = new CopyVisitor(factory);
    Rule copiedRule = (Rule) rules_.getRule(name).accept(visitor);
    try {
      SimpleProver.apply2(copiedRule, sequent);
    }
    catch (RuleApplicationException e) {
      try {
        StringWriter sw = new StringWriter();
        PrintWriter pw = new PrintWriter(sw);
        e.printStackTrace(pw);
        sw.close();
        JTextArea textArea = new JTextArea(sw.toString());
        JScrollPane scrollPane = new JScrollPane(textArea);

        JFrame frame = new JFrame("Reason");
        frame.setPreferredSize(new Dimension(800, 600));
        frame.getContentPane().add(scrollPane, BorderLayout.CENTER);
        frame.pack();
        frame.setVisible(true);
      }
      catch (IOException ioe) {
        throw new RuntimeException(ioe);
      }
    }
  }

  private void prove(ProofNode node)
  {
    SimpleProver prover = new SimpleProver(rules_, manager_, section_);
    PredSequent sequent = node.getSequent();
    if (prover.prove(sequent)) {
      substituteNode(node, new ProofNode(sequent));
    }
  }

  private void substituteNode(ProofNode node, ProofNode newNode)
  {
    DefaultMutableTreeNode parent = (DefaultMutableTreeNode)
      node.getParent();
    if (parent != null) {
      int index = getModel().getIndexOfChild(parent, node);
      getModel().removeNodeFromParent(node);
      getModel().insertNodeInto(newNode, parent, index);
    }
    else {
      getModel().setRoot(newNode);
    }
    if (newNode.getChildCount() > 0) {
      DefaultMutableTreeNode n = (DefaultMutableTreeNode)
        newNode.getChildAt(0);
      scrollPathToVisible(new TreePath(n.getPath()));
    }
  }

  private void reset(PredSequent sequent)
  {
    if (sequent.getDeduction() != null) {
      java.util.List<Binding> bindings = new java.util.ArrayList<Binding>();
      ProverUtils.collectBindings(sequent, bindings);
      for (Binding binding : bindings) {
        System.err.println(binding.getChildren()[0]);
      }
      System.err.println("Before resetting ");
      ProverUtils.printJokers(sequent);
      System.err.println("After resetting ");
      ProverUtils.printJokers(sequent);
      sequent.setDeduction(null);
    }
  }

  private void reset(ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    reset(sequent);
    substituteNode(node, new ProofNode(sequent));
  }


  public static void createAndShowGUI(PredSequent sequent,
                                      RuleTable rules,
                                      SectionManager manager,
                                      String section)
  {
    JFrame.setDefaultLookAndFeelDecorated(true);
    JFrame frame = new JFrame("ProofTree");
    // frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    ProofTree tree = new ProofTree(frame,
                                   sequent,
                                   rules,
                                   manager,
                                   section);
    tree.setFont(new Font("CZT", Font.PLAIN, 12));
    ToolTipManager.sharedInstance().registerComponent(tree);
    JScrollPane scrollPane = new JScrollPane(tree);
    frame.setPreferredSize(new Dimension(500, 300));
    frame.getContentPane().add(scrollPane);
    frame.pack();
    frame.setVisible(true);
  }

  class PopupListener
    extends MouseAdapter
  {
    public void mousePressed(MouseEvent e)
    {
      int selRow = getRowForLocation(e.getX(), e.getY());
      TreePath selPath = getPathForLocation(e.getX(), e.getY());
      if(selRow != -1) {
        if(e.getButton() == MouseEvent.BUTTON3) {
          Object o = selPath.getLastPathComponent();
          if (o instanceof ProofNode) {
            menu((ProofNode) o).show(e.getComponent(), e.getX(), e.getY());
          }
          else if (o instanceof ProvisoNode) {
            final ProvisoNode pn = (ProvisoNode) o;
            final ProverProviso p = (ProverProviso) pn.getProviso();
            if (! ProverProviso.Status.PASS.equals(p.getStatus())) {
              JPopupMenu popup = new JPopupMenu();
              JMenuItem menuItem = new JMenuItem("Check proviso");
              menuItem.addActionListener(new ActionListener() {
                  public void actionPerformed(ActionEvent e) {
                    p.check(manager_, section_);
                    getModel().nodeChanged(pn);
                  }
                });
              popup.add(menuItem);
              popup.show(e.getComponent(), e.getX(), e.getY());
            }
          }
        }
      }
    }

    private JPopupMenu menu(final ProofNode node)
    {
      final PredSequent sequent = (PredSequent) node.getUserObject();
      JPopupMenu popup = new JPopupMenu();
      if (sequent.getDeduction() != null) {
        JMenuItem menuItem = new JMenuItem("Undo rule application");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
              reset(node);
            }
          });
        popup.add(menuItem);
      }
      else {
        JMenuItem menuItem = new JMenuItem("Auto prove");
        menuItem.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
              prove(node);
            }
          });
        popup.add(menuItem);
        JMenu apply = new JMenu("Apply");
        popup.add(apply);
        JMenu whyNot = new JMenu("Why not");
        popup.add(whyNot);
        for (Iterator<Rule> iter = rules_.iterator(); iter.hasNext();) {
          final Rule rule = iter.next();
          System.err.println("Try rule " + rule.getName());
          if (apply(rule, node)) {
            System.err.println(node.toString());
            menuItem = new JMenuItem("Rule " + rule.getName());
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                  apply(rule.getName(), node);
                }
              });
            apply.add(menuItem);
          }
          else {
            menuItem = new JMenuItem("Rule " + rule.getName());
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                  whyNot(rule.getName(), node);
                }
              });
            whyNot.add(menuItem);
          }
          reset(sequent);
          System.err.println("resetting ... to " + node.toString());
        }
      }
      JMenuItem print = new JMenuItem("Print");
      print.addActionListener(new ActionListener() {
          public void actionPerformed(ActionEvent e) {
            System.err.println(node.toString());
          }
        });
      popup.add(print);
      return popup;
    }
  }

  class ProofNode
    extends DefaultMutableTreeNode
  {
    public ProofNode(PredSequent sequent)
    {
      super(sequent);
      Deduction ded = sequent.getDeduction();
      if (ded != null) {
        for (Sequent s : ded.getSequent()) {
          insert(createNode(s), getChildCount());
        }
      }
    }

    public PredSequent getSequent()
    {
      return (PredSequent) getUserObject();
    }

    public boolean isClosed()
    {
      if (getSequent().getDeduction() == null) return false;
      for (Enumeration<TreeNode> e = children();
           e.hasMoreElements() ;) {
        TreeNode node = e.nextElement();
        if (node instanceof ProofNode) {
          if (! ((ProofNode) node).isClosed()) return false;
        }
        else if (node instanceof ProvisoNode) {
          if (! ((ProvisoNode) node).isClosed()) return false;
        }
        else {
          throw new RuntimeException("Unexpected node " + node.getClass());
        }
      }
      return true;
    }

    public String toString() {
      try {
        StringWriter writer = new StringWriter();
        PrintUtils.printUnicode(getSequent().getPred(), writer,
                                manager_, section_);
        return "\u22A2 " + writer.toString();
      }
      catch (Exception e) {
        e.printStackTrace();
        return getSequent().toString();
      }
    }
  }

  class ProvisoNode
    extends DefaultMutableTreeNode
  {
    public ProvisoNode(ProverProviso proviso)
    {
      super(proviso);
    }

    public ProverProviso getProviso()
    {
      return (ProverProviso) getUserObject();
    }

    public boolean isClosed()
    {
      return  ProverProviso.Status.PASS.equals(getProviso().getStatus());
    }

    public String toString() {
      try {
        StringWriter writer = new StringWriter();
        PrintUtils.printUnicode(getProviso(), writer, manager_, section_);
        return writer.toString();
      }
      catch (Exception e) {
        e.printStackTrace();
        return getProviso().toString();
      }
    }
  }

  class Renderer
    extends DefaultTreeCellRenderer
  {
    public Component getTreeCellRendererComponent(JTree tree,
                                                  Object value,
                                                  boolean sel,
                                                  boolean expanded,
                                                  boolean leaf,
                                                  int row,
                                                  boolean hasFocus)
    {
      super.getTreeCellRendererComponent(tree, value, sel,
                                         expanded, leaf, row,
                                         hasFocus);
      if (value instanceof ProvisoNode) {
        setToolTipText("Proviso");
        ProvisoNode node = (ProvisoNode) value;
        if (node.isClosed()) {
          setIcon(new ImageIcon(getClass().getResource("images/ok.jpg")));
        }
        else {
          setIcon(new ImageIcon(getClass().getResource("images/question.jpg")));
        }
      }
      else if (value instanceof ProofNode) {
        ProofNode node = (ProofNode) value;
        PredSequent sequent = node.getSequent();
        if (sequent.getDeduction() != null) {
          setToolTipText("Rule " + sequent.getDeduction().getName());
        }
        else {
          setToolTipText("No rule has been applied to this sequent");
        }
        if (node.isClosed()) {
          setIcon(new ImageIcon(getClass().getResource("images/ok.jpg")));
        }
        else {
          setIcon(new ImageIcon(getClass().getResource("images/question.jpg")));
        }
      }
      return this;
    }
  }
}
