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
  private boolean apply(RulePara rulePara, ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor visitor = new CopyVisitor(factory);
    RulePara copiedRulePara = (RulePara) rulePara.accept(visitor);
    return SimpleProver.apply(copiedRulePara, sequent);
  }

  private void apply(String name, ProofNode node)
  {
    PredSequent sequent = node.getSequent();
    if (apply(rules_.getRulePara(name), node)) {
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
    Rule copiedRule = (Rule) rules_.getRulePara(name).accept(visitor);
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
      ProverUtils.reset(bindings);
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
          else if (o instanceof Proviso2Node) {
            final Proviso2Node pn = (Proviso2Node) o;
            if (! pn.isClosed()) {
              JPopupMenu popup = new JPopupMenu();
              JMenuItem menuItem = new JMenuItem("Check proviso");
              menuItem.addActionListener(new ActionListener() {
                  public void actionPerformed(ActionEvent e) {
                    SimpleProver prover =
                      new SimpleProver(rules_, manager_, section_);
                    prover.prove(pn.getProviso());
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
        for (Iterator<RulePara> iter = rules_.iterator(); iter.hasNext();) {
          final RulePara rulePara = iter.next();
          if (apply(rulePara, node)) {
            menuItem = new JMenuItem("Rule " + rulePara.getName());
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                  apply(rulePara.getName(), node);
                }
              });
            apply.add(menuItem);
          }
          else {
            menuItem = new JMenuItem("Rule " + rulePara.getName());
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                  whyNot(rulePara.getName(), node);
                }
              });
            whyNot.add(menuItem);
          }
          reset(sequent);
        }
      }
      JMenuItem print = new JMenuItem("Print node");
      print.addActionListener(new ActionListener() {
          public void actionPerformed(ActionEvent e) {
            System.err.println(node.toString());
            System.err.println(TermToString.apply(node.getSequent()));
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
      if (ded instanceof RuleApplication) {
        for (Sequent s : ((RuleApplication) ded).getSequentList()) {
          insert(createNode(s), getChildCount());
        }
      }
      else if (ded instanceof ProvisoApplication) {
        insert(new Proviso2Node((ProvisoApplication) ded), 0);
      }
    }

    public PredSequent getSequent()
    {
      return (PredSequent) getUserObject();
    }

    public boolean isClosed()
    {
      Deduction ded = getSequent().getDeduction();
      if (ded == null) return false;
      if (ded instanceof RuleApplication) {
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
      else if (ded instanceof ProvisoApplication) {
        ProvisoApplication provisoAppl = (ProvisoApplication) ded;
        return (provisoAppl.getProvisoStatus() instanceof CheckPassed);
      }
      throw new RuntimeException("Unexpected dedudction " + ded.getClass());
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

  class Proviso2Node
    extends DefaultMutableTreeNode
  {
    public Proviso2Node(ProvisoApplication provisoAppl)
    {
      super(provisoAppl);
    }

    public ProvisoApplication getProviso()
    {
      return (ProvisoApplication) getUserObject();
    }

    public boolean isClosed()
    {
      return (getProviso().getProvisoStatus() instanceof CheckPassed);
    }

    public String toString()
    {
      return "proviso";
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
      else if (value instanceof Proviso2Node) {
        setToolTipText("Proviso");
        Proviso2Node node = (Proviso2Node) value;
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
        if (sequent.getDeduction() instanceof RulePara) {
          RulePara rulePara = (RulePara) sequent.getDeduction();
          setToolTipText("Rule " + rulePara.getName());
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
