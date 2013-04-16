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

package net.sourceforge.czt.rules.prover;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.net.URL;
import java.util.*;
import javax.swing.*;
import javax.swing.tree.*;

import net.sourceforge.czt.rules.*;
import net.sourceforge.czt.rules.ast.*;
import net.sourceforge.czt.rules.print.PrintUtils;
import net.sourceforge.czt.session.*;
import net.sourceforge.czt.zpatt.ast.*;
import net.sourceforge.czt.zpatt.util.*;

public class ProofTree
  extends JTree
{
  /**
	 * 
	 */
	private static final long serialVersionUID = -1384815784250541020L;
  //private JFrame frame_;
  private RuleTable rules_;
  private SectionManager manager_;
  private String section_;

  public ProofTree(JFrame frame,
                   Sequent sequent,
                   RuleTable rules,
                   SectionManager manager,
                   String section)
  {
    //frame_ = frame;
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
    Sequent sequent = node.getSequent();
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor visitor = new CopyVisitor(factory);
    RulePara copiedRulePara = (RulePara) rulePara.accept(visitor);
    return SimpleProver.apply(copiedRulePara, sequent);
  }

  private void apply(String name, ProofNode node)
  {
    Sequent sequent = node.getSequent();
    if (apply(rules_.getRulePara(name), node)) {
      substituteNode(node, new ProofNode(sequent));
    }
  }

  private DefaultMutableTreeNode createNode(Sequent s)
  {
    return new ProofNode(s);
  }

  private void whyNot(String name, ProofNode node)
  {
    Sequent sequent = node.getSequent();
    Factory factory = new Factory(new ProverFactory());
    CopyVisitor visitor = new CopyVisitor(factory);
    RulePara copiedRule = (RulePara) rules_.getRulePara(name).accept(visitor);
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
    throws CommandException
  {
    SimpleProver prover = new SimpleProver(rules_, manager_, section_);
    Sequent sequent = node.getSequent();
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

  private void reset(Sequent sequent)
  {
    Deduction ded = sequent.getAnn(Deduction.class);
    if (ded != null) {
      java.util.List<Binding> bindings = new java.util.ArrayList<Binding>();
      ProverUtils.collectBindings(sequent, bindings);
      ProverUtils.reset(bindings);
      sequent.getAnns().remove(ded);
    }
  }

  private void reset(ProofNode node)
  {
    Sequent sequent = node.getSequent();
    reset(sequent);
    substituteNode(node, new ProofNode(sequent));
  }


  public static void createAndShowGUI(Sequent sequent,
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
          else if (o instanceof OracleNode) {
            final OracleNode pn = (OracleNode) o;
            if (! pn.isClosed()) {
              JPopupMenu popup = new JPopupMenu();
              JMenuItem menuItem = new JMenuItem("Ask oracle");
              menuItem.addActionListener(new ActionListener() {
                  public void actionPerformed(ActionEvent e) {
                    try {
                      SimpleProver prover =
                        new SimpleProver(rules_, manager_, section_);
                      prover.prove(pn.getOracleAppl());
                      getModel().nodeChanged(pn);
                    }
                    catch (CommandException exception)
                    {
                      exception.printStackTrace();
                    }
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
      final Sequent sequent = (Sequent) node.getUserObject();
      JPopupMenu popup = new JPopupMenu();
      Deduction ded = sequent.getAnn(Deduction.class);
      if (ded != null) {
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
              try {
                prove(node);
              }
              catch (CommandException exception)
              {
                exception.printStackTrace();
              }
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
            menuItem = new JMenuItem(rulePara.getName());
            menuItem.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                  apply(rulePara.getName(), node);
                }
              });
            apply.add(menuItem);
          }
          else {
            menuItem = new JMenuItem(rulePara.getName());
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
    /**
	 * 
	 */
	private static final long serialVersionUID = -2007617040338579312L;

	public ProofNode(Sequent sequent)
    {
      super(sequent);
      Deduction ded = sequent.getAnn(Deduction.class);
      if (ded instanceof RuleAppl) {
        for (Sequent s : ((RuleAppl) ded).getSequentList()) {
          insert(createNode(s), getChildCount());
        }
      }
      else if (ded instanceof OracleAppl) {
        insert(new OracleNode((OracleAppl) ded), 0);
      }
    }

    public Sequent getSequent()
    {
      return (Sequent) getUserObject();
    }

    public boolean isClosed()
    {
      Deduction ded = getSequent().getAnn(Deduction.class);
      if (ded == null) return false;
      if (ded instanceof RuleAppl) {
        for (@SuppressWarnings("unchecked")
		Enumeration<TreeNode> e = (Enumeration<TreeNode>)children();
             e.hasMoreElements() ;) {
          TreeNode node = e.nextElement();
          if (node instanceof ProofNode) {
            if (! ((ProofNode) node).isClosed()) return false;
          }
          else {
            throw new RuntimeException("Unexpected node " + node.getClass());
          }
        }
        return true;
      }
      else if (ded instanceof OracleAppl) {
        OracleAppl oracleAppl = (OracleAppl) ded;
        return (oracleAppl.getOracleAnswer() instanceof CheckPassed);
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

  class OracleNode
    extends DefaultMutableTreeNode
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = 5643642019102791655L;

	public OracleNode(OracleAppl oracleAppl)
    {
      super(oracleAppl);
    }

    public OracleAppl getOracleAppl()
    {
      return (OracleAppl) getUserObject();
    }

    public boolean isClosed()
    {
      return (getOracleAppl().getOracleAnswer() instanceof CheckPassed);
    }

    public String toString()
    {
      return "oracle";
    }
  }

  class Renderer
    extends DefaultTreeCellRenderer
  {
    /**
	 * 
	 */
	private static final long serialVersionUID = -1437641660754271760L;

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
      if (value instanceof OracleNode) {
        setToolTipText("Oracle");
        OracleNode node = (OracleNode) value;
        if (node.isClosed()) {
          setIcon("ok");
        }
        else {
	  setIcon("question");
        }
      }
      else if (value instanceof ProofNode) {
        ProofNode node = (ProofNode) value;
        Sequent sequent = node.getSequent();
	Deduction ded = sequent.getAnn(Deduction.class);
        if (ded instanceof RuleAppl) {
          RuleAppl ruleAppl = (RuleAppl) ded;
          setToolTipText("Rule " + ruleAppl.getName());
        }
        else if (ded instanceof OracleAppl) {
          OracleAppl oracleAppl = (OracleAppl) ded;
          setToolTipText("Oracle " + oracleAppl.getName());
        }
        else {
          setToolTipText("No rule has been applied to this sequent");
        }
        if (node.isClosed()) {
          setIcon("ok");
        }
        else {
          setIcon("question");
        }
      }
      return this;
    }

    private void setIcon(String iconName)
    {
      String s = "/net/sourceforge/czt/rules/images/" + iconName + ".jpg";
      URL url = getClass().getResource(s);
      if (url != null) {
	setIcon(new ImageIcon(url));
      }
      else {
	System.err.println(s + " not found!");
      }
    }
  }
}
