import jdsl.core.algo.traversals.*;
import jdsl.core.api.*;
import java.applet.Applet;
import java.awt.*;
import java.awt.event.*;

/** 
 * Class that manages the tree drawing application.
 *
 * @author Lucy Perry (lep)
 * @version JDSL 2
*/
public class SimpleTreeDraw extends Frame implements ActionListener,WindowListener {
    private RandomTreeBuilder builder=new RandomTreeBuilder();
    private Tree tree;
    private int numNodes=16;

    Button newTree = new Button("Draw New Tree");
    Button quitBtn = new Button("Quit");

    public SimpleTreeDraw() {
        super("Simple Tree Drawing");
        //build the tree
        tree=builder.randomTree(numNodes);
        
        setLayout(new BorderLayout());
        Panel p = new Panel();
        addWindowListener(this);
        quitBtn.addActionListener(this);
        newTree.addActionListener(this);
        p.add(newTree);
        p.add(quitBtn);
        add(p, BorderLayout.SOUTH);
        setSize(700,350);
	    setLocation(50,50);
    }

    /**
     * The paint method draws the tree.  There are 2 steps:  The BoundingBoxCalculator
     * determines the width of each subtree.  The TreeDrawer calculates the exact 
     * locations for labels and edges and draws the tree.
     */
    public void paint(Graphics g) {
        g.setColor(getBackground());
        BoundingBoxCalculator calc = new BoundingBoxCalculator(getGraphics());
        calc.execute(tree);
        TreeDrawer drawer = new TreeDrawer(g);
        drawer.execute(tree);
    }

    public void actionPerformed(ActionEvent e) {
        if (e.getSource()==quitBtn)
            quit();
        else if (e.getSource()==newTree) {
            // The user clicked the new tree button.  Build a new tree and redraw.
            tree=builder.randomTree(numNodes);
            repaint();
        }
    }

    private void quit() {
        System.exit(0);
    }

    public void windowActivated(WindowEvent e) {}
    public void windowClosed(WindowEvent e) {}
    public void windowClosing(WindowEvent e) {quit();}
    public void windowDeactivated(WindowEvent e) {}
    public void windowDeiconified(WindowEvent e) {}
    public void windowIconified(WindowEvent e) {}
    public void windowOpened(WindowEvent e) {}

    public static void main(String args[]) {
        SimpleTreeDraw s = new SimpleTreeDraw();
        s.show();
    }
}
