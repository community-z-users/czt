//b2.1
import jdsl.core.api.*;
import jdsl.core.ref.*;
import jdsl.core.algo.sorts.*;
//e2.1
import java.awt.*;
import java.awt.event.*;
import java.util.*;

/*
 * This Class demonstrates manipulating Sequences.
 *
 * @author Robert Cohen (rfc)
 * @version JDSL 2
*/
public class SequenceFun extends Frame implements ActionListener,  WindowListener {

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    /*
     Sort a sequence in alphabetical order.  
    */
    //b2.2
    private void sort(Sequence seq) {
        // This object will do the sorting.
        SortObject sorter = new ArrayQuickSort();
        // Sort in alphabetical order.
        sorter.sort(seq, new ComparableComparator());
    }
    //e2.2

    /*
     Sort a sequence in reverse alphabetical order.  
    */
    //b2.4
    private void reverseSort(Sequence seq) {
        // This object will do the sorting.
        SortObject sorter = new ArrayQuickSort();
        // Sort in alphabetical order.
        sorter.sort(seq, new ComparatorReverser(new ComparableComparator()));
    }
    //e2.4

    /*
     Randomly permute the elements of a Sequence.  
    */
    //b2.5
    protected void permute(Sequence s) {
        Random rnd = new java.util.Random();
        for(int i=s.size()-1;i>0;i--) {
            int j=rnd.nextInt(i+1);
            if (j<i)
                s.swapElements(s.atRank(i),s.atRank(j));
        }
    }
    //e2.5

    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    // The sequence to store the words.
    Sequence seq;
    
    // The GUI widgets
    Label title = new Label( "Test Sequences" );
    TextField inField = new TextField( "", 50 );
    TextField outField = new TextField( "", 50 );
    Button echoBtn = new Button("Echo");
    Button sortBtn = new Button("Sort");
    Button reverseBtn = new Button("Reverse Sort");
    Button permuteBtn = new Button("Permute");
    Button quitBtn = new Button("Quit");

    /*
     The Constructor simple sets up the GUI.
    */
    public SequenceFun() {
        setUpWindow();
    }

    public void actionPerformed(ActionEvent e) {
        String in = inField.getText();
        seq = getWords(in);
        if (e.getSource()==sortBtn)
            sort(seq);
        else if (e.getSource()==reverseBtn)
            reverseSort(seq);
        else if (e.getSource()==permuteBtn)
            permute(seq);
        else if (e.getSource()==quitBtn)
            quit();
        outField.setText(conc(seq));
    }

    /*
     Takes a string and converts it to a sequence of words.  This is
     the same method from Lesson 1.
    */ 
    private Sequence getWords(String s) {
        Sequence ret = new ArraySequence();
        StringTokenizer st = new StringTokenizer(s);
        while (st.hasMoreTokens()) {
            ret.insertLast(st.nextToken());
        }
        return ret;
    }

    /*
     Takes a Sequence of words and returns a string consisting of all
     the words, each separated by a space.  This is
     the same method from Lesson 1.
    */
    private String conc(Sequence s) {
        String ret = "";
        for(ObjectIterator i=seq.elements();i.hasNext();)
            ret += (i.nextObject() + " ");
        return ret;
    }

    /*
     Run the frame.
    */
    public static void main(String args[]) {
        SequenceFun s = new SequenceFun();
        s.show();
    }

    /*
     Set up the GUI.
    */
    private void setUpWindow() {
        setTitle("Sort");
        title.setFont( new Font( "Helvetica", Font.BOLD , 24 ) );
        Panel titlePanel = new Panel();
        titlePanel.add(title);

        Panel inPanel = new Panel();
        inPanel.add(new Label("Enter a sentence"));
        inPanel.add(inField);

        outField.setEditable(false);
        Panel outPanel = new Panel();
        outPanel.add(new Label("Result"));
        outPanel.add(outField);

        Panel centerPanel = new Panel();
        centerPanel.add(inPanel);
        centerPanel.add(outPanel);

        Panel btnPanel = new Panel();
        btnPanel.add(echoBtn);
        btnPanel.add(sortBtn);
        btnPanel.add(reverseBtn);
        btnPanel.add(permuteBtn);
        btnPanel.add(quitBtn);

        setLayout(new BorderLayout());
        add(titlePanel, BorderLayout.NORTH);
        add(centerPanel, BorderLayout.CENTER);
        add(btnPanel, BorderLayout.SOUTH);

        addWindowListener(this);
        echoBtn.addActionListener(this);
        sortBtn.addActionListener(this);
        reverseBtn.addActionListener(this);
        permuteBtn.addActionListener(this);
        quitBtn.addActionListener(this);
        inField.addActionListener(this);
        inField.requestFocus();

	setSize(500,250);
	setLocation(50,50);
    }

    private void quit() {
        System.exit(0);
    }
    
    public void windowActivated(WindowEvent e) {}
    public void windowClosed(WindowEvent e) {quit();}
    public void windowClosing(WindowEvent e) {quit();}
    public void windowDeactivated(WindowEvent e) {}
    public void windowDeiconified(WindowEvent e) {}
    public void windowIconified(WindowEvent e) {}
    public void windowOpened(WindowEvent e) {}
}
