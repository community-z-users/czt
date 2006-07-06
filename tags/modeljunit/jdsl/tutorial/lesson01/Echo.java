//b1.1
import jdsl.core.api.*;
import jdsl.core.ref.*;
//e1.1
import java.util.*;
import java.awt.*;
import java.awt.event.*;


/*
 * A class to introduce the JDSL.  It reads words into a jdsl.ref.Sequence
 * object and writes them back out.
 *
 * @author Robert Cohen (rfc)
 * @version JDSL 2
*/
public class Echo extends Frame implements ActionListener,WindowListener {

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 
    
    /*
     Takes a string and converts it to a sequence of words.  The StringTokenizer object
     returns an enumeration of tokens, each a word from the original string.  Each word
     is added to the end of the sequence.
    */ 
    //b1.2
    private Sequence getWords(String s) {
        Sequence ret = new ArraySequence();
        StringTokenizer st = new StringTokenizer(s);
        while (st.hasMoreTokens()) {
            ret.insertLast(st.nextToken());
        }        
        return ret;
    }
    //e1.2
    
    /*
     Takes a Sequence of words and returns a string consisting of all
     the words, each separated by a space.  Uses a jdsl.api.ObjectIterator to 
     iterate through the words.
    */
    //b1.3
    private String concatenate(Sequence s) {
        String ret = "";
        for(ObjectIterator i=s.elements();i.hasNext();)
            ret += (i.nextObject() + " ");
        return ret;
    }
    //e1.3

    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    // The sequence to store the words.
    Sequence seq;
    
    // The GUI widgets
    Label title = new Label( "Echo" );
    TextField inField = new TextField( "", 50 );
    TextField outField = new TextField( "", 50 );
    Button quitBtn = new Button("Quit");

    /*
     The Constructor simple sets up the GUI.
    */
    public Echo() {
      setUpWindow();
    }

    public void actionPerformed(ActionEvent e) {
        //The user entered text.  
        if (e.getSource()==inField) {
	        String in = inField.getText();
	        //converts the string into a sequence of words
	        seq = getWords(in);
	        //outputs the words.
	        outField.setText(concatenate(seq));
	    // The user clicked the quit button.    
	    } else if (e.getSource()==quitBtn)
            quit();
    }

    /*
     Run the frame.
    */
    public static void main(String args[]) {
        Echo e = new Echo();
        e.show();
    }
    
    /*
     Set up the GUI.
    */
    private void setUpWindow() {
        setTitle("Echo");
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
        btnPanel.add(quitBtn);

        add(titlePanel, BorderLayout.NORTH);
        add(centerPanel, BorderLayout.CENTER);
        add(btnPanel, BorderLayout.SOUTH);
        
        addWindowListener(this);
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
