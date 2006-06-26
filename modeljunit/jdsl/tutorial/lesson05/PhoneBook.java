import java.awt.*;
import java.awt.event.*;
import jdsl.core.ref.ComparableComparator;


/**
  * This simple phone number database supports insertion and removal of
  * names and corresponding phone numbers, and allows the user to retrieve
  * a phone number by entering a name. The program demonstrates some
  * capabilities of the JDSL's Dictionary and OrderedDictionary
  * interfaces.
	*
	* @author Lucy Perry (lep)
	* @version JDSL 2
*/


public class PhoneBook extends Frame
  implements ActionListener, WindowListener{
    
    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    //constructor
    public PhoneBook(){
      super();

      //b5.1
      //create the OrderedDictionary, passing a Comparator to its constructor
      od_ = new jdsl.core.ref.RedBlackTree(new ComparableComparator());
      //e5.1
      setupPanel();//takes care of visual components
    }

    /**
     * This method is called when the "add a name,number entry" button is
     * clicked. The String in the name_adder_ field is used as the key, and
     * the String (phone number) in the number_adder_ field is used as the
     * element to store.
     * The key and element are then inserted into the OrderedDictionary.
     */
    //b5.2
    public void addEntry(){
      Object key = name_adder_.getText();
      Object element = number_adder_.getText();
      od_.insert(key, element);
      //now clear out those text fields just to look nice
      name_adder_.setText("");
      number_adder_.setText("");
    }
    //e5.2

    /*
     * This method is called when the "find the phone number" button is
     * clicked. The String in the name_query_ field is used as a search key.
     * That key is passed as a parameter to the Dictionary's find(.) method.
     * A Locator is returned from the find(.) operation, and is stored as our
     * current_entry_. Then the displayCurrentEntry() helper method is
     * invoked.
     */
    //b5.3 
    public void findEntry(){
      Object key = name_query_.getText();
      // note that a JDSL Locator is returned from the find(.) operation
      current_entry_ = od_.find(key);

      //this helper method will display the data
      displayCurrentEntry();

      //now clear out the name_query_ text field just to look nice
      name_query_.setText("");
    }
    //e5.3

    /**
     * This method is called when the "previous entry" button is 
     * clicked. It uses the OrderedDictionary method before(Locator).
     */
    //b5.4
    public void getEntryBefore(){
      //we want to see the entry before the current_entry_
      //note that the before(.) method takes a Locator as a parameter
      try{
	    jdsl.core.api.Locator prevEntry = od_.before(current_entry_);
	    current_entry_ = prevEntry;
      }
      catch(jdsl.core.api.InvalidAccessorException iae){}
      //this would happen if we tried calling before(.) using an invalid
      //Locator for current_entry_.

      displayCurrentEntry();//Display the current (valid or not) entry.
    }
    //e5.4

    /**
     * This method is called when the "next entry" button is clicked.
     * It uses the OrderedDictionary method after(Locator).
     */
    //b5.5 
    public void getEntryAfter(){
      //we want to see the entry after the the current_entry_
      //note that the after(.) method takes a Locator as a parameter
      try{
	    jdsl.core.api.Locator nextEntry = od_.after(current_entry_);
	    current_entry_ = nextEntry;
      }
      catch(jdsl.core.api.InvalidAccessorException iae){}
      //this would happen if we tried calling after(.) using an invalid
      //Locator for current_entry_.

      displayCurrentEntry();//Display the current (valid or not) entry.
    }
    //e5.5
    
    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
   //JDSL OrderedDictionary for keeping track of data
    private jdsl.core.api.OrderedDictionary od_;
    
    //This JDSL Locator contains the name,number pair that is displayed
    //after a find(.) operation
    private jdsl.core.api.Locator current_entry_;

    //awt panel, holds all visual components
    private Panel panel_;

    //user enters a person's name here
    private TextField name_adder_;

    //user enters a person's phone number here
    private TextField number_adder_;

    //click this button to enter a name+number in the OrderedDictionary
    private Button add_entry_;

    //user enters a name here for retrieving a phone number
    private TextField name_query_;

    //user clicks this button to retrieve a phone number
    private Button find_entry_;

    //data resulting from a "find" operation is displayed here
    private TextField show_entry_;
    
    //click this button for the previous entry in the phone book
    private Button prev_entry_;

    //click this button for the next entry in the phone book
    private Button next_entry_;

    //click this button to quit
    private Button quit_;

    /*
      This method displays the element and key of the Locator which is
      the current_entry_. It also handles the display of two types of 
      invalid Locators which may result from a find(.), before(.), or 
      after(.) operation.
    */
    //b5.6
    public void displayCurrentEntry(){
      String toDisplay = null;

      //if a find(.) operation was unsuccessful, it returned NO_SUCH_KEY
      if (current_entry_ == jdsl.core.api.Dictionary.NO_SUCH_KEY){
	toDisplay = "No entry was found using that name as a key.";
      }

      //if before(.) or after(.) was requested, and there was no such entry
      else if (current_entry_ == jdsl.core.api.OrderedDictionary.BOUNDARY_VIOLATION){
	toDisplay = "You've passed the beginning or end of the Dictionary.";
      }
      
      else{
	toDisplay = (String)(current_entry_.key()) + 
	  " " + (String)(current_entry_.element());
      }	
      
      //put the string in the text field
      show_entry_.setText(toDisplay);

    }
    //e5.6

    //takes care of visual components
    private void setupPanel(){
      setLocation(50,50);//makes frame pop up in nice location

      panel_ = new Panel();
      add(panel_);

      name_adder_ = new TextField(25);
      name_adder_.setEditable(true);

      number_adder_ = new TextField(25);
      number_adder_.setEditable(true);

      add_entry_ = new Button("Click to add a name,number entry to the phone book");
      add_entry_.addActionListener(this);

      name_query_ = new TextField(25);
      name_query_.setEditable(true);

      find_entry_ = new Button("Click to find the phone number for the given name");
      find_entry_.addActionListener(this);

      show_entry_ = new TextField(45);
      show_entry_.setEditable(false);

      prev_entry_ = new Button("Click for the previous entry in phone book");
      prev_entry_.addActionListener(this);

      next_entry_ = new Button("Click for the next entry in phone book");
      next_entry_.addActionListener(this);
      
      quit_ = new Button("Quit");
      quit_.addActionListener(this);

      addWindowListener(this);

      GridBagLayout layout = new GridBagLayout();
      panel_.setLayout(layout);

      GridBagConstraints constraints = new GridBagConstraints();
      constraints.gridy=GridBagConstraints.RELATIVE;//right below the last one
      constraints.gridx=1;//1 column
      constraints.anchor=GridBagConstraints.CENTER;
      constraints.ipady=2;//set vgap to 2 pixels.
      constraints.ipadx=3;


      panel_.add(new Label("Enter a name here:"), constraints);
      panel_.add(name_adder_, constraints);

      panel_.add(new Label(""), constraints);//blank line

      panel_.add(new Label("Enter a phone number here:"), constraints);
      panel_.add(number_adder_, constraints);

      panel_.add(new Label(""), constraints);//blank line
      panel_.add(new Label(""), constraints);//blank line

      panel_.add(add_entry_, constraints);

      panel_.add(new Label(""), constraints);//blank line

      panel_.add(new Label("Find phone number for this person (enter name):"),
		 constraints);
      panel_.add(name_query_, constraints);
      panel_.add(find_entry_, constraints);

      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(show_entry_, constraints);
      panel_.add(prev_entry_, constraints);
      panel_.add(next_entry_, constraints);

      panel_.add(new Label(""), constraints);//blank line
      panel_.add(new Label(""), constraints);//blank line

      panel_.add(quit_, constraints);

      validate();
      setVisible(true);
      panel_.validate();
      panel_.setVisible(true);
      pack();
    }


    //handles button presses
    public void actionPerformed(ActionEvent e){
      
      if (e.getSource() == add_entry_){
	    addEntry();
      }
      else if (e.getSource() == find_entry_){
	    findEntry();
      }
      else if (e.getSource() == prev_entry_){
	    getEntryBefore();
      }
      else if (e.getSource() == next_entry_){
	    getEntryAfter();
      }
      else if (e.getSource() == quit_){
	    System.exit(0);
      }

    }


    public static void main(String args[]){
      PhoneBook pb = new PhoneBook();
    }

    public void windowActivated(WindowEvent e) {}
    public void windowClosed(WindowEvent e) {}
    public void windowClosing(WindowEvent e) {System.exit(0);}
    public void windowDeactivated(WindowEvent e) {}
    public void windowDeiconified(WindowEvent e) {}
    public void windowIconified(WindowEvent e) {}
    public void windowOpened(WindowEvent e) {}
}

      
      
