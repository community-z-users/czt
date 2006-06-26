
import jdsl.core.api.*;
import java.awt.*;
import java.awt.event.*;


/**
	* @author Lucy Perry (lep)
	* @version JDSL 2
	*/
public class Triage extends Frame 
        implements ActionListener,WindowListener{

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    public Triage(){
      super();
      //b4.1
      //create the PriorityQueue, passing a Comparator to its constructor
      pq_ = new jdsl.core.ref.ArrayHeap(new jdsl.core.ref.IntegerComparator());    
      //e4.1
      setupPanel();//takes care of visual components
    }

    /** 
     * This method is called when the "Add a patient" button is pressed
     * The patient's name is retrieved from the text field, and used as
     * as an element. The priority number is retrieved from the choice 
     * widget, and used as a key.
     * Then the key and element are inserted, together, into the 
     * PriorityQueue.
     */
    //b4.2 
    protected void enterPatient(){
      Object element = name_field_.getText();
      int priority = java.lang.Integer.parseInt(priority_chooser_.getSelectedItem(), 10);
      //rememer that the key must be an Object, so make the int an Integer
      Object key = new Integer(priority);
      //Insert the data into the PriorityQueue
      pq_.insert(key, element);
    }
    //e4.2

    /**
     * This method is called when the "Remove top patient" button is pressed.
     * The top-priority patient is removed from the PriorityQueue, and 
     * patient's name displayed in a text field.
     */
    //b4.3
    protected void getTopPatient(){
        Object output;
        //Remove the top-priority item from the PriorityQueue
        try{
	        output = pq_.removeMin();
        }
        catch(EmptyContainerException ece){
	        output = "No patients in queue.";
        }
        top_priority_patient_.setText((String)output);
    }
    //e4.3

    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    //JDSL PriorityQueue for keeping track of data
    private PriorityQueue pq_;

    //awt panel, holds all visual components
    private Panel panel_;
    
    //user enters a patient's name here
    private TextField name_field_;

    //a choice widget for selecting a triage priority
    private Choice priority_chooser_;

    //click this button to enter a patient + priority in the PriorityQueue
    private Button enter_patient_;

    //click this button to remove the top-priority patient
    private Button remove_top_patient_;

    //when the top patient is removed, the patient's name is displayed here
    private TextField top_priority_patient_;

    //click this button to quit
    private Button quit_;








    //takes care of visual components
    private void setupPanel(){
      setLocation(50,50);//makes frame pop up in a nice place

      panel_ = new Panel();
      
      add(panel_);
      
      name_field_ = new TextField(25);
      name_field_.setEditable(true);
      
      priority_chooser_ = new Choice();
      priority_chooser_.add("1");
      priority_chooser_.add("2");
      priority_chooser_.add("3");
      priority_chooser_.add("4");
      priority_chooser_.add("5");
      
      enter_patient_ = new Button("Add a patient to the PriorityQueue");
      enter_patient_.addActionListener(this);
      
      remove_top_patient_ = new Button("Remove the top-priority patient");
      remove_top_patient_.addActionListener(this);
      
      top_priority_patient_ = new TextField(25);
      top_priority_patient_.setEditable(false);
      
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

   
   

      panel_.add(new Label("Enter patient's name here:"), constraints);
      panel_.add(name_field_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(new Label("Set the patient's triage priority here:"), constraints);
      panel_.add(new Label("(1 = most urgent,  5 = least urgent)"), constraints);
      panel_.add(priority_chooser_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(enter_patient_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(remove_top_patient_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(new Label("Ready to treat patient:"), constraints);
      panel_.add(top_priority_patient_, constraints);
      
      
      panel_.add(new Label(""), constraints);//blank line
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
      
      if(e.getSource() == enter_patient_){
	    enterPatient();
      }
      else if (e.getSource() == remove_top_patient_){
	    getTopPatient();
      }
      else if (e.getSource() == quit_){
	    System.exit(0);
      }
    }




    public static void main(String args[]){
      Triage t = new Triage();
    }

    public void windowActivated(WindowEvent e) {}
    public void windowClosed(WindowEvent e) {}
    public void windowClosing(WindowEvent e) {System.exit(0);}
    public void windowDeactivated(WindowEvent e) {}
    public void windowDeiconified(WindowEvent e) {}
    public void windowIconified(WindowEvent e) {}
    public void windowOpened(WindowEvent e) {}


}





  
