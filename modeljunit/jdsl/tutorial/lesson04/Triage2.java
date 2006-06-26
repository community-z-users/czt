
import jdsl.core.api.*;
import java.awt.*;
import java.awt.event.*;


/**
	* @author Lucy Perry (lep)
	* @version JDSL 2
	*/
public class Triage2 extends Frame 
        implements ActionListener, WindowListener{

    /* ************************************ */ 
    /* The members described in the lesson. */
    /* ************************************ */ 

    //b4.4
    protected void changePatientPriority(){
        //if a patient is selected in the AWT list
        if (patient_list_.getSelectedItem() != null){
	        //get the String that's highlighted in the AWT list
	        String patientString = patient_list_.getSelectedItem();
	        //access the patient-locator from the Dictionary
	        Locator dictionaryLocator = dict_.find(patientString);
	        Locator pqLocator = (Locator)dictionaryLocator.element();
	        int newPriority = java.lang.Integer.parseInt(change_priority_choice_.getSelectedItem(), 10);
	        Object newKey = new Integer(newPriority);
	        pq_.replaceKey(pqLocator, newKey);//changes the priority-key in queue
	        //now replace patientString w/ new one and change it in dict_
	        patientString = patientString(pqLocator);
	        dict_.replaceKey(dictionaryLocator, patientString);
        }
    }	  
    //e4.4

    /* ************************************ */ 
    /* Members not described in the lesson. */
    /* ************************************ */ 
    
    //JDSL PriorityQueue for keeping track of data
    private PriorityQueue pq_;

    //JDSL Dictionary for finding patients, once they've been entered
    //into the PriorityQueue
    private Dictionary dict_;
    
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



    //this pull-down menu allows the user to select a patient
    private List patient_list_;

    //a choice widget for changing a patient's triage priority
    private Choice change_priority_choice_;

    //click this button to change a patient's priority
    private Button change_priority_button_;

    //click this button to quit
    private Button quit_;

    public Triage2(){
      super();
      
      //create the PriorityQueue, passing a Comparator to its constructor
      pq_ = new jdsl.core.ref.ArrayHeap(new jdsl.core.ref.IntegerComparator());

      dict_ = new jdsl.core.ref.HashtableDictionary(new jdsl.core.ref.ObjectHashComparator());

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
    protected void enterPatient(){
      Object element = name_field_.getText();
      int priority = java.lang.Integer.parseInt(priority_chooser_.getSelectedItem(), 10);
      //remebmer that the key must be an Object, so make the int an Integer
      Object key = new Integer(priority);
      //Insert the data into the PriorityQueue
      Locator patient = pq_.insert(key, element);
      //now hang on to the patient in a list for later access
      addPatientLocator(patient);
    }
   
    protected void addPatientLocator(Locator patient){
      String patientString = //this will be what we display in the list-widget
	  patientString(patient);

      dict_.insert(patientString, patient);
    }
   
    protected String patientString(Locator pqLocator){
      String name = (String)pqLocator.element();
      String number = ((Integer)pqLocator.key()).toString();
      String patientString = name + " " + number;
      return patientString;
    }

    /**
     * This method is called when the "Remove top patient" button is pressed.
     * The top-priority patient is removed from the PriorityQueue, and 
     * patient's name displayed in a text field.
     */
    protected void getTopPatient(){
      Object output;//this will be the patient's name, or an error msg
      Locator patientLocator;
      String patientString;

      //Remove the top-priority item from the PriorityQueue and Dictionary
      try{
	    patientLocator = pq_.min();
	    patientString = patientString(patientLocator);
	    dict_.remove(dict_.find(patientString));
	    output = pq_.removeMin();//output = element stored w/ minimum key
      }
      catch(EmptyContainerException ece){
	    output = "No patients in queue.";
      }
      top_priority_patient_.setText((String)output);
    }

    //takes care of visual components
    private void setupPanel(){
      setLocation(50,50);//makes frame pop up in nice location

      panel_ = new Panel();
      
      add(panel_);
      
      name_field_ = new TextField(20);
      name_field_.setEditable(true);
      
      priority_chooser_ = new Choice();
      priority_chooser_.add("1");
      priority_chooser_.add("2");
      priority_chooser_.add("3");
      priority_chooser_.add("4");
      priority_chooser_.add("5");
      
      enter_patient_ = new Button("Add the patient to the PriorityQueue");
      enter_patient_.addActionListener(this);
      
      remove_top_patient_ = new Button("Remove the top-priority patient");
      remove_top_patient_.addActionListener(this);
      
      top_priority_patient_ = new TextField(20);
      top_priority_patient_.setEditable(false);
      
      patient_list_ = new List(5, false);
      
      change_priority_choice_ = new Choice();
      change_priority_choice_.add("1");
      change_priority_choice_.add("2");
      change_priority_choice_.add("3");
      change_priority_choice_.add("4");
      change_priority_choice_.add("5");

      change_priority_button_ = new Button("Change the patient's triage priority");
      change_priority_button_.addActionListener(this);

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

      Panel row;
   
      row = new Panel();
      row.add(new Label("Enter new patient's name here:"));
      row.add(name_field_);
      panel_.add(row, constraints);
      
      panel_.add(new Label("Set the patient's triage priority here:"), constraints);
      
      row = new Panel();
      row.add(new Label("(1 = most urgent,  5 = least urgent)"));
      row.add(priority_chooser_);
      panel_.add(row, constraints);

      panel_.add(new Label(""), constraints);//blank line
      
      panel_.add(enter_patient_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line

      panel_.add(remove_top_patient_, constraints);
      
      panel_.add(new Label(""), constraints);//blank line
      
      row = new Panel();
      row.add(new Label("Ready to treat patient:"));
      row.add(top_priority_patient_);
      panel_.add(row, constraints);
      
      panel_.add(new Label(""), constraints);//blank line

      panel_.add(new Label("Change priority for the following patient (select one):"), constraints);
      panel_.add(patient_list_, constraints);

      row = new Panel();
      row.add(new Label("Choose new priority"));
      row.add(change_priority_choice_);
      panel_.add(row, constraints);
      
      panel_.add(new Label(""), constraints);//blank line

      panel_.add(change_priority_button_, constraints);

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
	    name_field_.setText("");//clears text field so it looks nice
	    updateListWidget();
      }
      else if (e.getSource() == remove_top_patient_){
	    getTopPatient();
	    updateListWidget();
      }
      else if (e.getSource() == change_priority_button_){
	    changePatientPriority();
	    updateListWidget();
      }
      else if (e.getSource() == quit_){
	    System.exit(0);
      }
    }

    


    protected void updateListWidget(){
      if (patient_list_.getItemCount() > 0){
	    patient_list_.removeAll();
      }
      ObjectIterator oi = dict_.keys();
      String patientString;
      while (oi.hasNext()){
	    patientString = (String)oi.nextObject();
	    patient_list_.add(patientString);
      }
    }

    public static void main(String args[]){
      Triage2 t = new Triage2();
    }

    public void windowActivated(WindowEvent e) {}
    public void windowClosed(WindowEvent e) {}
    public void windowClosing(WindowEvent e) {System.exit(0);}
    public void windowDeactivated(WindowEvent e) {}
    public void windowDeiconified(WindowEvent e) {}
    public void windowIconified(WindowEvent e) {}
    public void windowOpened(WindowEvent e) {}

}





  
