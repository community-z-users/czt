package net.sourceforge.czt.modeljunit.examples.gsm;

import java.io.FileNotFoundException;
import java.util.HashMap;
import java.util.Map;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.FsmModel;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.RandomTester;

/** This is an EFSM model of the SIM card within a mobile phone.
 *  It models just a small part of the functionality to do with
 *  accessing files and directories within the SIM card, and the
 *  PINs and PUKs used to make this secure.
 *
 *  See Chapter 11 of the book "Practical Model-Based Testing:
 *  A Tools Approach" for more discussion of this system and
 *  a version of the model in B.
 *  
 *  This ModelJUnit version of the model was translated from a UML/OCL
 *  model developed at LEIRIOS Technologies, which in turn was adapted
 *  from an earlier and larger version of the B model published in
 *  the above book.
 *
 * @author marku
 *
 */
public class SimCard implements FsmModel
{
  public enum E_Status {Enabled, Disabled};
  public enum B_Status {Blocked, Unblocked};
  public enum Status_Word {sw_9000, sw_9404, sw_9405, sw_9804,
                           sw_9840, sw_9808, sw_9400};
  public enum File_Type {Type_DF, Type_EF};
  public enum Permission {Always, CHV, Never, Adm, None};
  public enum F_Name {MF, DF_GSM, EF_LP, EF_IMSI, DF_Roaming, EF_FR, EF_UK};

  // These variables model the attributes within each Sim Card.
  protected int PIN;   // can be 11 or 12
  protected static final int PUK = 22;
  protected E_Status status_en;
  protected B_Status status_PIN_block;
  protected B_Status status_block;
  protected int counter_PIN_try;
  protected int counter_PUK_try;
  protected boolean perm_session;
  public static final int Max_Pin_Try = 3;
  public static final int Max_Puk_Try = 10;
  protected String read_data;
  protected Status_Word result;

  // These variables model what a SimCard knows about Files.
  protected File DF;  // the current directory (never null)
  protected File EF;  // the current elementary file, or null
  protected Map<F_Name,File> files = new HashMap<F_Name,File>();

  /** If this is non-null, each action calls the corresponding adaptor
   *  action, which tests the GSM11 implementation.
   */
  protected SimCardAdaptor sut = null;
  
  /** If <code>sut0</code> is null, then the model runs without
   *  testing any SUT.
   *  
   * @param sut0  Can be null.
   */
  public SimCard(SimCardAdaptor sut0)
  {
    sut = sut0;
  }
  
  /** This sets up a hierarchy of files that is used for testing.
   *  Their contents remain constant throughout the testing.
   */
  private void initFiles()
  {
    files.clear();
    File mf =     new File(File_Type.Type_DF, F_Name.MF,        "d1", Permission.None,   null);
    File df_gsm = new File(File_Type.Type_DF, F_Name.DF_GSM,    "d1", Permission.None,   mf);
    File ef_imsi =new File(File_Type.Type_EF, F_Name.EF_IMSI,   "d2", Permission.CHV,    df_gsm);
    File ef_lp =  new File(File_Type.Type_EF, F_Name.EF_LP,     "d1", Permission.Always, df_gsm);
    File df_roam =new File(File_Type.Type_DF, F_Name.DF_Roaming,"d1", Permission.None,   df_gsm);
    File ef_fr =  new File(File_Type.Type_EF, F_Name.EF_FR,     "d3", Permission.Adm,    df_roam);
    File ef_uk =  new File(File_Type.Type_EF, F_Name.EF_UK,     "d4", Permission.Never,  df_roam);
    files.put(F_Name.MF, mf);
    files.put(F_Name.DF_GSM, df_gsm);
    files.put(F_Name.EF_IMSI, ef_imsi);
    files.put(F_Name.EF_LP, ef_lp);
    files.put(F_Name.DF_Roaming, df_roam);
    files.put(F_Name.EF_FR, ef_fr);
    files.put(F_Name.EF_UK, ef_uk);
  }

  public Object getState()
  {
    return DF.name.toString()
      + "," + (EF==null ? "null" : EF.name.toString())
      + ",PIN="+PIN
      + "," + counter_PIN_try
      + "," + counter_PUK_try
      + "," + status_en
      + "," + (status_PIN_block==B_Status.Blocked ? "PINBLOCKED" : "")
      + "," + (status_block==B_Status.Blocked ? "PUKBLOCKED" : "")
      + "," + result.toString()
      ;
  }

  public void reset(boolean testing)
  {
    PIN = 11;
    status_en = E_Status.Enabled;
    status_PIN_block = B_Status.Unblocked;
    status_block = B_Status.Unblocked;
    counter_PIN_try = 0;
    counter_PUK_try = 0;
    perm_session = false;
    read_data = "";  // None
    initFiles();
    DF = files.get(F_Name.MF);
    EF = null;
    result = Status_Word.sw_9000;  // Okay
    /*@REQ: RESET @*/
    if (sut != null) {
      sut.reset();
    }
  }

  @Action public void verifyPIN11() {Verify_PIN(11);}
  @Action public void verifyPIN12() {Verify_PIN(12);}
  public void Verify_PIN(int Pin)
  {
    // Pre: Pin > 0 and Pin < 10000

    if (status_PIN_block == B_Status.Blocked) {
      result = Status_Word.sw_9840; /*@REQ: VERIFY_CHV1 @*/
    }
    else if (status_en == E_Status.Disabled) {
      result = Status_Word.sw_9808; /*@REQ: VERIFY_CHV5 @*/
    }
    else if (Pin == PIN) {
      counter_PIN_try = 0;
      perm_session = true;
      result = Status_Word.sw_9000; /*@REQ: REQ6,VERIFY_CHV2 @*/
    }
    else if (counter_PIN_try == Max_Pin_Try - 1) {
      counter_PIN_try = Max_Pin_Try;
      status_PIN_block = B_Status.Blocked;
      perm_session = false;
      result = Status_Word.sw_9840; /*@REQ: REQ6, VERIFY_CHV4 @*/
    }
    else {
      counter_PIN_try = counter_PIN_try + 1;
      result = Status_Word.sw_9804;  /*@REQ: VERIFY_CHV3 @*/
    }

    if (sut != null) {
      sut.Verify_PIN(Pin, result);
    }
  }

  @Action public void unblockPINGood12() {Unblock_PIN(22,12);}
  @Action public void unblockPINBad()    {Unblock_PIN(11,11);}
  public void Unblock_PIN(int Puk, int new_Pin)
  {
    // pre: Puk > 0 and Puk < 10000 and new_Pin > 0 and new_Pin < 10000

    if (status_block == B_Status.Blocked) {
      result = Status_Word.sw_9840; /*@REQ: Unblock_CHV1 @*/
    }
    else if (Puk == PUK) {
      PIN = new_Pin;
      counter_PIN_try = 0;
      counter_PUK_try = 0;
      perm_session = true;
      status_PIN_block = B_Status.Unblocked;
      result = Status_Word.sw_9000;
      if (status_en == E_Status.Disabled) {
        // Sep 2007: corrected this error from the B and UML/OCL models.
        // (The B model did not model enabled/disabled PINs, and the
        //  UML/OCL model set status_en to Disabled rather than Enabled.)
        // status_en = E_Status.Disabled; /*@REQ: Unblock5 @*/
        status_en = E_Status.Enabled; /*@REQ: Unblock5 @*/
      }
      else {
        // leave status_en unchanged
      }/*@REQ: Unblock7,Unblock2 @*/
    }
    else if (counter_PUK_try == Max_Puk_Try - 1) {
      System.out.println("BLOCKED PUK!!! PUK try counter="+counter_PUK_try);
      counter_PUK_try = Max_Puk_Try;
      status_block = B_Status.Blocked;
      perm_session = false;
      result = Status_Word.sw_9840; /*@REQ: REQ7, Unblock4 @*/
    }
    else {
      counter_PUK_try = counter_PUK_try + 1;
      result = Status_Word.sw_9804;  /*@REQ: Unblock3 @*/
    }
    
    if (sut != null) {
      sut.Unblock_PIN(Puk, new_Pin, result);
    }
  }

  // When the correct PIN is 12, this will also test the invalid-PIN case
  @Action public void enablePIN11() {Enabled_PIN(11);}
  public void Enabled_PIN(int Pin)
  {
    // pre: Pin > 0 and Pin < 10000

    if (status_PIN_block == B_Status.Blocked) {
      result = Status_Word.sw_9840; /*@REQ: ENABLE2 @*/
    }
    else if (status_en == E_Status.Enabled) {
      result = Status_Word.sw_9808; /*@REQ: ENABLE3 @*/
    }
    else if (Pin == PIN) {
      counter_PIN_try = 0;
      perm_session = true;
      status_en = E_Status.Enabled;
      result = Status_Word.sw_9000; /*@REQ: ENABLE1 @*/
    }
    else if (counter_PIN_try == Max_Pin_Try - 1) {
      counter_PIN_try = Max_Pin_Try;
      status_PIN_block = B_Status.Blocked;
      perm_session = false;
      result = Status_Word.sw_9840; /*@REQ: ENABLE4 @*/
    }
    else {
      counter_PIN_try = counter_PIN_try + 1;
      result = Status_Word.sw_9804;  /*@REQ: ENABLE5 @*/
    }
    
    if (sut != null) {
      sut.Enabled_PIN(Pin, result);
    }
  }

  // When the correct PIN is 12, this will also test the invalid-PIN case
  @Action public void disablePINGood() { Disabled_PIN(11); }
  public void Disabled_PIN(int Pin)
  {
    // pre:     Pin > 0 and Pin < 10000

    if (status_PIN_block == B_Status.Blocked) {
      result = Status_Word.sw_9840; /*@REQ: DISABLE2 @*/
    }
    else if (status_en == E_Status.Disabled) {
      result = Status_Word.sw_9808; /*@REQ: DISABLE3 @*/
    }
    else if (Pin == PIN) {
      counter_PIN_try = 0;
      perm_session = true;
      status_en = E_Status.Disabled;
      result = Status_Word.sw_9000; /*@REQ: DISABLE1 @*/
    }
    else if (counter_PIN_try == Max_Pin_Try - 1) {
      counter_PIN_try = Max_Pin_Try;
      status_PIN_block = B_Status.Blocked;
      perm_session = false;
      result = Status_Word.sw_9840; /*@REQ: DISABLE4 @*/
    }
    else {
      counter_PIN_try = counter_PIN_try + 1;
      result = Status_Word.sw_9804;  /*@REQ: DISABLE5 @*/
    }

    if (sut != null) {
      sut.Disabled_PIN(Pin, result);
    }
  }

  // When the correct PIN is 12, this will also test the invalid-PIN case
  @Action public void changePinSame() { Change_PIN(11,11); }  // ???
  @Action public void changePinNew() { Change_PIN(11,12); }
  public void Change_PIN(int old_Pin, int new_Pin)
  {
    // pre: old_Pin > 0 and old_Pin < 10000 and new_Pin > 0 and new_Pin < 10000

    if (status_PIN_block == B_Status.Blocked) {
      result = Status_Word.sw_9840; /*@REQ: CHANGE2 @*/
    }
    else if (status_en == E_Status.Disabled) {
      result = Status_Word.sw_9808; /*@REQ: CHANGE3 @*/
    }
    else if (old_Pin == PIN) {
      PIN = new_Pin;
      counter_PIN_try = 0;
      perm_session = true;
      result = Status_Word.sw_9000; /*@REQ: CHANGE1 @*/
    }
    else if (counter_PIN_try == Max_Pin_Try - 1) {
      counter_PIN_try = Max_Pin_Try;
      status_PIN_block = B_Status.Blocked;
      perm_session = false;
      result = Status_Word.sw_9840; /*@REQ: CHANGE4 @*/
    }
    else {
      counter_PIN_try = counter_PIN_try + 1;
      result = Status_Word.sw_9804;  /*@REQ: CHANGE5 @*/
    }
    
    if (sut != null) {
      sut.Change_PIN(old_Pin, new_Pin, result);
    }
  }

  @Action public void selectMF() {Select_file(F_Name.MF);}
  @Action public void selectDF_Gsm() {Select_file(F_Name.DF_GSM);}
  @Action public void selectDF_Roaming() {Select_file(F_Name.DF_Roaming);}
  @Action public void selectEF_IMSI() {Select_file(F_Name.EF_IMSI);}
  @Action public void selectEF_LP() {Select_file(F_Name.EF_LP);}
  @Action public void selectEF_FR() {Select_file(F_Name.EF_FR);}
  // We omit testing EF_UK, since its permissions are similar to EF_FR
  // @Action public void selectEF_UK() {Select_file(F_Name.EF_UK);}
  public void Select_file(F_Name file_name)
  {
    // pre: true

    File temp_file = files.get(file_name);
    if (temp_file.type == File_Type.Type_DF) {
      /* file_name is a directory */
      /* Check to see if file_name is reachable.
       * That is, if it refers to the master file or
       * to the parent of the current directory or
       * to a child of the current directory.
       * 
       * Sept 2007: Added the case where the requested directory is
       * the already-selected directory (and is not MF).  This case was
       * missing from the published B model in "Practical Model-Based
       * Testing", and was discovered when executing randomly-generated
       * tests from this model against the sample implementation.
       */
      if (file_name == F_Name.MF
          || file_name == DF.name
          || temp_file == DF.parent
          || (temp_file.parent != null && temp_file.parent == DF)) {
            result = Status_Word.sw_9000;
            DF = temp_file;
            EF = null; /*@REQ: REQ1, REQ3, SELECT_FILE2, SELECT_FILE3, SELECT_FILE4 @*/
          }
          else {
            /* the directory file_name cannot be selected */
            result = Status_Word.sw_9404; /*@REQ: SELECT_FILE6 @*/
          }
    }
    else {
      /* file_name is a elementary file */
      if (temp_file.parent == DF) {
        /*? file_name is a child of the current directory ?*/
        result = Status_Word.sw_9000;
        EF = temp_file; /*@REQ: REQ2, SELECT_FILE2  @*/
      }
      else {
        /* file_name is not a child of the current directory 
         * and is not the current directory
         */
        result = Status_Word.sw_9405; /*@REQ: SELECT_FILE7 @*/
      }
    }
    
    if (sut != null) {
      sut.Select_file(file_name, result);
    }
  }

  @Action public void Read_Binary()
  {
    // pre: true

    /*? No current file selected ?*/
    if (EF == null) {
      result = Status_Word.sw_9400; /*@REQ: READ_BINARY2 @*/
    }
    else if (EF.perm_read == Permission.Always) {
      result = Status_Word.sw_9000;
      read_data = EF.data;  /*@REQ: READ_BINARY1, REQ4 @*/
    }
    else if (EF.perm_read == Permission.Never) {
      result = Status_Word.sw_9804; /*@REQ: READ_BINARY3, REQ5 @*/
    }
    else if (EF.perm_read == Permission.Adm) {
      result = Status_Word.sw_9804; /*@REQ: READ_BINARY3, REQ8 @*/
    }
    else if (perm_session) {
      result = Status_Word.sw_9000;
      read_data = EF.data; /*@REQ: READ_BINARY1, REQ6, REQ7 @*/
    }
    else {
      result = Status_Word.sw_9804; /*@REQ: READ_BINARY3 @*/
    }
    
    if (sut != null) {
      sut.Read_Binary(result, read_data);
    }
  }

  public static void main(String[] args) throws FileNotFoundException
  {
    System.out.println("Exploring the SimCard model without testing the SUT.");
    RandomTester tester = new GreedyTester(new SimCard(null));
    tester.setResetProbability(0.01);  // long test sequences
    GraphListener graph = tester.buildGraph(100000);
    graph.printGraphDot("gsm.dot");
    System.out.println("Graph contains "
        + graph.getGraph().numVertices() + " states and "
        + graph.getGraph().numEdges() + " transitions.");
  }
}
