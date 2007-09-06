package net.sourceforge.czt.modeljunit.examples.gsm;

import java.util.HashMap;
import java.util.Map;

/** This is a simple Java implementation of the GSM 11.11 standard.
 *  This class pretends to be the SIM card within a mobile phone,
 *  which manages the security and the contents of the various
 *  files and directories stored within a typical SIM card.
 *
 *  It handles only a very small subset of the files and directories
 *  that a real SIM would, supports only CHV1 security, and has many
 *  other limitations.
 *
 * @author marku
 *
 */
public class GSM11Impl
{
  /** The result buffer for the main commands (excluding GetResponse). */
  private byte[] result = new byte[258];

  /** The data that will be returned by the next GetResponse (if any). */
  private byte[] response_data = new byte[258];
  /** true when response_data is valid */
  private boolean response_available = false;

  ///////// security-related variables ////////////////
  private boolean chv1_enabled = true;
  private boolean chv1_blocked = false;
  private int chv1_attempts = 3;
  private boolean puk_blocked = false; // true after 10 bad attempts
  private boolean puk_success = false; // true after a successful unblockChv
  private int puk_attempts = 10;
  private byte[] chv1 = new byte[] {0x30,0x30,0x30,0x30,0x30,0x30,0x31,0x31};//00000011
  private byte[] puk = new byte[] {0x30,0x30,0x30,0x30,0x30,0x30,0x32,0x32};//00000022

  public static final int MF = 0x3F00;
  /** This defines all the files in the SIM.
   *  Each file starts with a two byte header, which gives its parent.
   *  (the MF has a parent of 0).  Directories contain only this,
   *  so we assume that all files of length 2 are directories.
   */
  private Map<Integer, byte[]> files = new HashMap<Integer,byte[]>();
  public static final int DF_GSM = 0x7F20;
  public static final int EF_LP = 0x2F05;

  private int currentDir = MF;  // always a valid directory
  private int currentFile = 0;  // 0 means none selected

  public GSM11Impl()
  {
    // initialise all the files with dummy data.
    files.put(MF, new byte[] {0x00, 0x00});

    files.put(DF_GSM, new byte[] {0x3F, 0x00});
    // EF_LP (under DF_GSM)
    files.put(0x6F05, new byte[] {0x7F, 0x20, 0x64, 0x31}); // "d1"
    // EF_ISMI (under DF_GSM)
    files.put(0x6F07, new byte[] {0x7F, 0x20, 0x64, 0x32}); // "d2"

    // DF_IRIDIUM (a directory containing some imaginary supplier-specific files)
    files.put(0x5F30, new byte[] {0x7F, 0x20}); // under DF_GSM
    files.put(0x4F21, new byte[] {0x5F, 0x30, 0x64, 0x33}); // "d3"
    files.put(0x4F22, new byte[] {0x5F, 0x30, 0x64, 0x34}); // "d4"
  }

  /** This corresponds to sending a command to the SIM.
   *  It returns an array of bytes as a response.
   *  The caller is expected to know the length of the
   *  valid data within the returned array (typically 0), and
   *  the position of the two status bytes that follow the data.
   *  Note that in this Java implementation, the returned array
   *  may be reused, so successive calls will overwrite the contents.
   *
   * @param apdu Bytes 1..4 determine the command and its parameters
   * @return     The response array (ignore the length).
   */
  public byte[] cmd(byte[] apdu)
  {
    // clear the result buffer
    for (int i=0; i<result.length; i++) {
      result[i] = 0;
    }
    if ((apdu[0] & 0xFF) == 0xA0) {
      int offset, length, chvnum;
      // A GSM request
      switch (apdu[1] & 0xFF) {
        case 0xA4:
          select(getWord(apdu,5));
          break;

        case 0xF2:  // status
          length = apdu[4] & 0xFF;
          status(length);
          break;

        case 0xB0:  // read binary
          offset = getWord(apdu, 2);
          length = apdu[4] & 0xFF;
          readBinary(offset, length);
          break;

        case 0xD6:  // update binary
          offset = getWord(apdu, 2);
          length = apdu[4] & 0xFF;
          updateBinary(offset, length);
          break;

        case 0x20:
          chvnum = apdu[3];
          verifyChv(chvnum, apdu, 5);
          break;

        case 0x24:
          chvnum = apdu[3];
          changeChv(chvnum, apdu, 5, 13);
          break;

        case 0x26:
          disableChv(apdu, 5);
          break;

        case 0x28:
          enableChv(apdu, 5);
          break;

        case 0x2C:
          unblockChv((int)apdu[3], apdu, 5, 13);
          break;

        case 0xC0:
          if ( ! response_available) {
            throw new RuntimeException("Illegal GetResponse call");
          }
          length = apdu[4] & 0xFF;
          setWord(response_data, length, 0x9000);
          response_available = false;
          return response_data;

        default:
          setWord(result, 0, 0x6D00); // unknown command
      }
    }
    else {
      setWord(result, 0, 0x6E00); // wrong instruction class (not 0xA0)
    }
    return result;
  }

  private void unblockChv(int i, byte[] buf, int unblock_pos, int new_pos)
  {
    if (puk_blocked) {
      setWord(result, 0, 0x9840); // PUK is blocked
    }
    else if (equalsChv(puk, 0, buf, unblock_pos)) {
      puk_attempts = 10;
      chv1_attempts = 3;
      chv1_enabled = false;
      chv1_blocked = false;
      setWord(result, 0, 0x9000); // success
    }
    else {
      puk_attempts--;
      if (puk_attempts > 0) {
        setWord(result, 0, 0x9804); // at least one attempt left
      }
      else {
        puk_blocked = true; // does not change chv1 status
        setWord(result, 0, 0x9840); // no attempts left
      }
    }
  }

  private void enableChv(byte[] buf, int chvpos)
  {
    if (chv1_blocked) {
      // this operation is blocked
      setWord(result, 0, 0x9840); // CHV is blocked
    }
    else if (chv1_enabled) {
      setWord(result, 0, 0x9808); // contradiction: should not have been called
    }
    else if (canVerifyChv(buf, chvpos)) {
      chv1_enabled = true;
    }
  }

  private void disableChv(byte[] buf, int chvpos)
  {
    if (chv1_blocked) {
      // this operation is blocked
      setWord(result, 0, 0x9840); // CHV is blocked
    }
    else if ( ! chv1_enabled) {
      setWord(result, 0, 0x9808); // contradiction: should not have been called
    }
    else if (canVerifyChv(buf, chvpos)) {
      chv1_enabled = false;
    }
  }

  private void changeChv(int chvnum, byte[] buf, int old_pos, int new_pos)
  {
    if (chv1_blocked) {
      setWord(result, 0, 0x9840); // CHV is blocked
    }
    else if (! chv1_enabled) {
      setWord(result, 0, 0x9808); // Cannot change CHV while disabled???
    }
    else if (canVerifyChv(buf, old_pos)) {
      // copy the new chv into our internal chv
      for (int i=0; i<8; i++) {
        chv1[i] = buf[new_pos+i];
      }
    }
  }

  private void verifyChv(int chvnum, byte[] buf, int chvpos)
  {
    if (chv1_blocked) {
      // this operation is blocked
      setWord(result, 0, 0x9840); // CHV is blocked
    }
    else if ( ! chv1_enabled) {
      setWord(result, 0, 0x9808); // contradiction: should not have been called
    }
    else {
      canVerifyChv(buf, chvpos);
    }
  }

  private void updateBinary(int offset, int length)
  {
    // TODO Auto-generated method stub
    throw new RuntimeException("updateBinary not implemented yet");
  }

  private void readBinary(int offset, int length)
  {
    if (chv1_blocked) {
      setWord(result, 0, 0x9840); // CHV is blocked
    }
    else if (true) { // todo: or if UnblockChv been done
      // TODO
    }
  }

  private void status(int length)
  {
    // TODO Auto-generated method stub
    throw new RuntimeException("status not implemented yet");
  }

  /** Note: this does not yet return all the correct data
   * (CHV status, available memory, etc.) in the GetResponse buffer.
   * @param fileId
   */
  private void select(int fileId)
  {
    if (fileId == DF_GSM) {
      System.out.println("DF_GSM");
    }
    byte[] dir = files.get(currentDir);
    byte[] contents = files.get(fileId);  // null if unknown
    if (contents == null) {
      setWord(result, 0, 0x9404);  // fileId not known
    }
    else if (fileId == MF
        || fileId == currentDir
        || (fileId == getWord(dir, 0) && contents != null)
        || (contents != null
            && getWord(contents,0) == currentDir)) {
      // a valid selection
      response_available = true;
      if (isDirectory(contents)) {
        // valid selection of a directory
        currentDir = fileId;
        currentFile = 0; // none
        setWord(result, 0, 0x9F00 + 34); // upto 34 bytes of data
      }
      else {
        // valid selection of an EF within the current directory
        currentFile = fileId;
        setWord(result, 0, 0x9F00 + 15); // upto 15 bytes of data
      }
    }
    else {
      setWord(result, 0, 0x9404); // file not found
    }
    setWord(response_data, 5, fileId);
  }

  
  /////////////////////////////////////////////////////////////////
  //  Helper Methods
  /////////////////////////////////////////////////////////////////
  
  /** Reads a two-byte word from buf[pos..pos+1]. */
  protected int getWord(byte[] buf, int pos)
  {
    return ((buf[pos] & 0xFF) << 8) + (buf[pos+1] & 0xFF);
  }

  /** Writes a two-byte word into buf[pos..pos+1]. */
  protected void setWord(byte[] buf, int pos, int value)
  {
    buf[pos] = (byte) ((value >> 8) & 0xFF);
    buf[pos+1] = (byte) (value & 0xFF);
  }

  /** True if chv1[pos1..pos+7] equals chv2[pos2..pos2+7]. */
  protected boolean equalsChv(byte[] chv1, int pos1, byte[] chv2, int pos2)
  {
    for (int i=0; i<8; i++) {
      if (chv1[pos1+i] != chv2[pos2+i]) {
        System.out.println("byte "+i+" of chv differs: '"
            + (char)chv1[pos1+i] + "' != '" + (char)chv2[pos2+i] + "'");
        return false;
      }
    }
    return true;
  }

  /** An internal method that checks the given Chv for correctness.
   *  @return true if the given CHV is correct.
   */
  private boolean canVerifyChv(byte[] buf, int chvpos)
  {
    if (equalsChv(chv1, 0, buf, chvpos)) {
      chv1_attempts = 3;
      setWord(result, 0, 0x9000); // success
      return true;
    }
    chv1_attempts--;
    if (chv1_attempts > 0) {
      setWord(result, 0, 0x9804); // at least one attempt left
    }
    else {
      chv1_blocked = true;
      chv1_enabled = true;
      setWord(result, 0, 0x9840); // no attempts left
    }
    return false;
  }

  private boolean isDirectory(byte[] file)
  {
    return file.length == 2;
  }
}
