package net.sourceforge.czt.modeljunit.examples.gsm;

/** This is a simple Java implementation of the GSM 11.11 standard.
 *  This class pretends to be the SIM card within a mobile phone,
 *  which manages the security and the contents of the various
 *  files and directories stored within a typical SIM card.
 *
 * @author marku
 *
 */
public class GSM11Impl
{
  private byte[] result = new byte[258];

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
    if (apdu[0] == 0xA0) {
      int offset, length, chvnum;
      // A GSM request
      switch (apdu[1]) {
        case (byte)0xA4:
          select();
          break;

        case (byte)0xF2:  // status
          length = apdu[3] & 0xFF;
          status(length);
          break;

        case (byte)0xB0:  // read binary
          offset = (apdu[2] & 0xFF) << 8 + (apdu[3] & 0xFF);
          length = apdu[3] & 0xFF;
          readBinary(offset, length);
          break;

        case (byte)0xD6:  // update binary
          offset = apdu[2] << 8 + apdu[3];
          length = apdu[3] & 0xFF;
          updateBinary(offset, length);
          break;

        case (byte)0x20:
          chvnum = apdu[2];
          verifyChv(chvnum);
          break;

        case (byte)0x24:
          chvnum = apdu[2];
          changeChv(chvnum);
          break;

        case (byte)0x26:
          disableChv();
          break;

        case (byte)0x28:
          enableChv();
          break;

        case (byte)0x2C:
          unblockChv((int)apdu[2]);
          break;

        case (byte)0xC0:
          length = apdu[3] & 0xFF;
          getResponse(length);
          break;

        default:
          throw new RuntimeException("Unknown cmd="+(apdu[1]&0xFF));
      }
    }
    return result;
  }

  private void getResponse(int length)
  {
    // TODO Auto-generated method stub

  }

  private void unblockChv(int i)
  {
    // TODO Auto-generated method stub

  }

  private void enableChv()
  {
    // TODO Auto-generated method stub

  }

  private void disableChv()
  {
    // TODO Auto-generated method stub

  }

  private void changeChv(int chvnum)
  {
    // TODO Auto-generated method stub

  }

  private void verifyChv(int chvnum)
  {
    // TODO Auto-generated method stub

  }

  private void updateBinary(int offset, int length)
  {
    // TODO Auto-generated method stub

  }

  private void readBinary(int offset, int length)
  {
    // TODO Auto-generated method stub

  }

  private void status(int length)
  {
    // TODO Auto-generated method stub

  }

  private void select()
  {
    // TODO Auto-generated method stub

  }
}
