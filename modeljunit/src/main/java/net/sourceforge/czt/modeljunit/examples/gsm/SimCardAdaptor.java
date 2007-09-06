package net.sourceforge.czt.modeljunit.examples.gsm;

import junit.framework.Assert;
import net.sourceforge.czt.modeljunit.examples.gsm.SimCard.F_Name;

/** This class connect the SimCard model to the GSM11Impl.
 *
 * @author marku
 */
public class SimCardAdaptor extends SimCard
{
  protected byte[] apdu = new byte[258];
  protected byte[] response = null;
  protected GSM11Impl sut = new GSM11Impl();

  /** Sets up the first few bytes of the APDU, ready to send to the SIM. */
  protected void initCmd(int cmdnum, int p1, int p2, int p3)
  {
    for (int i=0; i<apdu.length; i++)
      apdu[i] = 0;
    apdu[0] = (byte)0xA0;
    apdu[1] = (byte)(cmdnum & 0xFF);
    apdu[2] = (byte)(p1 & 0xFF);
    apdu[3] = (byte)(p2 & 0xFF);
    apdu[4] = (byte)(p3 & 0xFF);
  }

  protected void setWord(int pos, int value)
  {
    apdu[pos] = (byte) ((value >> 8) & 0xFF);
    apdu[pos+1] = (byte) (value & 0xFF);
  }

  /** Packs a PIN number (given as an int) into 8 bytes. */
  protected void setChv(int pos, int chv)
  {
    for (int i=1; i<=8; i++) {
      int digit = chv % 10;
      char ch = Character.forDigit(digit, 10);
      apdu[pos+8-i] = (byte) ch;
      chv = chv / 10;
    }
  }

  /** Translate a model filename into a real filename. */
  protected void setFileID(F_Name file)
  {
    switch (file) {
      case MF:         setWord(5, 0x3F00); break;
      case DF_GSM:     setWord(5, 0x7F20); break;
      case EF_LP:      setWord(5, 0x6F05); break;
      case EF_IMSI:    setWord(5, 0x6F07); break;
      case DF_Roaming: setWord(5, 0x5F30); break; // DF_IRIDIUM is under DF_GSM
      case EF_FR:      setWord(5, 0x4F21); break; // Under DF_IRIDIUM
      case EF_UK:      setWord(5, 0x4F22); break; // Under DF_IRIDIUM
      default: throw new RuntimeException("illegal file: "+file);
    }
  }

  protected int getWord(byte[] buf, int pos)
  {
    return ((buf[pos] & 0xFF) << 8) + (buf[pos+1] & 0xFF);
  }

  protected int getByte(byte[] buf, int pos)
  {
    return buf[pos] & 0xFF;
  }

  /** Check that an expected and actual status agree.
   *  @param expect  The expected status (from the model).
   *  @param position The position in {@code response} of the status word
   */
  protected void checkStatus(Status_Word expect, int position)
  {
    int actual = getWord(response, position);
    switch (expect) {
      // normal execution
      case sw_9000: Assert.assertEquals("expect 0x9000", 0x9000, actual); break;

      // file ID not found, or pattern not found
      case sw_9404: Assert.assertEquals("expect 0x9404", 0x9404, actual); break;

      // SHOULD BE 9404: file ID not found
      case sw_9405: Assert.assertEquals("expect 0x9404/5", 0x9404, actual); break;

      // access condition not fulfilled
      // unsuccessful CHV verification, at least one attempt left
      // unsuccessful UNBLOCK CHV verification, at least one attempt left
      // authentication failed (A Phase 1 SIM may send this error code
      //      after the third consecutive unsuccessful CHV verification
      //      attempt or the tenth consecutive unsuccessful unblocking attempt
      case sw_9804: Assert.assertEquals("expect 0x9804", 0x9804, actual); break;

      // unsuccessful CHV verification, no attempt left
      // unsuccessful UNBLOCK CHV verification, no attempt left
      // CHV blocked
      // UNBLOCK CHV blocked
      case sw_9840: Assert.assertEquals("expect 0x9840", 0x9840, actual); break;

      // in contradiction with CHV status
      case sw_9808: Assert.assertEquals("expect 0x9808", 0x9808, actual); break;

      // no EF selected
      case sw_9400: Assert.assertEquals("expect 0x9400", 0x9400, actual); break;
      default: throw new RuntimeException("Illegal model status: "+expect);
    }
  }

  @Override
  public void reset(boolean testing)
  {
    sut = new GSM11Impl(); // or just reset it?
    super.reset(testing);
  }

  @Override
  public void Verify_PIN(int Pin)
  {
    super.Verify_PIN(Pin);
    initCmd(0x20, 0x00, 0x01, 0x08);
    setChv(5, Pin);
    response = sut.cmd(apdu);
    checkStatus(super.result, 0);
  }

@Override
public void Unblock_PIN(int Puk, int new_Pin)
{
  super.Unblock_PIN(Puk, new_Pin);
  initCmd(0x2C, 0x00, 0x00, 0x10);
  setChv(5, Puk);
  setChv(13, new_Pin);
  response = sut.cmd(apdu);
  checkStatus(super.result, 0);
}

  @Override
  public void Enabled_PIN(int Pin)
  {
    super.Enabled_PIN(Pin);
    initCmd(0x28, 0x00, 0x01, 0x08);
    setChv(5, Pin);
    response = sut.cmd(apdu);
    checkStatus(super.result, 0);
  }

  @Override
  public void Disabled_PIN(int Pin)
  {
    super.Disabled_PIN(Pin);
    initCmd(0x26, 0x00, 0x01, 0x08);
    setChv(5, Pin);
    response = sut.cmd(apdu);
    checkStatus(super.result, 0);
  }

  @Override
  public void Change_PIN(int old_Pin, int new_Pin)
  {
    super.Change_PIN(old_Pin, new_Pin);
    initCmd(0x24, 0x00, 0x01, 0x10);
    setChv(5, old_Pin);
    setChv(13, new_Pin);
    response = sut.cmd(apdu);
    checkStatus(super.result, 0);
  }

  @Override
  public void Select_file(F_Name file_name)
  {
    super.Select_file(file_name);
    initCmd(0xA4, 0x00, 0x00, 0x02);
    setFileID(file_name);
    response = sut.cmd(apdu);
    if (super.result == Status_Word.sw_9000) {
      Assert.assertEquals("expect 0x9F", 0x9F, getByte(response,0));
      int length = getByte(response,1);
      // now send a GetResponse command to get the results
      initCmd(0xC0, 0x00, 0x00, length);
      response = sut.cmd(apdu);
      Assert.assertEquals(0x9000, getWord(response, length));
    }
    else {
      // we expect some kind of error
      checkStatus(super.result, 0);
    }
  }

  /**
   *  This always reads from offset 0, and reads just 2 bytes.
   */
  @Override
  public void Read_Binary()
  {
    super.Read_Binary();
    initCmd(0xB0, 0x00, 0x00, 0x02);
    response = sut.cmd(apdu);
    if (super.result == Status_Word.sw_9000) {
      Assert.assertEquals("expect 0x9F", 0x9F, getByte(response,0));
      int length = getByte(response,1);
      // now send a GetResponse command to read the first 2 bytes
      initCmd(0xC0, 0x00, 0x00, length);
      response = sut.cmd(apdu);
      // then check the first two bytes of the data
      if (length > 0)
        Assert.assertEquals(super.read_data.codePointAt(0), getByte(response,0));
      if (length > 1)
        Assert.assertEquals(super.read_data.codePointAt(1), getByte(response,1));
      Assert.assertEquals(0x9000, getWord(response, length));
    }
    else {
      // we expect some kind of error
      checkStatus(super.result, 0);
    }
  }
}
