package net.sourceforge.czt.modeljunit.timing;

import java.util.Random;

import junit.framework.TestCase;
import net.sourceforge.czt.modeljunit.Action;


public class TimedModelTest extends TestCase{
	
	
	public void testLoadModel() {
		TimedModel model = new TimedModel(new PhoneModel());
		
		//make sure the Time and 2 Timeouts were read properly
		assertEquals(0,model.getTime());
		assertEquals("dialTimeout", model.getTimeoutName(0));
		assertEquals("hangUpTimeout", model.getTimeoutName(1));
		
		model = new TimedModel(new BogusFSM());
		
		
	}
	
	public void testInvalidTimeouts() {
		TimedModel model = new TimedModel(new PhoneModel());
		
	}
	
	public void testReset() {
		//TODO
	}
	
	
	
	public void testIncrementTime() {
		SimpleTimedFSM simpleFSM = new SimpleTimedFSM();
		TimedModel model = new TimedModel(simpleFSM);
		
		assertEquals(0,model.getTime());
		simpleFSM.action1Timer = 55;
		simpleFSM.action2Timer = 60;
		simpleFSM.action3Timer = 65;
		
		assertTrue(model.incrementTime());
		assertTrue(model.getTime() >= 1);
		assertTrue(model.getTime() <= 10);
		
		model.setTime(50);
		if(model.incrementTime()) {
		//time must be less than the timeout value
			assertTrue(model.getTime() >= 51);
			assertTrue(model.getTime() < 55);
		}
		
		model.setTime(54);
		assertFalse(model.incrementTime());
		assertEquals(54, model.getTime());
		
		
		
	}
	
	
	
	
	public void testGetTime() {
		PhoneModel phoneFSM = new PhoneModel();
		TimedModel model = new TimedModel(phoneFSM);
		
		assertEquals(0, phoneFSM.now);
		assertEquals(0, model.getTime());
		
		phoneFSM.now = 10;
		assertEquals(10, phoneFSM.now);
		assertEquals(10, model.getTime());
		
		model.setTime(11);
		assertEquals(11,model.getTime());
		assertEquals(model.getTime(),phoneFSM.now);
	}
	
	
	
	public void testTimeoutsBasic() {
		SimpleTimedFSM FSM = new SimpleTimedFSM();
		TimedModel model = new TimedModel(FSM);
		
		assertEquals(5, FSM.action1Timer);
		assertEquals(0, FSM.now);
		
		assertTrue(model.doAction(model.getActionNumber("action3")));
		assertTrue(FSM.getState().equals("3"));
		
		assertFalse(FSM.now > 5);
		
		if(FSM.now == 5){
			//must do timeout
			assertFalse(model.doAction(model.getActionNumber("action2")));
			assertFalse(model.doAction(model.getActionNumber("action3")));
			assertTrue(model.doAction(model.getActionNumber("action1")));
			
			assertTrue(FSM.getState().equals("31"));
		}
		
		
		//now set it up so two timeouts are at same time and we are timed out
		FSM.action1Timer = 20;
		FSM.action2Timer = 20;
		FSM.now = 19;
		assertTrue(model.doAction(model.getActionNumber("action3")));
		assertEquals(FSM.action1Timer, FSM.now);
		
		//action1 should occur first because it is declared first
		assertFalse(model.doAction(model.getActionNumber("action2")));
		assertTrue(model.doAction(model.getActionNumber("action1")));
		assertEquals(FSM.action2Timer, FSM.now);
		assertFalse(model.doAction(model.getActionNumber("action1")));
		assertTrue(model.doAction(model.getActionNumber("action2")));
		assertTrue(FSM.now > 20);
		
		
	}

	public void testGetLowestTimeout() {
		SimpleTimedFSM simpleFSM = new SimpleTimedFSM();
		TimedModel model = new TimedModel(simpleFSM);
		
		simpleFSM.action1Timer = 20;
		simpleFSM.action2Timer = 10;
		simpleFSM.action3Timer = 15;
		
		assertEquals("action2Timer",model.getLowestTimeout().getName());
		
		simpleFSM.action1Timer = 0;
		simpleFSM.action2Timer = 0;
		simpleFSM.action3Timer = 0;
		
		assertNull(model.getLowestTimeout());
	}
}




/**
 * A simple example class to test the TimedModel class
 * TODO: Put this in its own class as an example
 * @author Scott
 *
 *	In this model keys can be pressed at any time. If there is a delay
 *	of more than 10 seconds between key presses then the system attempts
 *	to dial the number. If more than 7 digits have been entered then it
 *	can call the number, otherwise dialing fails. If a call is successfully
 * 	started then exactly 60 seconds later the phone will be hung up.
 */
class PhoneModel implements TimedFsmModel {
	public PhoneModel() {
		
	}
	/*The current time*/
	@Time public int now;
	
	@Timeout("dial") public int dialTimeout = 0;
	
	@Timeout("hangUp") public int hangUpTimeout = 0;
	
	/*The number of key presses*/
	private int keysPressed = 0;
	/*Whether the phone is calling someone.*/
	private boolean calling = false;
	
	public boolean pressKeyGuard() {
		return !calling;
	}
	/**
	 * Action for pressing a key. Action is enabled as long as
	 * the phone is not currently calling someone.
	 */
	@Action public void pressKey() {
		keysPressed++;
		dialTimeout = now + 10;		//timeout set for 10 seconds in the future
	}
	
	public boolean dialGuard() {
		return !calling;
	}
	/**
	 * Action for dialling the number. 
	 */
	@Action public void dial() {
		if(keysPressed >= 7) {
			calling = true;
			//set the hangUpTimeout to expire in 60 seconds
			hangUpTimeout = now + 60;
		} else {
			keysPressed = 0;	//reset the phone
		}
	}
	
	/**
	 * Guard for hanging up a call. This is only ever done through a timeout
	 * so the guard returns false unless the timer for hanging up has expired.
	 * @return
	 */
	public boolean hangUpGuard() {
		return calling && hangUpTimeout == now;		
	}
	
	@Action public void hangUp() {
		calling = false;
		keysPressed = 0;
		hangUpTimeout = -1;
	}

	
	
	
	
	@Override
	public String getState() {
		if(keysPressed == 0) {
				return "IDLE";
		}
		else {
			if(calling) 
				return "CALLING";
			else
				return "DIALING";
		}
		
	}

	@Override
	public void reset(boolean testing) {
		keysPressed = 0;
		dialTimeout = 0;
		
	}
	@Override
	public int getNextTimeIncrement() {
		// Constant increments of two time units
		return 2;
	}
}

/**
 * Simple FSM for testing. Note: with the current implementation of this
 * class it actually has a an infinite number of states. I just wanted a class
 * where I could see exactly what the sequence of states has been.
 * @author Scott
 *
 */
class SimpleTimedFSM implements TimedFsmModel {

	private String state = "";
	private Random rand = new Random(12345);
	
	@Time public int now;
	
	@Timeout("action1") public int action1Timer;
	@Timeout("action2") public int action2Timer;
	@Timeout("action3") public int action3Timer;
	
	@Action public void action1() {
		state += "1";
		action1Timer = -1;
	}
	
	@Action public void action2() {
		state += "2";
		action2Timer = -1;
	}
	
	@Action public void action3() {
		state += "3";
		action3Timer += 10;
	}
	
	@Override
	public Object getState() {
		return state;
	}

	@Override
	public void reset(boolean testing) {
		action1Timer = 5;
		action2Timer = 30;
		action3Timer = 10;
		state = "";
		
	}

	@Override
	public int getNextTimeIncrement() {
		// TODO Auto-generated method stub
		return rand.nextInt(10) + 1;
	}
	
	
}

class BogusFSM implements TimedFsmModel {

	private String state = "";
	
	@Timeout("") public int t1;
	@Timeout("action2") private int t2;
	@Timeout("action3") public float t3;
	
	@Override
	public int getNextTimeIncrement() {
		return 0;
	}

	@Override
	public Object getState() {
		return state;
	}

	@Override
	public void reset(boolean testing) {
		// TODO Auto-generated method stub
		
	}
	
	@Action public void action2(){}
	
	@Action public void action3(){}
	
}