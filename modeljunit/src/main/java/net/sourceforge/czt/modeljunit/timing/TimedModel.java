package net.sourceforge.czt.modeljunit.timing;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.Model;
import net.sourceforge.czt.modeljunit.TestFailureException;
import net.sourceforge.czt.modeljunit.Transition;

import junit.framework.Assert;
/**
 * An extension of the model class which supports timed models.
 * @author ScottT
 *
 */
public class TimedModel extends Model{


	/**The Timeouts of the FSM.*/
	private ArrayList <Field> timeouts_ ;
	/**The single Time annotation.*/
	private Field time_;
	
	private boolean timedOut;
	private String timeoutAction = "";
	/**Random generator for internal use. Used to decide whether to
	 * do a time increment or a timeout next.
	 */
	private Random rand;
	
	private double timeoutProbability = 0.5;
		
	public TimedModel(TimedFsmModel model) {
		super(model);
		rand = new Random(12345);		//fixed seed for now
	}
	
	
	/**
	 * {@inheritDoc}
	 */
	@Override
	public void loadModelClass(Class fsm) {
		super.loadModelClass(fsm);
		
		if(timeouts_ == null) {
			timeouts_ = new ArrayList<Field>();
		}
		
		for(Field field : fsm.getFields()) {
			if(field.isAnnotationPresent(Time.class)) {
				if(field.getType() == int.class) {
					time_ = field;
				} else {
					printWarning("@Time field " + field.getName() 
							+ "should be of type int.");
				}
			}
			
			else if(field.isAnnotationPresent(Timeout.class)) {
				if(verifyTimeout(field, fsm))
				{
					timeouts_.add(field);
				}
			}
		}
		
		//TODO: check that there is exactly one Time annotation (?)
	}
	
	/**
	 * Verifies that a Timeout is valid in a given FSM. It must be an integer
	 * and the action name provided as an annotation must correspond
	 * to and Action method.
	 * @param field the Timeout to verify
	 * @param fsm the FSM the the Timeout exists in
	 * @return true if the Timeout is valid, false otherwise
	 */
	private boolean verifyTimeout(Field field, Class fsm) {
		//Timeouts must be integers
		if(field.getType() != int.class) {
			printWarning("Timeout: " + field.getName() + "-Timeouts must be of type int");
			return false;
		}
		
		//Action name must correspond to an action method
		String actionName = field.getAnnotation(Timeout.class).value();
		for(Method method : fsm.getMethods()) {
			if(method.isAnnotationPresent(Action.class)) {
				if(method.getName().equals(actionName)) {
					return true;
				}
			}
		}
		
		//no corresponding action
		printWarning("Timeout: " + field.getName() + "-No corresonding action was found");
		return false;

	}
	

	

	/**
	 * Partitioning actions to make sure that only tick actions can happen
	 * when in a tick state
	 */
	@Override public int enabled(int index) {
		if(timedOut) {
			if(getActionName(index).equals(timeoutAction)) {
				return super.enabled(index);
			}
			else
				return 0;
		}
		
		return super.enabled(index);
	}
	
	@Override
	public void doReset(String reason) {
		super.doReset(reason);
		timedOut = false;
		fsmState_ = fsmModel_.getState();
	};
	
	@Override
	public boolean doAction(int index) {
		 if (! isEnabled(index)) {
			 return false;
		 }
		        
		 
		 if(timedOut) {
			 assert getActionName(index).equals(timeoutAction);
			 timeoutAction = "";
			 timedOut = false;
		 }

		int startTime = getTime();
		Method m = fsmActions_.get(index);
		try {
			notifyStartAction(fsmState_, index, m.getName());
			m.invoke(fsmModel_, VOID_ARGS);
			
		}
		catch (InvocationTargetException ex) {
			String failmsg = "failure in action "+m.getName()
			+" from state "+this.fsmState_+" due to "+ex.getCause();
			createTestFailure(failmsg, m.getName());
		}
		catch (IllegalAccessException ex) {
			Assert.fail("Model Error: Non-public actions? "+ex);
			return false;
		}

		Object newState = fsmModel_.getState();

		//now either increment the time or do the lowest timeout
		if(rand.nextDouble() > timeoutProbability) {
			//try to increment the time
			if(!incrementTime())
			{
				//we cound't increment the time so we must have a timeout to do
				doLowestTimeout();
			}
		}
		else {
			//try to do the lowest timeout
			if(!doLowestTimeout()) {
				//no timeouts to do so increment the time
				incrementTime();
			}
				
		}
		if(!newState.equals(fsmModel_.getState())) {
			//changing the time caused a state change
			String failmsg = "Failure in action "+m.getName()
			+" from state "+ fsmState_ +". Model state should not change "
			+ "when changing the time. Use Timeouts to control time dependant states.";
			createTestFailure(failmsg, m.getName());
			
		}
		
		Transition done = new TimedTransition(startTime,fsmState_, m.getName(), newState);
		fsmSequence_.add(done);
		fsmState_ = newState;
		Assert.assertNotNull("Model Error: getState() must be non-null", fsmState_);				 

		notifyDoneTransition(index, done);
		return true;
	}


	/**
	 * TODO: Change TestFailureException to FsmException in case where 
	 * 	changing time causes a state change
	 * @param failmsg
	 * @param actionName
	 */
	private void createTestFailure(String failmsg, String actionName) {
		TestFailureException failure =
			new TestFailureException(failmsg);
		failure.setActionName(actionName);
		failure.setModel(this.fsmModel_);
		failure.setModelName(this.getModelName());
		failure.setSequence(this.fsmSequence_);
		failure.setState(this.fsmState_);
		notifyFailure(failure);

	}


	/**
	 * Gets the current Time of the model. Uses reflection
	 * to retrieve the Time value in the FSM object.
	 * @return 
	 */
	public int getTime() {
		if(time_ != null) {
			try{
				return time_.getInt(getModel());
			}
			catch(Exception ex) {
				System.out.println(ex.getMessage());
			}
		}
		return -1;
	}
	
	/**
	 * Sets the current time in the FSM object.
	 * @param value
	 */
	public void setTime(int value) {
		try{
			time_.setInt(getModel(),value);
		}
		catch(Exception ex) {
			System.out.println(ex.getMessage());
		}
	}

	/**
	 * Increment the current time by a random value between the minimum
	 * and maximum delays.
	 * 
	 * If the time can be incremented by at least the minimum delay without
	 * going past any timeouts then the time will be incremented between either
	 * minDelay and max Delay or minDelay and lowestTimeout
	 * 
	 * @return true if the time was changed, otherwise false
	 */
	public boolean incrementTime() {
		
		Field lowest = getLowestTimeout();
		int currTime = getTime();
		int increment = ((TimedFsmModel)fsmModel_).getNextTimeIncrement();
		if(increment <= 0) {
			createTestFailure("Invalid time increment: " + increment + 
					". All time increments must be greater than zero.",
					"tick");
		}
		
		try{
			if(lowest == null) {
				//no timeouts set
				setTime(currTime + increment);
				return true;
			}
			else {
				int maxTime = lowest.getInt(getModel())-1;
				if(currTime + increment <= maxTime ) {
					//The increment will not go past the lowest timeout
					setTime(currTime + increment);
					return true;
				}else {
					//incrementing time will take us past a timeout
					return false;
				}
			}
		}catch (IllegalAccessException ex) {
			//TODO: is this because of public/private?
			ex.printStackTrace();
			return false;
		}
			
		
	}
		
	/**
	 * Gets the timeout that will expire next in the model.
	 * If no timeouts are set then null is returned
	 * @return
	 */
	public Field getLowestTimeout(){ 
		int lowestTimeout = Integer.MAX_VALUE;
		Field lowest = null;
		try{
			//find the lowest timeout first
			for(Field field : timeouts_) {
				int value = field.getInt(getModel());
				if(value > 0) {
					//timer is set
					if(value < lowestTimeout) {
						lowestTimeout = value;
						lowest = field;
					}
				}
			}
		}
		catch(Exception ex) {
			ex.printStackTrace();
		}
		return lowest;
	}
	
	/**
	 * Gets the value of the lowest enabled timeout. Returns
	 * Integer.MIN_VALUE if no timeouts are set.
	 * @return
	 */
	public int getLowestTimeoutValue() {
		Field lowest = getLowestTimeout();
		if(lowest == null) {
			return Integer.MIN_VALUE;
		}
		else {
			try {
				return lowest.getInt(getModel());
			} catch (Exception e) {
				e.printStackTrace();
				return Integer.MIN_VALUE;
			}
			
		}
			
	}
	
	private boolean doLowestTimeout() {
		Field lowest = getLowestTimeout();
		
		if(lowest == null)
			return false;
		
		//set the time to the timeout value
		try {
			setTime(lowest.getInt(getModel()));
			
			timeoutAction = lowest.getAnnotation(Timeout.class).value();
			timedOut = true;
		} catch (Exception e) {
			e.printStackTrace();
			return false;
		}

		return true;
	}

	public String getTimeoutName(int index) {
		if(timeouts_ == null ||index >= timeouts_.size())
			return "";
		
		return timeouts_.get(index).getName();
	}
	
	public double getTimeoutProbability() {
		return timeoutProbability;
	}
	
	public void setTimeoutProbability(double value) {
		timeoutProbability = value;
	}

}
