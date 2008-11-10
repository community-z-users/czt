package net.sourceforge.czt.modeljunit.examples;

import java.util.Random;

import net.sourceforge.czt.modeljunit.Action;
import net.sourceforge.czt.modeljunit.GraphListener;
import net.sourceforge.czt.modeljunit.GreedyTester;
import net.sourceforge.czt.modeljunit.Tester;
import net.sourceforge.czt.modeljunit.timing.Time;
import net.sourceforge.czt.modeljunit.timing.TimedFsmModel;
import net.sourceforge.czt.modeljunit.timing.TimedModel;
import net.sourceforge.czt.modeljunit.timing.Timeout;

public class TrafficLight implements TimedFsmModel {

	/**Whether the pedestrian button has been pressed*/
	private boolean buttonPressed;
	
	private STATE state;
	
	/**
	 * The length of time that both lights are red in between changing
	 * who can use the crossing
	 */
	private static final int SAFETY_PERIOD = 5;
	
	/**
	 * The minimum time that the light must stay green for cars. 
	 *  This ensures that traffic can flow freely through the 
	 *  intersection without constantly being interrupted by pedestrians.
	 */
	private static final int MINIMUM_TRAFFIC_PERIOD = 20;
	
	/**
	 * The length of time that the light stays green for pedestrians
	 * while they cross.
	 */
	private static final int CROSSING_TIME = 10;
	
	/**
	 * This timer controls the minimum 20 second period in which
	 * the light must be green for cars.When the timer expires
	 * the minimumWaitElapsed action will be called
	 */
	@Timeout("minimumWaitElapsed") public int trafficFlowTimer = 0;
	
	/**
	 * This timer controls the period in which the light is green for
	 * pedestrians to cross.
	 */
	@Timeout("finishPedestrianPeriod") public int crossingTimer = 0;
	
	/**
	 * Timer to control the saftey period where both lights are red
	 * because the lights are changing from allowing cars through
	 * to allowing predestrians to cross
	 */
	@Timeout("allowPedestrians") public int allowPedestriansTimer = 0;
	
	/**
	 * Timer to control the safety period where both lights are red
	 * because the lights are changing from allowing pedestrians to cross 
	 * to allowing cars through
	 */
	@Timeout("allowCars") public int allowCarsTimer = 0;
	
	/**
	 * The current time of the model
	 */
	@Time public int now = 0;
	
	/**
	 * Random generator for generating time increments.
	 */
	private Random rand = new Random();
	
	public enum STATE {
		CARS_HOLD,			//The period while the light is held green even if the button gets pressed
		CARS,				//Regular state for allowing cars to move through
		WAIT_CARS,			//safety period after cars have been crossing
		PEDESTRIANS,		//period where pedestrians cross
		WAIT_PEDS			//safety period after pedestrians cross
	}
	
	@Override
	public Object getState() {
		return state;
	}

	@Override
	public void reset(boolean testing) {
		now = getNextTimeIncrement();
		buttonPressed = false;
		crossingTimer = 0;
		allowPedestriansTimer = 0;
		
		state = STATE.CARS_HOLD;
		trafficFlowTimer = now + MINIMUM_TRAFFIC_PERIOD;

	}
	
	/**
	 * Action for pedestrians arriving at the crossing. This can
	 * happen at any time so no guard is needed because it would
	 * always return true
	 */
	@Action public void pedestrianArrive() {
		if(state == STATE.PEDESTRIANS) {
			//they can walk right through
			return;
		}
		//In all other states they must press the button and wait
		buttonPressed = true;
		
		if(state == STATE.CARS) {
			state = STATE.WAIT_CARS;
			allowPedestriansTimer = now + SAFETY_PERIOD;
		}
	}
	
	/**
	 * Guard for the safetyPeriodEnd action. We only want this
	 * action to occur when the safetyTimer expires so the guard 
	 * is set up to do this.
	 * @return
	 */
	public boolean allowPedestriansGuard() {
		return now == allowPedestriansTimer;
	}
	
	@Action public void allowPedestrians() {
		//clear the timer
		allowPedestriansTimer = 0;

		//we now move to the state where pedestrians can cross
		state = STATE.PEDESTRIANS;
		//set the timer for when the light should finish
		crossingTimer = now + CROSSING_TIME;
		
		buttonPressed=false;
	}
	
	public boolean allowCarsGuard() {
		return now == allowCarsTimer;
	}
	
	@Action public void allowCars() {
		allowCarsTimer = 0;
	
		//move to the state where the light must remain green for cars
		state = STATE.CARS_HOLD;
		//set the timer for when this period ends
		trafficFlowTimer = now + MINIMUM_TRAFFIC_PERIOD;
	
	}
	
	public boolean minimumWaitElapsedGuard() {
		return now == trafficFlowTimer;
	}
	
	@Action public void minimumWaitElapsed() {
		trafficFlowTimer = 0;
		
		if(buttonPressed) {
			//the pedestrian button has been pressed.
			//go to the safety period so we can let the pedestrians cross
			//in a moment
			state = STATE.WAIT_CARS;
			allowPedestriansTimer = now + SAFETY_PERIOD;
		} else {
			state = STATE.CARS;
		}
	}
	
	public boolean finishPedestrianPeriodGuard() {
		return now == crossingTimer;
	}
	
	@Action public void finishPedestrianPeriod() {
		crossingTimer = 0;
		state = STATE.WAIT_PEDS;
		allowCarsTimer = now + SAFETY_PERIOD;
	}
	
	public static void main(String[] args) {
		TimedModel model = new TimedModel(new TrafficLight());
		Tester tester = new GreedyTester(model);
		tester.addListener("verbose");
		GraphListener graphListener = tester.buildGraph();
		try{
			graphListener.printGraphDot("TrafficLight.dot");
		}
		catch(Exception ex) {
			System.out.println(ex.getMessage());
		}
	}

	/**
	 * Take random steps of between 1 and 10 time units (inclusive)
	 */
	@Override
	public int getNextTimeIncrement() {
		return rand.nextInt(10) + 1;
	}
	
	

}
