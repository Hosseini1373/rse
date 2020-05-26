package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE UNSAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class Test_MultipleTrainStations {
		
	public void m3() {
		TrainStation t1 = new TrainStation(10);
		TrainStation t2 = new TrainStation(10);
		
		for(int j=0 ; j<10; j++) {
			t1.arrive(j-1);
			t2.arrive(j-1);
		}
	}
}
