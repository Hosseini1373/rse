package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class A4_Test_Safe {
	
	public static void example(int j) {
		TrainStation s = new TrainStation(10);
		
		int i = 2; 
		int a = 2;
		while(i*a < 10) {
			s.arrive(i);
			
			i++;
			a++;
		}
	}
	
}
