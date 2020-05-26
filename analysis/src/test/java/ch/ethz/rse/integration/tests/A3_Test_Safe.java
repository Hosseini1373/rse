package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class A3_Test_Safe {
	public static void m3(int x) {
		TrainStation st = new TrainStation(100);
		for (int j = 20; j >= 0; j--) {
				st.arrive(j);
		}
	} 
}
