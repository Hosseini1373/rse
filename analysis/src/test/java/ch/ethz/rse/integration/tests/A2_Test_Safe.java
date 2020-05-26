package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class A2_Test_Safe {
	public static void m3(int j) {
		TrainStation st = new TrainStation(100);
		st.arrive(14);
		st.arrive(16);
		st.arrive(1);
		}
}
