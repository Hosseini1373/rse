package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class A1_Test_Safe {
	public static void m3(int j) {
		  TrainStation st = new TrainStation(500);
		  for (int i = 0; i < 20; i++) {
		    st.arrive(i);
		    i += 4;
		    i -= 3;
		    st.arrive(i);
		    i += 1;
		    st.arrive(i);
		  }
		}
}
