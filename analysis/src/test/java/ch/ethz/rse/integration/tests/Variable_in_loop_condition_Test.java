package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE

public class Variable_in_loop_condition_Test{
	

public static void m1(int j) {
    TrainStation s = new TrainStation(10);
     j = 10;
     for (int i = 0; i < j; i++ ) {
        // 0 <= i < 10
       s.arrive(i);
    }
}

}