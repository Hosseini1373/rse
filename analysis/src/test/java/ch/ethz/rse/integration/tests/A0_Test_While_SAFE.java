package ch.ethz.rse.integration.tests;

import ch.ethz.rse.TrainStation;

// expected results:
// TRACK_NON_NEGATIVE SAFE
// TRACK_IN_RANGE SAFE
// NO_CRASH SAFE



public class A0_Test_While_SAFE {
    public static void m1(int j) {
        TrainStation s = new TrainStation(10);
        while (0 <= j && j < 10) {
            s.arrive(j);
            j++;
        }
    }
}