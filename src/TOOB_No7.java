/**
 * And example application you may want to analyze to test your analysis.
 *
 */
public class TOOB_No7 {
	public static void bar(int a) {
		PrinterArray pa1 = new PrinterArray(10);
		PrinterArray pa2 = new PrinterArray(1);
		PrinterArray pa3 = new PrinterArray(3);
		PrinterArray pa4 = pa2;
		pa2 = new PrinterArray(5);
		
		if ((a >= 0) && (a < 1)) {
			pa4.sendJob(a);
		}
		
		if ((a >= 2) && (a < 3)) {
			pa3.sendJob(a);
		}
		
		if ((a >= 3) && (a < 5)) {
			pa2.sendJob(a);
		}
		
		if ((a >= 5) && (a < 10)) {
			pa1.sendJob(a);
		}

		if ( a == -1 ) pa2.sendJob(1);
		if ( a != -1 ) pa2.sendJob(2);
		if ( a > -1 ) pa2.sendJob(3);
		if ( a <= -1 ) pa2.sendJob(4);
	}
}
