public class TOOB_May6 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(10);
		
		int i = 15;
		int a = 0;
		int b = 10;
		
		a = a * 5;
		b = b / 2;
		
		if (b < a) i = 5;
		
		pa.sendJob(i);

	}
}
