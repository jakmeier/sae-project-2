public class TOOB_No3 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(5);
		PrinterArray pb = new PrinterArray(8);
		PrinterArray pc = new PrinterArray(5);
		PrinterArray pd = new PrinterArray(2);
		pa.sendJob(2);
		pc.sendJob(4);
		pd.sendJob(0);
		pb.sendJob(6);
	}
}
