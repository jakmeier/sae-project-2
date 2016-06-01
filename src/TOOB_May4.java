public class TOOB_May4 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(10);
		PrinterArray pb = new PrinterArray(20);
		PrinterArray pc = new PrinterArray(30);
		PrinterArray pd = new PrinterArray(40);
		
		
		pa = pb;
		pb = pd;
		pd = pc; 
		pc = pa;
		
		
		pb.sendJob(2);
		pd.sendJob(4);
		pa.sendJob(1);
		pc.sendJob(11);
	}
}
