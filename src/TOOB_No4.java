public class TOOB_No4 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(10);
		PrinterArray pb = new PrinterArray(20);
		PrinterArray pc = new PrinterArray(30);
		PrinterArray pd = new PrinterArray(40);
		
		
		pa = pb;
		pb = pd;
		pd = pc; 
		pc = pa;
		
		pa.sendJob(19);
		pb.sendJob(39);
		pc.sendJob(19);
		pd.sendJob(29);
	}
}
