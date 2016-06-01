public class TOOB_May5 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(10);
		PrinterArray pb = new PrinterArray(10);
		PrinterArray pc = new PrinterArray(10);
		PrinterArray pd = new PrinterArray(1);
		
		
		pa = pb;
		pb = pd;
		pd = pc; 
		pc = pa;
		pa = pb;
		pc = pa;
		pd = pc;
		
		pa.sendJob(0);
		pd.sendJob(5);
		pb.sendJob(0);
		pc.sendJob(0);

	}
}
