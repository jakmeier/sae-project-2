public class TOOB_No5 {
	public static void foo() {
		PrinterArray pa = new PrinterArray(1);
		PrinterArray pb = new PrinterArray(1);
		PrinterArray pc = new PrinterArray(1);
		PrinterArray pd = new PrinterArray(10);
		
		
		pa = pb;
		pb = pd;
		pd = pc; 
		pc = pa;
		pa = pb;
		pc = pa;
		pd = pc;
		
		pa.sendJob(5);
		pb.sendJob(5);
		pc.sendJob(5);
		pd.sendJob(5);
	}
}
