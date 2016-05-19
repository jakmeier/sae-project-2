public class PrinterArray {
	private int numPrinters;

	public PrinterArray(int numPrinters) {
		this.numPrinters = numPrinters;
	}

	public native void sendJob(int printerIndex);
}