/**
 * And example application you may want to analyze to test your analysis.
 *
 */
public class Test2 {
    public static void bar(int n) {
        int a = 5/n;
        PrinterArray pa = new PrinterArray(10);
        if ((a >= 0) && (a < 10)) {
            pa.sendJob(a);
        }
    }
}
