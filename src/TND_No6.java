// result NO_DIV_ZERO
public class TND_No6 {
	public static void foo(int n) {
		int a = 3;
		int b = 1;
		for (int i = b; i < 3; i++) {
			if (i == a) break;
			else a++;
		}
	}
}
