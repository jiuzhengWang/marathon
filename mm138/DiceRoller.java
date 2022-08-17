import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.SplittableRandom;

public class DiceRoller {
	private static int n, v;
	private static int[] grid;
	private static int[] sc;
	private static final double[] log = new double[1 << 16];
	private static final int[] dice = new int[6];
	private static Node head;
	private static Node[] nodes, nc;
	private static final int[] a0 = { 2, 0, 3, 1, 21, 6, 7, 8, 5, 10, 11, 12, 9, 14, 16, 22, 17, 13, 4, 18, 15, 19, 23, 20 };
	private static final int[] a1 = { 1, 3, 0, 2, 18, 8, 5, 6, 7, 12, 9, 10, 11, 17, 13, 20, 14, 16, 19, 21, 23, 4, 15, 22 };
	private static final int[] a2 = { 11, 17, 4, 20, 5, 14, 22, 19, 9, 3, 16, 6, 21, 12, 2, 13, 23, 7, 10, 1, 8, 15, 0, 18 };
	private static final int[] a3 = { 22, 19, 14, 9, 2, 4, 11, 17, 20, 8, 18, 0, 13, 15, 5, 21, 10, 1, 23, 7, 3, 12, 6, 16 };
	private static final int[] a4 = { 1, 4, 5, 0, 3, 4, 0, 5, 1, 2, 4, 3, 5, 1, 2, 4, 0, 3, 1, 2, 3, 0, 2, 5 };

	public static void main(String[] args) throws Exception {
		long timeout = System.currentTimeMillis() + 9600;
		for (int i = 0; i < log.length; i++) {
			log[i] = Math.log((i + 0.5) / log.length);
		}
		BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
		n = Integer.parseInt(in.readLine());
		v = Integer.parseInt(in.readLine());
		in.readLine();
		grid = new int[n << 5];
		for (int y = 0; y < n; y++) {
			for (int x = 0; x < n; x++) {
				grid[pos(x, y)] = Integer.parseInt(in.readLine());
			}
		}
		sc = new int[(v + 1) << 3];
		int best = 0;
		String ret = "";
		SplittableRandom rnd = new SplittableRandom(999);
		double t0 = v * 0.6;
		int q = 1;
		nodes = new Node[grid.length];
		nc = new Node[n * n];
		int k = 0;
		for (int y = 0; y < n; y++) {
			for (int x = 0; x < n; x++) {
				Node a = nc[k++] = new Node();
				a.pos = pos(x, y);
				nodes[a.pos] = a;
			}
		}
		Node prev = head = nodes[pos(q, q)];
		for (int i = q + 1; i <= n - 1 - q; i++) {
			prev = prev.next = nodes[pos(i, q)];
		}
		for (int i = q + 1; i <= n - 1 - q; i++) {
			prev = prev.next = nodes[pos(n - 1 - q, i)];
		}
		for (int i = n - 2 - q; i >= q; i--) {
			prev = prev.next = nodes[pos(i, n - 1 - q)];
		}
		for (int i = n - 2 - q; i >= q + 1; i--) {
			prev = prev.next = nodes[pos(q, i)];
		}
		prev.next = head;
		int curr = sim();
		double temp = t0;
		double rem = 1;
		long start = System.currentTimeMillis();
		double duration = timeout - start;
		int cycles = -1;
		while (true) {
			if ((++cycles & 255) == 0) {
				long t = System.currentTimeMillis();
				if (t > timeout) break;
				rem = 1 - (t - start) / (double) duration;
				temp = t0 * rem;
			}
			Node a0 = nc[cycles % nc.length];
			Node a1 = a0.next;
			if (a1 == null) continue;
			Node a2 = a1.next;
			if (Math.abs(a1.pos - a0.pos) != Math.abs(a1.pos - a2.pos) && head != a1) {
				int p3 = a0.pos - a1.pos + a2.pos;
				Node a3 = nodes[p3];
				if (a3.next == null) {
					a0.next = a3;
					a3.next = a2;
					int next = sim();
					int gain = next - curr;
					if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
						curr = next;
						if (curr > best) {
							best = curr;
							ret = ret();
						}
						a1.next = null;
					} else {
						a0.next = a1;
						a3.next = null;
					}
					continue;
				}
			}
			int mode = rnd.nextInt(6);
			if (mode == 0) {
				Node h = head;
				head = a1;
				int next = sim();
				int gain = next - curr;
				if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
					curr = next;
					if (curr > best) {
						best = curr;
						ret = ret();
					}
				} else {
					head = h;
				}
			} else if (mode <= 2 && head != a1 && head != a2) {
				Node a3 = a2.next;
				int d = Math.abs(a3.pos - a0.pos);
				if (d == 1 || d == 32) {
					a0.next = a3;
					int next = sim();
					int gain = next - curr;
					if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
						curr = next;
						if (curr > best) {
							best = curr;
							ret = ret();
						}
						a1.next = a2.next = null;
					} else {
						a0.next = a1;
					}
				}
			} else if (mode == 5) {
				Node a3 = a2.next;
				int d = Math.abs(a3.pos - a0.pos);
				if (d == 1 || d == 32) {
					int d2 = a1.pos - a0.pos;
					if (Math.abs(d2) == 1) {
						int x = (a1.pos & 31) + d2;
						if (x < 0 || x >= n) continue;
					} else {
						int y = (a1.pos >>> 5) + (d2 >>> 5);
						if (y < 0 || y >= n) continue;
					}
					Node a4 = nodes[a1.pos + d2];
					if (a4.next != null) {
						Node a5 = nodes[a2.pos + d2];
						if (a5.next == a4) {
							a0.next = a3;
							a5.next = a2;
							a2.next = a1;
							a1.next = a4;
							int next = sim();
							int gain = next - curr;
							if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
								curr = next;
								if (curr > best) {
									best = curr;
									ret = ret();
								}
							} else {
								a0.next = a1;
								a1.next = a2;
								a2.next = a3;
								a5.next = a4;
							}
						}
					}
				}
			} else {
				boolean o1 = true;
				boolean o2 = true;
				int d = Math.abs(a1.pos - a0.pos);
				if (d == 32) {
					int x = a0.pos & 31;
					if (x == 0) o1 = false;
					else if (x == n - 1) o2 = false;
					d = 1;
				} else {
					int y = a0.pos >>> 5;
					if (y == 0) o1 = false;
					else if (y == n - 1) o2 = false;
					d = 32;
				}
				Node a3 = null;
				if (o1) {
					a2 = nodes[a0.pos - d];
					a3 = nodes[a1.pos - d];
					if (a2.next != null || a3.next != null) o1 = false;
				}
				if (o2) {
					a2 = nodes[a0.pos + d];
					a3 = nodes[a1.pos + d];
					if (a2.next != null || a3.next != null) o2 = false;
				}
				if (o1 && o2) {
					if (rnd.nextBoolean()) o1 = false;
					else o2 = false;
				}
				if (o1) {
					a2 = nodes[a0.pos - d];
					a3 = nodes[a1.pos - d];
				} else if (!o2) continue;
				a0.next = a2;
				a2.next = a3;
				a3.next = a1;
				int next = sim();
				int gain = next - curr;
				if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
					curr = next;
					if (curr > best) {
						best = curr;
						ret = ret();
					}
				} else {
					a0.next = a1;
					a2.next = a3.next = null;
				}
			}
		}
		System.err.println(cycles);
		System.out.print(ret);
		System.out.flush();
	}

	private static String ret() {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < 6; i++) {
			sb.append(dice[i]);
			sb.append("\n");
		}
		Node a = head;
		int len = 0;
		while (true) {
			len++;
			a = a.next;
			if (a == head) break;
		}
		sb.append(len);
		sb.append("\n");
		a = head;
		while (true) {
			int p = a.pos;
			sb.append((p >>> 5) + " " + (p & 31));
			sb.append("\n");
			a = a.next;
			if (a == head) break;
		}
		return sb.toString();
	}

	private static int sim() {
		int prev = 99999;
		int state = 0;
		Arrays.fill(sc, 0);
		int score = 0;
		Node a = head;
		while (true) {
			switch (a.pos - prev) {
			case 1:
				state = a0[state];
				break;
			case -1:
				state = a1[state];
				break;
			case -32:
				state = a2[state];
				break;
			case 32:
				state = a3[state];
				break;
			}
			int g = grid[prev = a.pos];
			sc[(Math.abs(g) << 3) | a4[state]] += g;
			if ((a = a.next) == head) break;
		}
		for (int i = 0; i < 6; i++) {
			int max = -9999;
			for (int j = v; j >= 1; j--) {
				int curr = sc[i | (j << 3)];
				if (curr > max) {
					max = curr;
					dice[i] = j;
				}
			}
			score += max;
		}
		return score;
	}

	private static int pos(int x, int y) {
		return x + (y << 5);
	}
}

class Node {
	Node next;
	int pos;
}
