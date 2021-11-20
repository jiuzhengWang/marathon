import java.io.*;
import java.util.*;

public class Slider {
    private static final long timeLimit = 8900;
    private final long start = System.currentTimeMillis(), timeout1 = start + timeLimit, timeout2 = timeout1 + 500;
    private byte[] initialGrid, reach;
    private int n, h, c, mult, nn;
    private State cutState;
    private long[] zh;
    private int[] hx, hy, rc, support;
    private final SplittableRandom rnd = new SplittableRandom(999);
    private final State[] stateList = new State[4096];

    private String solve() {
        nn = n * n;
        zh = new long[nn << 4];
        rc = new int[nn];
        support = new int[nn];
        State root = new State();
        root.grid = initialGrid;
        for (int i = 0; i < nn; i++) {
            for (int j = 1; j <= c; j++) {
                zh[(i << 4) | j] = rnd.nextLong();
            }
            byte g = root.grid[i];
            if (g >= 1) root.zh ^= zh[(i << 4) | g];
        }
        root.move = new Move(-1, -1, -1, -1, (byte) 0);
        reach = new byte[nn];
        hx = new int[h];
        hy = new int[h];
        int hh = 0;
        for (int i = 0; i < nn; i++) {
            if (initialGrid[i] == -1) {
                hx[hh] = i % n;
                hy[hh++] = i / n;
            }
        }
        State best = null;
        List<Long> times = new ArrayList<Long>();
        int rep = 0;
        OUT: while (System.currentTimeMillis() < timeout1) {
            mult = n * n;
            long t0 = System.currentTimeMillis();
            int width = 1 << (rep + 2);
            if (!times.isEmpty()) {
                long prev = times.get(times.size() - 1);
                if (t0 + prev * 2 > timeout1) {
                    width = (int) Math.max(1, width * (timeout1 - t0) / (prev + 1) / 2);
                }
            }
            Beam<State> currStates = new Beam<State>(width);
            Beam<State> nextStates = new Beam<State>(width);
            currStates.add(root);
            while (mult > 0 && System.currentTimeMillis() < timeout1) {
                cutState = null;
                for (int i = 0; i < currStates.size; i++) {
                    if ((i & 31) == 31 && System.currentTimeMillis() >= timeout1) break OUT;
                    State curr = currStates.get(i);
                    updateReach(curr.grid);
                    int ns = getStates(curr);
                    for (int j = 0; j < ns; j++) {
                        State a = stateList[j];
                        if (best == null || a.score > best.score) best = a;
                        if (nextStates.add(a) && nextStates.size == width) cutState = nextStates.last();
                    }
                }
                for (int i = 0; i < nextStates.size; i++) {
                    State a = nextStates.get(i);
                    a.grid = a.parent.grid.clone();
                    if (a.move.dest >= 0) a.grid[a.move.dest] = a.grid[a.move.pos];
                    a.grid[a.move.pos] = 0;
                }
                if (nextStates.size == 0) break;
                if (mult-- < nn) {
                    for (int i = 0; i < currStates.size; i++) {
                        currStates.get(i).grid = null;
                    }
                }
                Beam<State> aux = currStates;
                currStates = nextStates;
                nextStates = aux;
                nextStates.clear();
            }
            rep++;
            times.add(System.currentTimeMillis() - t0);
            //System.err.println(width + ":" + times);
        }
        Move[] sol = getMoves(best);
        improve(sol);
        return mountRet(sol);
    }

    private int improve(Move[] sol) {
        mult = nn;
        byte[][] grids = new byte[sol.length + 1][nn];
        byte[] g0 = grids[0];
        System.arraycopy(initialGrid, 0, g0, 0, nn);
        int score = 0;
        for (int i = 0; i < sol.length; i++, mult--) {
            Move m = sol[i];
            byte[] g1 = grids[i + 1];
            int add = apply(m, g0, g1, mult);
            if (add < 0) {
                score = -1;
                break;
            }
            score += add;
            g0 = g1;
        }
        byte[] aux = new byte[nn];
        Move[] rot = new Move[sol.length];
        for (int rep = 0; rep < 5 && System.currentTimeMillis() < timeout2; rep++) {
            boolean imp = false;
            for (int len = Math.min(50, sol.length); len >= 2 && System.currentTimeMillis() < timeout2; len--) {
                for (int i = 0; i < sol.length - len; i++) {
                    int old = 0;
                    int best = 0;
                    g0 = grids[i];
                    byte[] g1 = grids[i + len];
                    int dist = Math.min(len, 10);
                    for (int k = 0; k < len; k++) {
                        Move m = sol[i + k];
                        if (m.dest == -1 && m.val > 1) old += (nn - i - k) * (m.val - 1);
                    }
                    int max = old;
                    for (int j = 0; j < len; j++) {
                        if (j < dist || j >= len - dist) {
                            int sum = 0;
                            System.arraycopy(g0, 0, aux, 0, nn);
                            int v = nn - i;
                            for (int k = 0; k < len; k++, v--) {
                                int add = apply(sol[i + (k - j + len) % len], aux, aux, v);
                                if (add < 0) {
                                    sum = -1;
                                    break;
                                }
                                sum += add;
                            }
                            if (sum > max && Arrays.equals(aux, g1)) {
                                max = sum;
                                best = j;
                            }
                        }
                    }
                    if (best > 0) {
                        imp = true;
                        score += max - old;
                        System.arraycopy(sol, i, rot, i, len);
                        System.arraycopy(rot, i, sol, i + best, len - best);
                        System.arraycopy(rot, i + len - best, sol, i, best);
                        for (int k = i; k < i + len; k++) {
                            apply(sol[k], grids[k], grids[k + 1], 0);
                        }
                    }
                }
            }
            if (!imp) break;
        }
        return score;
    }

    private int apply(Move m, byte[] g0, byte[] g1, int v) {
        byte g = g0[m.pos];
        if (g <= 0) return -1;
        if (g0 != g1) System.arraycopy(g0, 0, g1, 0, nn);
        g1[m.pos] = 0;
        int d = m.type == 0 ? 1 : n;
        int dx = 0;
        int dy = 0;
        if (m.dir == 2) dx = -1;
        else if (m.dir == 3) dx = 1;
        else if (m.dir == 0) dy = -1;
        else if (m.dir == 1) dy = 1;
        int dn = dx + dy * n;
        int nx = m.pos % n;
        int ny = m.pos / n;
        int prev = -1;
        int add = 0;
        int np = m.pos;
        for (int j = 0; j < d; j++) {
            if (dx != 0) {
                if ((nx += dx) < 0 || nx >= n) break;
            } else {
                if ((ny += dy) < 0 || ny >= n) break;
            }
            np += dn;
            byte a = g1[np];
            if (a == -1) {
                if (m.dest != -1) return -1;
                if (g > 1) add = v * (g - 1);
                prev = -2;
                break;
            }
            if (a > 0) break;
            prev = np;
        }
        if (prev == -1) return -1;
        if (prev >= 0) {
            if (m.dest != prev) return -1;
            g1[prev] = g;
        }
        return add;

    }

    private Move[] getMoves(State a) {
        List<Move> l = new ArrayList<Move>();
        while (a.parent != null) {
            l.add(a.move);
            a = a.parent;
        }
        Collections.reverse(l);
        return l.toArray(new Move[0]);
    }

    private void updateReach(byte[] grid) {
        Arrays.fill(reach, (byte) 10);
        Arrays.fill(support, 0);
        int cnt = 0;
        for (int i = 0; i < h; i++) {
            int x = hx[i];
            int y = hy[i];
            for (int dir = 0; dir < 4; dir++) {
                int nx = x;
                int ny = y;
                int dd = dir == 2 ? -1 : dir == 3 ? 1 : dir == 0 ? -n : n;
                int np = x + y * n;
                for (int d = 0; d < n; d++) {
                    if (dir == 2) nx--;
                    else if (dir == 3) nx++;
                    else if (dir == 0) ny--;
                    else ny++;
                    if (nx < 0 || nx >= n || ny < 0 || ny >= n) break;
                    int ng = grid[np += dd];
                    if (ng != 0) break;
                    if (reach[np] != 1) reach[rc[cnt++] = np] = (byte) 1;
                }
            }
        }
        for (int ii = 0; ii < cnt; ii++) {
            int i = rc[ii];
            int x = i % n;
            int y = i / n;
            for (int dir = 0; dir < 4; dir++) {
                int nx = x;
                int ny = y;
                int k = n;
                int dd = dir == 2 ? -1 : dir == 3 ? 1 : dir == 0 ? -n : n;
                int np = i;
                boolean s = false;
                for (int d = 0; d < k; d++) {
                    if (dir == 2) nx--;
                    else if (dir == 3) nx++;
                    else if (dir == 0) ny--;
                    else ny++;
                    if (nx < 0 || nx >= n || ny < 0 || ny >= n) break;
                    if (d == 0) {
                        int qx = x;
                        int qy = y;
                        if (dir == 2) qx++;
                        else if (dir == 3) qx--;
                        else if (dir == 0) qy++;
                        else qy--;
                        if (qx >= 0 && qx < n && qy >= 0 && qy < n) {
                            if (grid[i - dd] == 0) k = 1;
                            else s = true;
                        }
                    }
                    int ng = grid[np += dd];
                    if (ng != 0) {
                        if (s && ng > 1) support[i - dd] += ng;
                        break;
                    }
                    if (reach[np] > 2) reach[np] = (byte) 2;
                }
            }
        }
    }

    private String mountRet(Move[] moves) {
        StringBuilder sb = new StringBuilder();
        sb.append(moves.length).append('\n');
        for (Move m : moves) {
            sb.append(m.toString()).append('\n');
        }
        return sb.toString();
    }

    private int getStates(State curr) {
        int k = 0;
        int min = cutState == null ? 1 : Math.max(1, (mult - 1 + cutState.score - curr.score) / mult + 1);
        for (int i = 0; i < curr.grid.length; i++) {
            byte a = curr.grid[i];
            if (a < min) continue;
            int x = i % n;
            int y = i / n;
            boolean hole = false;
            for (int dir = 0; dir < 4; dir++) {
                int nx = x;
                int ny = y;
                int dd = dir == 2 ? -1 : dir == 3 ? 1 : dir == 0 ? -n : n;
                int np = i;
                int prev = -1;
                for (int d = 0; d < n; d++) {
                    if (dir == 2) nx--;
                    else if (dir == 3) nx++;
                    else if (dir == 0) ny--;
                    else if (dir == 1) ny++;
                    if (nx < 0 || nx >= n || ny < 0 || ny >= n) {
                        if (prev >= 0 && add(curr, k, dir, i, prev, 1, a)) k++;
                        break;
                    }
                    int ng = curr.grid[np += dd];
                    if (ng == -1) {
                        if (!hole && add(curr, k, dir, i, -1, 1, a)) {
                            hole = true;
                            k++;
                        }
                        break;
                    }
                    if (ng > 0) {
                        if (prev >= 0 && add(curr, k, dir, i, prev, 1, a)) k++;
                        break;
                    }
                    if (d != 0) prev = np;
                    else if (add(curr, k, dir, i, np, 0, a)) k++;
                }
            }
        }
        return k;
    }

    private boolean add(State curr, int k, int dir, int p1, int p2, int type, byte v) {
        int score = curr.score;
        if (p2 < 0 && v > 1) score += mult * (v - 1);
        if (cutState != null && score < cutState.score) return false;
        int bonus = curr.bonus / 100 + rnd.nextInt(100) - support[p1] * 10;
        if (p2 < 0) {
            bonus += 1000;
            for (int i = 0; i < h; i++) {
                int x = hx[i];
                int y = hy[i];
                for (int dr = 0; dr < 4; dr++) {
                    int nx = x;
                    int ny = y;
                    int m = 128;
                    while (true) {
                        if (dr == 2) nx--;
                        else if (dr == 3) nx++;
                        else if (dr == 0) ny--;
                        else if (dr == 1) ny++;
                        if (nx < 0 || nx >= n || ny < 0 || ny >= n) break;
                        int np = ny * n + nx;
                        if (np == p1) continue;
                        int ng = curr.grid[np];
                        if (ng > 1) {
                            bonus += ng * m;
                            m >>>= 1;
                        }
                        if (ng == 1 || ng == -1) break;
                    }
                }
            }
        } else {
            bonus += support[p2] * 10 + v * 100 / reach[p2] - v * 100 / reach[p1];
        }
        if (cutState != null && score == cutState.score && bonus <= cutState.bonus) return false;
        State ns = stateList[k] = new State();
        ns.score = score;
        ns.bonus = bonus;
        ns.parent = curr;
        ns.zh = curr.zh ^ zh[(p1 << 4) | v];
        if (p2 >= 0) ns.zh ^= zh[(p2 << 4) | v];
        ns.move = new Move(p1, dir, type, p2, v);
        return true;
    }

    class Move {
        final int pos, dest;
        final byte dir, type, val;

        Move(int pos, int dir, int type, int dest, byte val) {
            this.pos = pos;
            this.dir = (byte) dir;
            this.type = (byte) type;
            this.dest = dest;
            this.val = val;
        }

        public String toString() {
            return pos / n + " " + pos % n + " " + "MS".charAt(type) + " " + "UDLR".charAt(dir);
        }
    }

    class State implements Comparable<State> {
        State parent;
        byte[] grid;
        int score, bonus;
        Move move;
        long zh;

        public int compareTo(State o) {
            int cmp = Integer.compare(o.score, score);
            if (cmp != 0) return cmp;
            return Integer.compare(o.bonus, bonus);
        }

        public boolean equals(Object obj) {
            State o = (State) obj;
            return o.zh == zh;
        }
    }

    class Beam<T extends Comparable<T>> {
        private int beamWidth;
        private T[] items;
        private int size;

        @SuppressWarnings("unchecked")
        Beam(int beamWidth) {
            this.beamWidth = beamWidth;
            items = (T[]) new Comparable<?>[beamWidth];
        }

        void addAll(Beam<T> other) {
            System.arraycopy(other.items, 0, items, 0, size = other.size);
        }

        boolean add(T item) {
            if (size >= beamWidth && ((Comparable<T>) items[beamWidth - 1]).compareTo(item) <= 0) return false;
            int pos = Arrays.binarySearch(items, 0, size, item);
            if (pos >= 0) return false;
            pos = -pos - 1;
            if (pos >= beamWidth) return false;
            for (int i = size - 1; i >= 0; i--) {
                T o = items[i];
                if (o.equals(item)) {
                    if (item.compareTo(o) < 0) {
                        items[i] = item;
                        Arrays.sort(items, 0, size);
                        return true;
                    }
                    return false;
                }
            }
            if (size < beamWidth) size++;
            for (int i = size - 1; i > pos; i--) {
                items[i] = items[i - 1];
            }
            items[pos] = item;
            return true;
        }

        T last() {
            if (size < beamWidth) return null;
            return items[beamWidth - 1];
        }

        T get(int idx) {
            return items[idx];
        }

        int size() {
            return size;
        }

        void setWidth(int newWidth) {
            beamWidth = newWidth;
            if (size > beamWidth) size = beamWidth;
        }

        void clear() {
            size = 0;
        }
    }

    public static void main(String[] args) {
        Slider slider = new Slider();
        try {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            int n = slider.n = Integer.parseInt(br.readLine());
            slider.c = Integer.parseInt(br.readLine());
            slider.h = Integer.parseInt(br.readLine());
            slider.initialGrid = new byte[n * n];
            for (int k = 0; k < slider.initialGrid.length; k++) {
                slider.initialGrid[k] = Byte.parseByte(br.readLine());
            }
            String ret = slider.solve();
            System.out.println(ret);
            System.out.flush();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}