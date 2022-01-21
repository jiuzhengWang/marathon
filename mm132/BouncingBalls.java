import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.SplittableRandom;

public class BouncingBalls {
    private static final long timeLimit = 9400;
    private static final long timeout = System.currentTimeMillis() + timeLimit;
    private static final byte[] stateGrids = new byte[1 << 26];
    private static int n, nn, b, bonus, bestScore, size;
    private static State bestState;
    private static final int[] auxEmpty = new int[5];
    private static final byte cellEmpty = 1;
    private static final byte cellFixedNE = 2;
    private static final byte cellFixedNW = 3;
    private static final byte cellBonus = 4;
    private static final byte cellNE = 6;
    private static final byte cellNW = 7;
    private static final byte dirRight = 0;
    private static final byte dirLeft = 1;
    private static final byte dirUp = 2;
    private static final byte dirDown = 3;
    private static final SplittableRandom rnd = new SplittableRandom(99);
    private static final double[] log = new double[1 << 16];
    private static byte[] initialGrid;
    private static byte[] bestSol, simGrid;
    private static byte[][] gunsVecs;
    private static int stateGridsOffset;
    private static int[] hits;
    private static int[] hitCount;

    public static void main(String[] args) throws Exception {
        init();
        long S = System.currentTimeMillis();
        search(false);
        System.err.println("Search = " + (System.currentTimeMillis() - S));
        if (timeout - System.currentTimeMillis() > timeLimit * 0.8) search(true);
        improve();
        write();
    }

    private static void init() throws Exception {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        n = Integer.parseInt(br.readLine());
        nn = n * n;
        b = Integer.parseInt(br.readLine());
        bonus = Integer.parseInt(br.readLine());
        initialGrid = new byte[nn];
        Arrays.fill(initialGrid, cellEmpty);
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                char c = br.readLine().charAt(0);
                if (c == '/') initialGrid[pos(x, y)] = cellFixedNE;
                else if (c == '\\') initialGrid[pos(x, y)] = cellFixedNW;
                else if (c == '*') initialGrid[pos(x, y)] = cellBonus;
            }
        }
        br.close();
        gunsVecs = new byte[n * 4][3];
        int cnt = 0;
        for (int i = 0; i < n; i++) {
            gunsVecs[cnt++] = vec(-1, i, dirRight);
            gunsVecs[cnt++] = vec(n, i, dirLeft);
            gunsVecs[cnt++] = vec(i, -1, dirDown);
            gunsVecs[cnt++] = vec(i, n, dirUp);
        }
        size = nn + b * 3;
        bestSol = new byte[size];
        simGrid = new byte[size];
        hitCount = new int[nn];
        hits = new int[b];
        for (int i = 0; i < log.length; i++) {
            log[i] = Math.log((i + 0.5) / log.length);
        }
    }

    private static byte[] vec(int x, int y, int dir) {
        return new byte[] {(byte) x,(byte) y,(byte) dir};
    }

    private static void search(boolean any) {
        int k = Math.max(10, n);
        int width = (int) (3.5E7 / Math.pow(k, 2.567) * (1 - (b - 1) * 0.05)); //TODO
        List<State> currStates = new ArrayList<State>();
        List<int[]> used = new ArrayList<int[]>();
        OUT: while (currStates.size() < Math.min(width, b * (any ? n * 2 : 8))) {
            State state = new State();
            state.offset = stateGridsOffset;
            if ((stateGridsOffset += size) + size > stateGrids.length) stateGridsOffset = 0;
            System.arraycopy(initialGrid, 0, stateGrids, state.offset, nn);
            int[] sel = new int[b];
            for (int i = 0; i < b; i++) {
                NEXT: while (true) {
                    int p = rnd.nextInt(gunsVecs.length);
                    for (int j = 0; j < i; j++) {
                        if (p == sel[j]) continue NEXT;
                    }
                    byte[] vec = gunsVecs[p];
                    int x = vec[0];
                    int y = vec[1];
                    if (!any && x != 0 && x != n - 1 && y != 0 && y != n - 1) continue;
                    System.arraycopy(vec, 0, stateGrids, state.offset + nn + i * 3, vec.length);
                    sel[i] = p;
                    break;
                }
            }
            Arrays.sort(sel);
            for (int[] a : used) {
                if (Arrays.equals(a, sel)) continue OUT;
            }
            used.add(sel);
            state.add = new byte[b * 3];
            System.arraycopy(stateGrids, state.offset + nn, state.add, 0, state.add.length);
            state.advance();
            state.update();
            currStates.add(state);
        }
        List<State> nextStates = new ArrayList<State>();
        long tm1 = System.currentTimeMillis() + timeLimit * 85 / 100;
        long tm2 = System.currentTimeMillis() + timeLimit * 90 / 100;
        long tm3 = System.currentTimeMillis() + timeLimit * 95 / 100;
        int m = 0;
        int turn = 0;
        while (true) {
            turn++;
            for (int i = 0; i < currStates.size(); i++) {
                State curr = currStates.get(i);
                expand(curr, nextStates);
            }
            if (nextStates.size() == 0) break;
            long t = System.currentTimeMillis();
            if (t > timeout) {
                for (State s : nextStates) {
                    bestState = s;
                    bestScore = s.score;
                }
                break;
            }
            
            if (m == 0 && t > tm1) {
                m++;
                width = width * 3 / 4;
            } else if (m == 1 && t > tm2) {
                m++;
                width /= 2;
            } else if (m == 2 && t > tm3) {
                m++;
                width /= 2;
            }
            List<State> aux = currStates;
            currStates = nextStates;
            nextStates = aux;
            nextStates.clear();
            int w = turn < n ? width / 100 : width;
            if (currStates.size() > w) {
                Collections.sort(currStates);
                currStates.subList(w, currStates.size()).clear();
            }
        }
        System.err.println(">>>" + bestScore);
        System.arraycopy(initialGrid, 0, bestSol, 0, nn);
        State a = bestState;
        while (true) {
            if (a.parent == null) {
                System.arraycopy(a.add, 0, bestSol, nn, b * 3);
                break;
            }
            for (int i = 0; i < a.add.length; i += 3) {
                int p = pos(a.add[i], a.add[i + 1]);
                bestSol[p] = a.add[i + 2];
            }
            a = a.parent;
        }
    }

    private static void expand(State state, List<State> nextStates) {
        int all = 1 << state.empty.length;
        for (int j = 0; j < state.empty.length; j++) {
            stateGrids[state.offset + state.empty[j]] = cellNE;
        }
        for (int mask = 0; mask < all; mask++) {
            for (int j = 0; j < state.empty.length; j++) {
                int bit = 1 << j;
                boolean a = (bit & mask) != 0;
                if (a != ((bit & (mask - 1)) != 0)) stateGrids[state.offset + state.empty[j]] = a ? cellNW : cellNE;
            }
            State next = new State();
            next.offset = stateGridsOffset;
            if ((stateGridsOffset += size) + size > stateGrids.length) stateGridsOffset = 0;
            System.arraycopy(stateGrids, state.offset, stateGrids, next.offset, size);
            next.score = state.score;
            next.parent = state;
            next.advance();
            next.update();
            if (next.done) {
                if (next.score > bestScore) {
                    next.finish(state);
                    bestState = next;
                    bestScore = next.score;
                }
            } else {
                if (nextStates.add(next)) next.finish(state);
            }
        }
    }

    private static void improve() {
        byte[] sol = bestSol.clone();
        int currScore = eval(sol);
        if (currScore > bestScore) {
            System.arraycopy(sol, 0, bestSol, 0, sol.length);
            bestScore = currScore;
        }
        double mult = 2.4 / n;
        double t0 = currScore * mult / n;
        double temp = t0;
        double duration = timeout - System.currentTimeMillis();
        int cycles = 0;
        int div = n <= 10 ? nn + b : nn;
        NEXT: while (true) {
            if ((++cycles & 511) == 0) {
                long t = System.currentTimeMillis();
                if (t >= timeout) break;
                temp = t0 * (timeout - t) / duration;
            }
            int pos = cycles % div;
            if (pos >= nn) {
                int idx = (pos - nn) * 3 + nn;
                byte cx = sol[idx];
                byte cy = sol[idx + 1];
                byte cd = sol[idx + 2];
                byte[] vec = gunsVecs[rnd.nextInt(gunsVecs.length)];
                int nx = vec[0];
                int ny = vec[1];
                for (int j = 0; j < b; j++) {
                    if (j == pos - nn) continue;
                    int jj = nn + j * 3;
                    if (nx == sol[jj] && ny == sol[jj + 1]) continue NEXT;
                }
                System.arraycopy(vec, 0, sol, idx, vec.length);
                int nextScore = eval(sol);
                int gain = nextScore - currScore;
                if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
                    currScore = nextScore;
                } else {
                    sol[idx] = cx;
                    sol[idx + 1] = cy;
                    sol[idx + 2] = cd;
                }
            } else {
                byte currCell = sol[pos];
                if (currCell != cellEmpty && currCell != cellNE && currCell != cellNW) continue;
                sol[pos] = currCell == cellEmpty ? (rnd.nextBoolean() ? cellNW : cellNE) : currCell == cellNE ? (rnd.nextInt(16) != 0 ? cellNW : cellEmpty) : (rnd.nextInt(16) != 0 ? cellNE : cellEmpty);
                int nextScore = eval(sol);
                int gain = nextScore - currScore;
                if (gain >= 0 || gain > log[rnd.nextInt(log.length)] * temp) {
                    currScore = nextScore;
                } else {
                    sol[pos] = currCell;
                }
            }
            if (currScore > bestScore) {
                System.arraycopy(sol, 0, bestSol, 0, sol.length);
                bestScore = currScore;
            }
        }
    }

    private static int eval(byte[] evalSol) {
        System.arraycopy(evalSol, 0, simGrid, 0, evalSol.length);
        byte[] s = simGrid;
        int score = 0;
        boolean done = false;
        while (!done) {
            int hc = 0;
            for (int i = 0; i < b; i++) {
                int idx = nn + i * 3;
                byte x = s[idx];
                byte y = s[idx + 1];
                byte dir = s[idx + 2];
                switch (dir) {
                case dirDown:
                    if (++y == n) {
                        done = true;
                        continue;
                    }
                    break;
                case dirUp:
                    if (y-- == 0) {
                        done = true;
                        continue;
                    }
                    break;
                case dirLeft:
                    if (x-- == 0) {
                        done = true;
                        continue;
                    }
                    break;
                case dirRight:
                    if (++x == n) {
                        done = true;
                        continue;
                    }
                    break;
                }
                int p = pos(s[idx] = x, s[idx + 1] = y);
                switch (s[p]) {
                case cellNE:
                    score++;
                    s[idx + 2] = (byte) ((dir + 2) & 3);
                    hitCount[hits[hc++] = p]++;
                    break;
                case cellFixedNE:
                    score++;
                    s[idx + 2] = (byte) ((dir + 2) & 3);
                    break;
                case cellNW:
                    score++;
                    s[idx + 2] = (byte) (dir ^ 3);
                    hitCount[hits[hc++] = p]++;
                    break;
                case cellFixedNW:
                    score++;
                    s[idx + 2] = (byte) (dir ^ 3);
                    break;
                case cellBonus:
                    score += bonus;
                    break;
                }
            }
            for (int i = 0; i < hc; i++) {
                int p = hits[i];
                if (hitCount[p] == 1) s[p] ^= 1;
                hitCount[p] = 0;
            }
        }
        return score;
    }

    private static void write() {
        StringBuilder sb = new StringBuilder();
        int idx = nn;
        for (int i = 0; i < b; i++) {
            int x = bestSol[idx++];
            int y = bestSol[idx++];
            idx++;
            sb.append(y).append(" ").append(x).append(System.lineSeparator());
        }
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                byte b = bestSol[pos(x, y)];
                if (b == cellFixedNE || b == cellNE) sb.append('/');
                else if (b == cellFixedNW || b == cellNW) sb.append('\\');
                else if (b == cellBonus) sb.append('*');
                else sb.append('.');
                sb.append(System.lineSeparator());
            }
        }
        System.out.print(sb.toString());
        System.out.flush();
    }

    private static int pos(int x, int y) {
        return y * n + x;
    }

    static class State implements Comparable<State> {
        int offset;
        byte[] add;
        State parent;
        int score, val;
        int[] empty;
        boolean done;

        public int compareTo(State o) {
            return Integer.compare(o.val, val);
        }

        private void step() {
            byte[] s = stateGrids;
            int hc = 0;
            for (int j = 0; j < b; j++) {
                int idx = nn + j * 3 + offset;
                byte x = s[idx];
                byte y = s[idx + 1];
                byte dir = s[idx + 2];
                switch (dir) {
                case dirDown:
                    if (++y == n) continue;
                    break;
                case dirUp:
                    if (y-- == 0) continue;
                    break;
                case dirLeft:
                    if (x-- == 0) continue;
                    break;
                case dirRight:
                    if (++x == n) continue;
                    break;
                }
                int p = pos(s[idx] = x, s[idx + 1] = y);
                switch (s[p + offset]) {
                case cellNE:
                    score++;
                    s[idx + 2] = (byte) ((dir + 2) & 3);
                    hitCount[hits[hc++] = p]++;
                    break;
                case cellFixedNE:
                    score++;
                    s[idx + 2] = (byte) ((dir + 2) & 3);
                    break;
                case cellNW:
                    score++;
                    s[idx + 2] = (byte) (dir ^ 3);
                    hitCount[hits[hc++] = p]++;
                    break;
                case cellFixedNW:
                    score++;
                    s[idx + 2] = (byte) (dir ^ 3);
                    break;
                case cellBonus:
                    score += bonus;
                    break;
                }
            }
            for (int i = 0; i < hc; i++) {
                int p = hits[i];
                if (hitCount[p] == 1) s[p + offset] ^= 1;
                hitCount[p] = 0;
            }
        }

        private void findNext() {
            byte[] s = stateGrids;
            int ne = 0;
            for (int i = 0; i < b; i++) {
                int idx = nn + i * 3 + offset;
                byte x = s[idx];
                byte y = s[idx + 1];
                byte dir = s[idx + 2];
                switch (dir) {
                case dirDown:
                    if (++y == n) {
                        done = true;
                        continue;
                    }
                    break;
                case dirUp:
                    if (y-- == 0) {
                        done = true;
                        continue;
                    }
                    break;
                case dirLeft:
                    if (x-- == 0) {
                        done = true;
                        continue;
                    }
                    break;
                case dirRight:
                    if (++x == n) {
                        done = true;
                        continue;
                    }
                    break;
                }
                int p = pos(x, y);
                if (s[p + offset] == cellEmpty) {
                    boolean found = false;
                    for (int j = 0; j < ne; j++) {
                        if (auxEmpty[j] == p) {
                            found = true;
                            break;
                        }
                    }
                    if (!found) auxEmpty[ne++] = p;
                }
            }
            empty = Arrays.copyOf(auxEmpty, ne);
        }

        private void advance() {
            while (!done) {
                findNext();
                if (empty.length != 0) break;
                step();
            }
        }

        private void finish(State state) {
            add = new byte[state.empty.length * 3];
            int idx = 0;
            for (int i = 0; i < state.empty.length; i++) {
                int p = state.empty[i];
                add[idx++] = (byte) (p % n);
                add[idx++] = (byte) (p / n);
                add[idx++] = stateGrids[state.offset + p];
            }
        }

        private void update() {
            val = score + rnd.nextInt(5);
            int idx = nn + offset;
            int v = 100;
            int sum = 0;
            for (int i = 0; i < b; i++, idx += 3) {
                int x = stateGrids[idx];
                int y = stateGrids[idx + 1];
                int k = Math.min(Math.min(x, n - 1 - x), Math.min(y, n - 1 - y));
                sum += k;
                if (k < v) v = k;
            }
            val += (sum + v) * (n * 4) / (b + 1);
        }
    }
}
