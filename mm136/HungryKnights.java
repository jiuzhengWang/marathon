import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.Comparator;
import java.util.SplittableRandom;

public class HungryKnights {
    private static int n, c;
    private static byte[] grid;
    private static int[] d;
    private static int[] dx = {-2,-1,-2,-1,2,1,2,1};
    private static int[] dy = {-1,-2,1,2,-1,-2,1,2};
    private static final SplittableRandom rnd = new SplittableRandom(999);
    private static final long timeout = System.currentTimeMillis() + 9300;
    private static State aux = new State();

    public static void main(String[] args) {
        init();
        State bestState = solve();
        output(bestState);
    }

    private static State solve() {
        int[] cnt = new int[c];
        for (int y0 = 0; y0 < n; y0++) {
            for (int x0 = 0; x0 < n; x0++) {
                cnt[grid[pos(x0, y0)]]++;
            }
        }
        Integer[] ord = new Integer[c];
        for (int i = 0; i < c; i++) {
            ord[i] = i;
        }
        Arrays.sort(ord, new Comparator<Integer>() {
            public int compare(Integer a, Integer b) {
                return cnt[b] - cnt[a];
            }
        });
        int[] rank = new int[c];
        for (int i = 0; i < c; i++) {
            rank[ord[i]] = i;
        }
        int[] bonus = new int[c];
        for (int i = 0; i < c; i++) {
            bonus[i] = (c / 2 - rank[i]) * ((n - 1) / 10);
        }
        for (int i = 0; i < c; i++) {
            for (int j = 0; j < c; j++) {
                if (i != j) d[colorPair(i, j)] += bonus[i] - bonus[j];
            }
        }
        State root = new State();
        root.grid = grid;
        root.moves = new int[0];
        root.pos = -1;
        State bestState = root;
        int bestScore = 0;
        int width = 50000 / n / n;
        int[] path = new int[5];
        while (System.currentTimeMillis() < timeout) {
            width = width * 10 / 9;
            Beam<State> currStates = new Beam<State>(width);
            currStates.add(root);
            Beam<State> nextStates = new Beam<State>(width);
            while (currStates.size() != 0 && System.currentTimeMillis() < timeout) {
                for (int i = 0; i < currStates.size(); i++) {
                    State si = currStates.get(i);
                    NEXT: for (int j = i + 1; j < currStates.size(); j++) {
                        State sj = currStates.get(j);
                        if (si.chain != sj.chain || si.pos != sj.pos) continue;
                        for (int y = 0; y < n; y++) {
                            for (int x = 0; x < n; x++) {
                                int p = pos(x, y);
                                if (si.grid[p] != sj.grid[p]) continue NEXT;
                            }
                        }
                        currStates.remove(j--);
                    }
                }
                for (int i = 0; i < currStates.size(); i++) {
                    State currState = currStates.get(i);
                    if (currState.score > bestScore) {
                        bestScore = currState.score;
                        bestState = currState;
                    }
                    boolean expanded = false;
                    int p0 = currState.pos;
                    if (p0 != -1) {
                        int x0 = x(p0);
                        int y0 = y(p0);
                        int c0 = currState.grid[p0];
                        expanded = expand(x0, y0, p0, c0, currState, nextStates);
                        if (!expanded) {
                            path[0] = p0;
                            expanded = find(x0, y0, p0, c0, currState, nextStates, path, 1, path.length);
                        }
                    }
                    if (!expanded) {
                        for (int y0 = 0; y0 < n; y0++) {
                            for (int x0 = 0; x0 < n; x0++) {
                                p0 = pos(x0, y0);
                                int c0 = currState.grid[p0];
                                if (c0 == -1) continue;
                                expand(x0, y0, p0, c0, currState, nextStates);
                            }
                        }
                    }
                }
                Beam<State> auxStates = currStates;
                currStates = nextStates;
                nextStates = auxStates;
                nextStates.clear();
            }
        }
        return bestState;
    }

    private static boolean find(int x0, int y0, int p0, int c0, State state, Beam<State> next, int[] path, int level, int max) {
        if (level > 1) {
            int cc = state.grid[p0];
            if (cc == c0) {
                aux.chain = state.chain;
                aux.score = state.score;
                for (int i = 1; i < level - 1; i++) {
                    aux.score += d[colorPair(cc, state.grid[path[i]])];
                }
                aux.pos = state.pos;
                aux.val = rnd.nextInt(10);
                aux.len = state.len + level - 2;
                if (next.add(aux)) {
                    aux.moves = Arrays.copyOf(state.moves, state.moves.length + level - 2);
                    int pos = state.moves.length - state.chain;
                    System.arraycopy(state.moves, pos, aux.moves, pos + level - 2, state.chain);
                    for (int i = level - 1; i > 1; i--) {
                        aux.moves[pos++] = move(path[i], path[i - 1]);
                    }
                    aux.grid = state.grid.clone();
                    for (int i = 2; i < level; i++) {
                        aux.grid[path[i]] = -1;
                    }
                    aux.grid[path[1]] = (byte) c0;
                    aux = new State();
                }
                return true;
            }
        }
        boolean ret = false;
        if (level < max) {
            for (int i = 0; i < dx.length; i++) {
                int x1 = x0 + dx[i];
                if (x1 < 0 || x1 >= n) continue;
                int y1 = y0 + dy[i];
                if (y1 < 0 || y1 >= n) continue;
                int p1 = pos(x1, y1);
                int c1 = state.grid[p1];
                if (c1 == -1) continue;
                if (level >= 2 && path[level - 2] == p1) continue;
                if (level >= 4 && path[level - 4] == p1) continue;
                path[level] = p1;
                if (find(x1, y1, p1, c0, state, next, path, level + 1, max)) ret = true;
            }
        }
        return ret;
    }

    private static boolean expand(int x0, int y0, int p0, int c0, State currState, Beam<State> nextStates) {
        boolean expanded = false;
        for (int i = 0; i < dx.length; i++) {
            int x1 = x0 + dx[i];
            if (x1 < 0 || x1 >= n) continue;
            int y1 = y0 + dy[i];
            if (y1 < 0 || y1 >= n) continue;
            int p1 = pos(x1, y1);
            int c1 = currState.grid[p1];
            if (c1 == -1) continue;
            if (c0 == c1 && p0 == currState.pos) {
                aux.chain = currState.chain + 1;
                aux.score = aux.chain + currState.score;
                aux.pos = p1;
                expanded = true;
            } else if (c0 == c1) {
                aux.pos = p1;
                aux.chain = 1;
                aux.score = 1 + currState.score;
            } else {
                int dc = d[colorPair(c0, c1)];
                aux.pos = -1;
                aux.chain = 0;
                aux.score = dc + currState.score;
            }
            int nb = 0;
            if (c0 == c1) {
                for (int k = 0; k < dx.length; k++) {
                    int x2 = x1 + dx[k];
                    if (x2 < 0 || x2 >= n) continue;
                    int y2 = y1 + dy[k];
                    if (y2 < 0 || y2 >= n) continue;
                    int p2 = pos(x2, y2);
                    if (p2 != p0 && currState.grid[p2] == c1) nb++;
                }
                if (nb == 0) nb = -1;
                else nb = 8 - nb;
            }
            aux.val = nb * 2 + rnd.nextInt(10);
            aux.len = currState.len + 1;
            if (nextStates.add(aux)) {
                aux.moves = Arrays.copyOf(currState.moves, currState.moves.length + 1);
                aux.moves[aux.moves.length - 1] = move(p0, p1);
                aux.grid = currState.grid.clone();
                aux.grid[p0] = -1;
                aux.grid[p1] = (byte) c0;
                aux = new State();
            }
        }
        return expanded;
    }

    private static void output(State s) {
        StringBuilder sb = new StringBuilder();
        sb.append(s.moves.length).append(System.lineSeparator());
        for (int m : s.moves) {
            int p0 = m & 1023;
            int p1 = m >>> 10;
            sb.append(y(p0)).append(' ');
            sb.append(x(p0)).append(' ');
            sb.append(y(p1)).append(' ');
            sb.append(x(p1)).append(System.lineSeparator());
        }
        System.out.print(sb.toString());
        System.out.flush();
    }

    private static void init() {
        try {
            BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
            n = Integer.parseInt(in.readLine());
            c = Integer.parseInt(in.readLine());
            grid = new byte[n << 5];
            for (int y = 0; y < n; y++) {
                for (int x = 0; x < n; x++) {
                    grid[pos(x, y)] = Byte.parseByte(in.readLine());
                }
            }
            d = new int[c << 3];
            for (int i = 0; i < c; i++) {
                for (int j = 0; j < c; j++) {
                    d[colorPair(i, j)] = Byte.parseByte(in.readLine());
                }
            }
            in.close();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static int x(int p) {
        return p & 31;
    }

    private static int y(int p) {
        return p >>> 5;
    }

    private static int pos(int x, int y) {
        return (y << 5) | x;
    }

    private static int move(int p0, int p1) {
        return (p1 << 10) | p0;
    }

    private static int colorPair(int c0, int c1) {
        return (c1 << 3) | c0;
    }

    static class State implements Comparable<State> {
        byte[] grid;
        int[] moves;
        int pos, score, chain, val, len;

        public int compareTo(State o) {
            int cmp = Integer.compare((o.chain * 6 + o.score + o.val) * len, (chain * 6 + score + val) * o.len);
            if (cmp != 0) return cmp;
            cmp = Integer.compare(o.chain, chain);
            if (cmp != 0) return cmp;
            return Integer.compare(o.val, val);
        }
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

    boolean add(T item) {
        if (size >= beamWidth && ((Comparable<T>) items[beamWidth - 1]).compareTo(item) <= 0) return false;
        int pos = Arrays.binarySearch(items, 0, size, item);
        if (pos < 0) pos = -pos - 1;
        if (pos >= beamWidth) return false;
        if (size < beamWidth) size++;
        for (int i = size - 1; i > pos; i--) {
            items[i] = items[i - 1];
        }
        items[pos] = item;
        return true;
    }

    T get(int idx) {
        return items[idx];
    }

    void remove(int idx) {
        size--;
        for (int i = idx; i < size; i++) {
            items[i] = items[i + 1];
        }
    }

    int size() {
        return size;
    }

    void clear() {
        size = 0;
    }
}
