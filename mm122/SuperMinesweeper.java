import java.io.*;
import java.util.*;

public class SuperMinesweeper {
    private final long timeLimit = 9650;
    private long timeout;
    private int[] grid, minBomb, maxBomb;
    private int[][] neighbors, checkNeighbors;
    private final static int unknown = -1;
    private final static int toclear = -2;
    private final static int bomb = 63;
    private int n, m, d, lastPos, maxNeighbors, score = 1, div = 1, maxScore;
    private final Set<Integer> analyse = new TreeSet<Integer>();
    private final int[] auxNeighbors = new int[64];

    private SuperMinesweeper(int n, int m, int d, String cell) {
        this.n = n;
        this.m = m;
        this.d = d;
        int sd = 1;
        while ((sd + 1) * (sd + 1) <= d) {
            sd++;
        }
        grid = new int[n * n];
        minBomb = new int[n * n];
        maxBomb = new int[n * n];
        neighbors = new int[n * n][];
        checkNeighbors = new int[n * n][0];
        int[] a = new int[64];
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int c = 0;
                for (int dy = -sd; dy <= sd; dy++) {
                    int ny = y + dy;
                    if (ny < 0 || ny >= n) continue;
                    int nny = ny * n;
                    int d2 = dy * dy;
                    for (int dx = -sd; dx <= sd; dx++) {
                        int nx = x + dx;
                        if (nx < 0 || nx >= n) continue;
                        if (d2 + dx * dx > d) continue;
                        if (dx == 0 && dy == 0) continue;
                        a[c++] = nx + nny;
                    }
                }
                neighbors[x + y * n] = Arrays.copyOf(a, c);
            }
        }
        maxNeighbors = neighbors[n / 2 * n + n / 2].length;
        maxScore = n * n - m;
        Arrays.fill(grid, unknown);
        String[] s = cell.split(" ");
        int p = Integer.parseInt(s[0]) * n + Integer.parseInt(s[1]);
        grid[p] = 0;
        update(p, 0);
    }

    private void updateNeighbors(int pos) {
        int[] np0 = neighbors[pos];
        for (int p0 : np0) {
            if (grid[p0] != unknown) continue;
            int c = 0;
            int[] np1 = neighbors[p0];
            for (int p1 : np1) {
                int s = grid[p1];
                if (s > unknown && s < bomb) auxNeighbors[c++] = p1;
            }
            checkNeighbors[p0] = Arrays.copyOf(auxNeighbors, c);
        }
    }

    private void update(int pos, int v) {
        int numUnknown = 0;
        int numBombs = 0;
        int[] np = neighbors[pos];
        for (int p : np) {
            int s = grid[p];
            if (s == unknown) numUnknown++;
            else if (s == bomb) numBombs++;
        }
        if (numUnknown > 0 && (numUnknown + numBombs == v || numBombs == v)) {
            int nv = numBombs == v ? toclear : bomb;
            for (int p : np) {
                if (grid[p] == unknown && (grid[p] = nv) == bomb) m--;
            }
        }
    }

    private String move() {
        while (true) {
            boolean finished = true;
            for (int i = 0; i < grid.length; i++) {
                int g = grid[i];
                if (g == toclear || (m == 0 && g == unknown)) {
                    lastPos = i;
                    return String.format("G %d %d", i / n, i % n);
                }
                if (g == unknown) finished = false;
            }
            if (finished || System.currentTimeMillis() >= timeout || !save()) break;
        }
        return "STOP";
    }

    private boolean save() {
        if (System.currentTimeMillis() > timeout) return false;
        List<Map<Integer, Integer>> spending = new ArrayList<Map<Integer, Integer>>();
        Set<Integer> cp = new HashSet<Integer>();
        Iterator<Integer> it = analyse.iterator();
        while (it.hasNext()) {
            int p1 = it.next();
            int g = grid[p1];
            if (g > 0 && g < bomb) {
                cp.clear();
                int[] np = neighbors[p1];
                int cb = 0;
                for (int p2 : np) {
                    int g2 = grid[p2];
                    if (g2 == unknown) cp.add(p2);
                    else if (g2 == bomb) cb++;
                }
                if (!cp.isEmpty()) {
                    minBomb[p1] = cb;
                    maxBomb[p1] = cp.size() + cb;
                    int idx = -1;
                    for (int i = 0; i < spending.size(); i++) {
                        if (intersects(cp, spending.get(i).keySet())) {
                            idx = i;
                            break;
                        }
                    }
                    if (idx == -1) {
                        spending.add(new HashMap<Integer, Integer>());
                        idx = spending.size() - 1;
                    }
                    Map<Integer, Integer> map = spending.get(idx);
                    for (int v : cp) {
                        Integer a = map.get(v);
                        if (a == null) a = 0;
                        map.put(v, a + 1);
                    }
                    for (int i = idx + 1; i < spending.size(); i++) {
                        Map<Integer, Integer> merge = spending.get(i);
                        if (intersects(map.keySet(), merge.keySet())) {
                            spending.remove(i--);
                            for (int v : merge.keySet()) {
                                Integer a = map.get(v);
                                if (a == null) a = 0;
                                map.put(v, a + merge.get(v));
                            }
                        }
                    }
                } else {
                    it.remove();
                }
            }
        }
        boolean ret = false;
        double min = 9e9;
        double prob = 1;
        int cell = -1;
        int pb = m;
        for (int i = 0; i < spending.size(); i++) {
            Map<Integer, Integer> map = spending.get(i);
            int[] pending = arr(map);
            int[] res = new int[pending.length + 2];
            int[] avg = new int[pending.length];
            if (!go(pending, res, 0, timeout, pb, avg)) break;
            double tot = res[pending.length];
            pb = res[pending.length + 1];
            for (int j = 0; j < pending.length; j++) {
                int r = res[j];
                int pj = pending[j];
                int x = pj % n;
                int y = pj / n;
                int border = Math.min(Math.min(y, n - 1 - y), Math.min(x, n - 1 - x));
                double curr = r / tot - 0.001 * (map.get(pj) + map.size()) + 0.1 * border / n;
                if (d <= 2) curr += avg[j] / (tot * maxNeighbors * maxNeighbors);
                if (curr < min) {
                    min = curr;
                    prob = r / tot;
                    cell = pj;
                }
                if (r == 0) {
                    grid[pj] = toclear;
                    ret = true;
                } else if (r == tot) {
                    grid[pj] = bomb;
                    m--;
                    ret = true;
                }
            }
        }
        if (!ret && cell != -1) {
            double currScore = score / (double) div;
            double newScore = (0.6 * maxScore) * (1 - prob) / div + score * prob / (div + 1);
            if (newScore > currScore) {
                grid[cell] = toclear;
                ret = true;
            }
        }
        return ret;
    }

    private boolean intersects(Set<Integer> a, Set<Integer> b) {
        if (a.size() > b.size()) return intersects(b, a);
        for (Integer v : a) {
            if (b.contains(v)) return true;
        }
        return false;
    }

    private boolean go(int[] pending, int[] res, int idx, long tl, int pb, int[] avg) {
        if (pb < 0) return true;
        if (idx == pending.length) {
            for (int i = 0; i < pending.length; i++) {
                int p = pending[i];
                if (grid[p] == bomb) res[i]++;
                else if (d <= 2) {
                    int[] np = checkNeighbors[p];
                    int sum = 0;
                    for (int a : np) {
                        sum += grid[a];
                    }
                    avg[i] += sum;
                }
            }
            res[pending.length]++;
            res[pending.length + 1] = Math.max(res[pending.length + 1], pb);
            return true;
        }
        if ((idx & 7) == 0 && System.currentTimeMillis() > tl) return false;
        int pos = pending[idx];
        int[] np0 = checkNeighbors[pos];
        boolean ok0 = true;
        boolean ok1 = true;
        for (int p0 : np0) {
            int g0 = grid[p0];
            if (minBomb[p0] + 1 > g0) {
                ok1 = false;
                if (!ok0) return true;
            }
            if (maxBomb[p0] - 1 < g0) {
                ok0 = false;
                if (!ok1) return true;
            }
        }
        if (ok0 && ok1) {
            for (int p0 : np0) {
                maxBomb[p0]--;
            }
            if (!go(pending, res, idx + 1, tl, pb, avg)) return false;
            for (int p0 : np0) {
                maxBomb[p0]++;
                minBomb[p0]++;
            }
            grid[pos] = bomb;
            if (!go(pending, res, idx + 1, tl, pb - 1, avg)) return false;
            grid[pos] = unknown;
            for (int p0 : np0) {
                minBomb[p0]--;
            }
        } else if (ok0) {
            for (int p0 : np0) {
                maxBomb[p0]--;
            }
            if (!go(pending, res, idx + 1, tl, pb, avg)) return false;
            for (int p0 : np0) {
                maxBomb[p0]++;
            }
        } else if (ok1) {
            for (int p0 : np0) {
                minBomb[p0]++;
            }
            grid[pos] = bomb;
            if (!go(pending, res, idx + 1, tl, pb - 1, avg)) return false;
            grid[pos] = unknown;
            for (int p0 : np0) {
                minBomb[p0]--;
            }
        }
        return true;
    }

    private int[] arr(Map<Integer, Integer> s) {
        Integer[] a = new Integer[s.size()];
        int c = 0;
        Map<Integer, Integer> score = new HashMap<Integer, Integer>();
        int m = maxNeighbors;
        for (int p0 : s.keySet()) {
            a[c++] = p0;
            int v = s.get(p0) * m;
            int[] np = checkNeighbors[p0];
            for (int p1 : np) {
                v -= maxBomb[p1] - minBomb[p1];
            }
            score.put(p0, v);
        }
        Arrays.sort(a, 0, c, new Comparator<Integer>() {
            public int compare(Integer a, Integer b) {
                return score.get(b) - score.get(a);
            }
        });
        if (c > 64) c = 64;
        for (int i = 32; i < c; i++) {
            if (s.get(a[i]) == 1) {
                c = i;
                break;
            }
        }
        int[] ret = new int[c];
        for (int i = 0; i < c; i++) {
            ret[i] = a[i];
        }
        return ret;
    }

    private void update(String feedback) {
        if (feedback.length() == 0) return;
        String[] s = feedback.split(" ");
        timeout = System.currentTimeMillis() + (timeLimit - Long.parseLong(s[1]));
        if (s[0].charAt(0) == 'B') {
            if (grid[lastPos] != unknown) updateNeighbors(lastPos);
            grid[lastPos] = bomb;
            analyse.remove(lastPos);
            m--;
            div++;
        } else {
            int value = Integer.parseInt(s[0]);
            if (value > 0) analyse.add(lastPos);
            grid[lastPos] = value;
            update(lastPos, value);
            if (value > 0) updateNeighbors(lastPos);
            score++;
        }
    }

    public static void main(String[] args) {
        try {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in), 64);
            int n = Integer.parseInt(br.readLine());
            int m = Integer.parseInt(br.readLine());
            int d = Integer.parseInt(br.readLine());
            String cell = br.readLine();
            SuperMinesweeper sol = new SuperMinesweeper(n, m, d, cell);
            while (true) {
                String move = sol.move();
                System.out.println(move);
                System.out.flush();
                if (move.equals("STOP")) break;
                String feedback = br.readLine();
                if (feedback == null) break;
                sol.update(feedback);
            }
        } catch (Throwable e) {
        }
    }
}