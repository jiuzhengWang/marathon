import java.io.*;
import java.util.*;

public class PipeConnector {
    private static int n, numColors, actualPenalty, penalty, currSum, currCrossings, bestScore, cycle, mask, shift, add;
    private static int[] colors, values, ends, dists, grid;
    private static int[][] paths, neighbors, bestPaths, closers;
    private static final long timeLimit = 9800;
    private static final long start = System.currentTimeMillis();
    private static final int[] queue1 = new int[65536], queue2 = new int[65536], auxPath = new int[1024], auxCand = new int[4];
    private static final SplittableRandom rnd = new SplittableRandom(19720909);
    private static final double[] log = new double[1 << 16];

    public static void main(String[] args) throws Exception {
        init();
        int rep = 15;
        if (n >= 27) rep = 3;
        else if (n >= 23) rep = 4;
        else if (n >= 19) rep = 5;
        else if (n >= 15) rep = 6;
        else if (n >= 11) rep = 10;
        double t0 = 4.8;
        for (int i = 1; i <= rep; i++) {
            solve(start + timeLimit * i / rep, t0);
            t0 += actualPenalty / 80.0;
        }
        output();
    }

    private static void solve(long timeout, double t0) {
        Arrays.fill(paths, null);
        for (int i = 0; i < grid.length; i++) {
            if (grid[i] > 0) grid[i] = 0;
        }
        currSum = currCrossings = 0;
        long start = System.currentTimeMillis();
        t0 /= timeout - start;
        double temp = t0;
        int[] saveGrid = grid.clone();
        int saveSum = 0;
        int saveCrossings = 0;
        penalty = (actualPenalty + 1) / 2;
        while (true) {
            if ((++cycle & 127) == 0) {
                long t = System.currentTimeMillis();
                if (t >= timeout) break;
                temp = (timeout - t) * t0;
                penalty = (int) ((actualPenalty + (timeout - t) * actualPenalty / (timeout - start) + 1) / 2);
            }
            int p1 = ends[rnd.nextInt(ends.length)];
            int[] pt1 = paths[p1];
            int[] nb1 = neighbors[p1];
            int p2 = nb1[rnd.nextInt(nb1.length)];
            int currScore = score();
            int[] pt2 = paths[p2];
            int[] npt1 = null;
            int[] npt2 = null;
            double minGain = log[rnd.nextInt(log.length)] * temp;
            if (pt1 == null && pt2 == null) {
                npt1 = connect(p1, p2);
            } else if (pt1 == pt2) {
                disconnect(pt1);
                pt2 = null;
                int mode = rnd.nextInt(3);
                if (mode == 2) {
                    int[] c = closers[p1];
                    int p3 = c[rnd.nextInt(c.length)];
                    if (p3 == p1 || p3 == p2) mode = cycle&1;
                    else {
                        int[] pt3 = paths[p3];
                        if (pt3 == null) mode = cycle&1;
                        else {
                            pt2 = pt3;
                            int p4 = otherEnd(pt3, p3);
                            disconnect(pt3);
                            npt2 = connect(p4, p3);
                            npt1 = connect(p2, p1);
                        }
                    }
                }
                if (mode == 0) npt1 = connect(p1, p2);
            } else if (pt1 != null && pt2 != null) {
                int p3 = otherEnd(pt1, p1);
                int p4 = otherEnd(pt2, p2);
                double dv = minGain + (values[p1] - values[p2]) * (values[p3] - values[p4]);
                if (currCrossings * penalty < dv || (getCrossings(pt1) + getCrossings(pt2)) * penalty < dv) continue;
                disconnect(pt1);
                disconnect(pt2);
                npt1 = connect(p1, p4);
                npt2 = connect(p2, p3);
            } else if (pt1 != null) {
                int p3 = otherEnd(pt1, p1);
                double dv = minGain + (values[p1] - values[p2]) * values[p3];
                if (currCrossings * penalty < dv || getCrossings(pt1) * penalty < dv) continue;
                disconnect(pt1);
                npt2 = connect(p2, p3);
            } else {
                int p3 = otherEnd(pt2, p2);
                double dv = minGain + (values[p2] - values[p1]) * values[p3];
                if (currCrossings * penalty < dv || getCrossings(pt2) * penalty < dv) continue;
                disconnect(pt2);
                npt1 = connect(p1, p3);
            }
            int newScore = score();
            double gain = newScore - currScore;
            if (gain >= minGain) {
                System.arraycopy(grid, 0, saveGrid, 0, grid.length);
                saveCrossings = currCrossings;
                saveSum = currSum;
                newScore = actualScore();
                if (newScore > bestScore) {
                    bestScore = newScore;
                    System.arraycopy(paths, 0, bestPaths, 0, paths.length);
                }
            } else {
                disconnectFast(npt1);
                disconnectFast(npt2);
                connectFast(pt1);
                connectFast(pt2);
                System.arraycopy(saveGrid, 0, grid, 0, grid.length);
                currCrossings = saveCrossings;
                currSum = saveSum;
            }
        }
    }

    private static void output() {
        int c = 0;
        for (int i = 0; i < bestPaths.length; i++) {
            int[] pt = bestPaths[i];
            if (pt != null && pt[0] == i) c++;
        }
        StringBuilder sb = new StringBuilder();
        sb.append(c);
        sb.append(System.lineSeparator());
        for (int i = 0; i < bestPaths.length; i++) {
            int[] pt = bestPaths[i];
            if (pt != null && pt[0] == i) {
                sb.append(pt.length);
                sb.append(System.lineSeparator());
                for (int j = 0; j < pt.length; j++) {
                    int p = pt[j];
                    sb.append(y(p));
                    sb.append(' ');
                    sb.append(x(p));
                    sb.append(System.lineSeparator());
                }
            }
        }
        System.out.print(sb);
        System.out.flush();
    }

    private static int[] connectFast(int p1, int p2) {
        int curr = 0;
        int tot = 1;
        queue1[0] = p1;
        int x1 = x(p1);
        int y1 = y(p1);
        int x2 = x(p2);
        int y2 = y(p2);
        int inf = 9999;
        Arrays.fill(dists, inf);
        dists[p1] = 0;
        int md = inf;
        while (curr < tot) {
            int p = queue1[curr++];
            int d = dists[p] + 1;
            if (d > md) continue;
            int x = x(p);
            int y = y(p);
            for (int i = 0; i < 4; i++) {
                int np = p;
                switch (i) {
                case 0:
                    if (x1 >= x2 || x == n - 1) continue;
                    np++;
                    break;
                case 1:
                    if (x1 <= x2 || x == 0) continue;
                    np--;
                    break;
                case 2:
                    if (y1 >= y2 || y == n - 1) continue;
                    np += add;
                    break;
                default:
                    if (y1 <= y2 || y == 0) continue;
                    np -= add;
                }
                if (np == p2) md = d;
                else if (grid[np] == 0 && d < md && d < dists[np]) dists[queue1[tot++] = np] = d;
            }
        }
        if (md == inf) return null;
        auxPath[0] = p2;
        int len = 1;
        int p = p2;
        while (md != 0) {
            int x = x(p);
            int y = y(p);
            int numCand = 0;
            int nd = md - 1;
            for (int i = 0; i < 4; i++) {
                int np = p;
                switch (i) {
                case 0:
                    if (x == n - 1) continue;
                    np++;
                    break;
                case 1:
                    if (x == 0) continue;
                    np--;
                    break;
                case 2:
                    if (y == n - 1) continue;
                    np += add;
                    break;
                default:
                    if (y == 0) continue;
                    np -= add;
                }
                if (nd == dists[np]) auxCand[numCand++] = np;
            }
            md = dists[p = auxPath[len++] = auxCand[numCand == 1 ? 0 : rnd.nextInt(numCand)]];
        }
        int[] pt = Arrays.copyOf(auxPath, len);
        connect(pt);
        return pt;
    }

    private static int[] connect(int p1, int p2) {
        int[] fast = connectFast(p1, p2);
        if (fast != null) return fast;
        int curr1 = 0;
        int curr2 = 0;
        int tot1 = 1;
        int tot2 = 0;
        queue1[0] = p1;
        int pp = actualPenalty > 12 ? penalty * 2 + 2 : rnd.nextInt(penalty, penalty * 3 + 5);
        int inf = pp + 2 * n;
        Arrays.fill(dists, inf);
        dists[p1] = 0;
        int md = inf;
        while (true) {
            int p = 0;
            if (curr1 < tot1) p = queue1[curr1++];
            else if (curr2 < tot2) p = queue2[curr2++];
            else break;
            int d = dists[p] + 1;
            if (d > md) continue;
            int x = x(p);
            int y = y(p);
            for (int i = 0; i < 4; i++) {
                int np = p;
                switch (i) {
                case 0:
                    if (x == n - 1) continue;
                    np++;
                    break;
                case 1:
                    if (x == 0) continue;
                    np--;
                    break;
                case 2:
                    if (y == n - 1) continue;
                    np += add;
                    break;
                default:
                    if (y == 0) continue;
                    np -= add;
                }
                if (np == p2) md = d;
                else {
                    switch (grid[np]) {
                    case 0:
                        if (d < md && d < dists[np]) dists[queue1[tot1++] = np] = d;
                        break;
                    case 1:
                        int nd = d + pp;
                        if (nd < md && nd < dists[np]) dists[queue2[tot2++] = np] = nd;
                    }
                }
            }
        }
        if (md == inf) return null;
        auxPath[0] = p2;
        int len = 1;
        int p = p2;
        while (md != 0) {
            int x = x(p);
            int y = y(p);
            int numCand = 0;
            int nd = md - (grid[p] == 1 ? pp + 1 : 1);
            for (int i = 0; i < 4; i++) {
                int np = p;
                switch (i) {
                case 0:
                    if (x == n - 1) continue;
                    np++;
                    break;
                case 1:
                    if (x == 0) continue;
                    np--;
                    break;
                case 2:
                    if (y == n - 1) continue;
                    np += add;
                    break;
                default:
                    if (y == 0) continue;
                    np -= add;
                }
                if (nd == dists[np]) auxCand[numCand++] = np;
            }
            md = dists[p = auxPath[len++] = auxCand[numCand == 1 ? 0 : rnd.nextInt(numCand)]];
        }
        int[] pt = Arrays.copyOf(auxPath, len);
        connect(pt);
        return pt;
    }

    private static int[] neighbors(int pos, int color) {
        List<Integer> neighbors = new ArrayList<Integer>();
        int curr = 0;
        int tot = 1;
        queue1[0] = pos;
        Arrays.fill(dists, 999);
        dists[pos] = 0;
        while (curr < tot) {
            int p = queue1[curr++];
            int x = x(p);
            int y = y(p);
            int nd = dists[p] + 1;
            for (int i = 0; i < 4; i++) {
                int np = p;
                switch (i) {
                case 0:
                    if (x == n - 1) continue;
                    np++;
                    break;
                case 1:
                    if (x == 0) continue;
                    np--;
                    break;
                case 2:
                    if (y == n - 1) continue;
                    np += add;
                    break;
                default:
                    if (y == 0) continue;
                    np -= add;
                }
                if (dists[np] > nd) {
                    dists[np] = nd;
                    if (grid[np] == 0) queue1[tot++] = np;
                    else if (colors[np] == color) neighbors.add(np);
                }
            }
        }
        int sum = 0;
        int[] weight = new int[n << shift];
        for (int p : neighbors) {
            sum += weight[p] = Math.max(1, n / 2 - dists[p]);
        }
        int[] ret = new int[sum];
        sum = 0;
        for (int p : neighbors) {
            int k = weight[p];
            for (int j = 0; j < k; j++) {
                ret[sum++] = p;
            }
        }
        return ret;
    }

    private static void connect(int[] pt) {
        if (pt == null) return;
        int p1 = pt[0];
        int p2 = pt[pt.length - 1];
        paths[p1] = paths[p2] = pt;
        currSum += values[p1] * values[p2];
        for (int i = 1; i < pt.length - 1; i++) {
            if (grid[pt[i]]++ >= 1) currCrossings++;
        }
    }

    private static int getCrossings(int[] pt) {
        if (pt == null || currCrossings == 0) return 0;
        int ret = 0;
        for (int i = 1; i < pt.length - 1; i++) {
            if (grid[pt[i]] > 1) ret++;
        }
        return ret;
    }

    private static void disconnectFast(int[] pt) {
        if (pt != null) paths[pt[0]] = paths[pt[pt.length - 1]] = null;
    }

    private static void connectFast(int[] pt) {
        if (pt != null) paths[pt[0]] = paths[pt[pt.length - 1]] = pt;
    }

    private static void disconnect(int[] pt) {
        if (pt == null) return;
        int p1 = pt[0];
        int p2 = pt[pt.length - 1];
        paths[p1] = paths[p2] = null;
        currSum -= values[p1] * values[p2];
        for (int i = 1; i < pt.length - 1; i++) {
            if (--grid[pt[i]] >= 1) currCrossings--;
        }
    }

    private static int otherEnd(int[] pt, int p) {
        int first = pt[0];
        return first == p ? pt[pt.length - 1] : first;
    }

    private static int score() {
        return currSum - penalty * currCrossings;
    }

    private static int actualScore() {
        return currSum - actualPenalty * currCrossings;
    }

    private static void init() throws Exception {
        for (int i = 0; i < log.length; i++) {
            log[i] = Math.log((i + 0.5) / log.length);
        }
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        n = Integer.parseInt(in.readLine());
        numColors = Integer.parseInt(in.readLine());
        actualPenalty = Integer.parseInt(in.readLine());
        mask = n > 16 ? 31 : 15;
        shift = n > 16 ? 5 : 4;
        add = mask + 1;
        grid = new int[n << shift];
        colors = new int[n << shift];
        values = new int[n << shift];
        ends = new int[n * n];
        int[] countPerColor = new int[numColors + 1];
        int numEnds = 0;
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                String[] s = in.readLine().split(" ");
                int val = Integer.parseInt(s[0]);
                if (val > 0) {
                    int p = ends[numEnds++] = pos(x, y);
                    grid[p] = -1;
                    values[p] = val;
                    countPerColor[colors[p] = Integer.parseInt(s[1])]++;
                }
            }
        }
        in.close();
        ends = Arrays.copyOf(ends, numEnds);
        bestPaths = new int[n << shift][];
        paths = new int[n << shift][];
        dists = new int[n << shift];
        neighbors = new int[n << shift][];
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int pos = pos(x, y);
                int color = colors[pos];
                if (color > 0) {
                    int[] np = neighbors[pos] = neighbors(pos, color);
                    if (np.length == 0) {
                        for (int i = 0; i < ends.length; i++) {
                            if (ends[i] == pos) {
                                ends[i] = ends[ends.length - 1];
                                ends = Arrays.copyOf(ends, ends.length - 1);
                                break;
                            }
                        }
                    }
                }
            }
        }
        closers = new int[n << shift][];
        for (int i = 0; i < ends.length; i++) {
            List<Integer> l = new ArrayList<Integer>();
            for (int j = 0; j < ends.length; j++) {
                if (j != i) l.add(ends[j]);
            }
            int p = ends[i];
            int xp = x(p);
            int yp = y(p);
            Collections.sort(l, new Comparator<Integer>() {
                public int compare(Integer a, Integer b) {
                    int cmp = Integer.compare(dist(a), dist(b));
                    if (cmp != 0) return cmp;
                    return Integer.compare(values[b], values[a]);
                }
                int dist(int a) {
                    int xa = x(a);
                    int ya = y(a);
                    return Math.abs(xa-xp)+Math.abs(ya-yp);
                }
            });
            int k = l.size();
            int c = 0;
            for (int j : l) {
                for (int o = 0; o < k; o++) {
                    queue1[c++] = j;
                }
                k--;
            }
            closers[p] = Arrays.copyOf(queue1, c); 
        }
    }

    private static int x(int p) {
        return p & mask;
    }

    private static int y(int p) {
        return p >>> shift;
    }

    private static int pos(int x, int y) {
        return (y << shift) | x;
    }
}
