import java.io.*;
import java.util.*;

public class ChickenRun {
    private final Map<Key, Integer> memo = new HashMap<Key, Integer>();
    private int n, minFind, numMoves;
    private int[] chickens, farmers, targets;
    private int[][] dist;
    private byte[] grid;
    private boolean[] usedChickens, usedFarmers, collected;
    private static final byte EMPTY = 0, CHICKEN = 1, WALL = 2, FARMER = 3;
    private final SplittableRandom rnd = new SplittableRandom(9999);
    private static final int[] delta = new int[] {1,-1,32,-32,0};
    private final int[] options = new int[5], moves = new int[256];
    private final List<Integer> candidates = new ArrayList<Integer>(), pick = new ArrayList<Integer>();

    public static void main(String[] args) throws Exception {
        new ChickenRun().run();
    }

    private void run() throws Exception {
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        n = Integer.parseInt(br.readLine());
        grid = new byte[(n + 2) << 5];
        chickens = new int[n * n];
        farmers = new int[n * n];
        Arrays.fill(grid, WALL);
        readGrid(br);
        usedFarmers = new boolean[farmers.length];
        collected = new boolean[farmers.length];
        usedChickens = new boolean[chickens.length];
        targets = new int[farmers.length];
        initDist();
        int elapsedTime = 0;
        for (int turn = n * n; turn > 0; turn--) {
            System.out.print(move(elapsedTime > 7000));//TODO
            System.out.flush();
            elapsedTime = Integer.parseInt(br.readLine());
            if (readGrid(br)) break;
        }
        System.out.println("-1");
        System.out.flush();
        br.close();
    }

    private boolean readGrid(BufferedReader br) throws Exception {
        int numChickens = 0;
        int numFarmers = 0;
        for (int y = 1; y <= n; y++) {
            int p = pos(1, y);
            for (int x = 1; x <= n; x++, p++) {
                char c = br.readLine().charAt(0);
                if (c == '.') grid[p] = EMPTY;
                else if (c == 'P') grid[farmers[numFarmers++] = p] = FARMER;
                else if (c == 'C') grid[chickens[numChickens++] = p] = CHICKEN;
            }
        }
        if (numChickens < chickens.length) chickens = Arrays.copyOf(chickens, numChickens);
        if (numFarmers < farmers.length) farmers = Arrays.copyOf(farmers, numFarmers);
        return numChickens == 0;
    }

    private void initDist() {
        int[] queue = new int[grid.length];
        dist = new int[grid.length][grid.length];
        for (int i = 0; i < grid.length; i++) {
            if (grid[i] == WALL) continue;
            int[] d = dist[i];
            Arrays.fill(d, 9999);
            queue[0] = i;
            d[i] = 0;
            int curr = 0;
            int tot = 1;
            while (curr < tot) {
                int p = queue[curr++];
                int nd = d[p] + 1;
                for (int a : delta) {
                    if (a == 0) continue;
                    int np = p + a;
                    if (grid[np] == WALL || d[np] <= nd) continue;
                    d[np] = nd;
                    queue[tot++] = np;
                }
            }
        }
    }

    private String move(boolean fast) {
        numMoves = 0;
        memo.clear();
        Arrays.fill(usedFarmers, false);
        Arrays.fill(collected, false);
        catchChickens();
        findTargets(fast);
        moveUnassigned();
        return movesToStr();
    }

    private int[] findMoves(int[] farmersPos, int chickenPos, int maxDepth, boolean[] fixed) {
        int[] pos = Arrays.copyOf(farmersPos, farmersPos.length + 1);
        pos[pos.length - 1] = chickenPos;
        int[] orgPos = pos.clone();
        minFind = 1000;
        int[] findArr = new int[pos.length - 1];
        Arrays.fill(findArr, -1);
        go(0, 0, pos, maxDepth, orgPos, findArr, fixed);
        return findArr;
    }

    private void applyMoves(int[] farmersIdx, int[] findArr) {
        for (int i = 0; i < farmersIdx.length; i++) {
            int idx = farmersIdx[i];
            int target = findArr[i];
            int p = farmers[idx];
            if (p != target) {
                if (grid[target] == FARMER) continue;
                for (int dir = 0; dir < delta.length - 1; dir++) {
                    if (target == p + delta[dir]) {
                        moves[numMoves++] = move(p, dir);
                        grid[p] = EMPTY;
                        grid[target] = FARMER;
                        farmers[idx] = target;
                        usedFarmers[idx] = true;
                        break;
                    }
                }
            } else usedFarmers[idx] = true;
        }
    }

    private int go(int t, int idx, int[] pos, int maxDepth, int[] orgPos, int[] findArr, boolean[] fixed) {
        Key key = null;
        if (t > 0) {
            key = new Key(t, idx, pos);
            Integer prev = memo.get(key);
            if (prev != null) return prev;
        }
        int p = pos[idx];
        int ret = 200;
        if (idx < pos.length - 1) {
            int target = pos[pos.length - 1];
            int[] dt = dist[target];
            int cd = dt[p];
            NEXT: for (int dir = 0; dir < 5; dir++) {
                int np = p + delta[dir];
                if (grid[np] == WALL) continue;
                if (np == target) {
                    if (t > 0) memo.put(key, t * 10);
                    return t * 10;
                }
                int dnp = dt[np];
                if (dnp > cd) continue;
                if (t == 0 && fixed[idx]) {
                    if (dir != 4) continue;
                } else {
                    if (cd > 3 && dnp == cd) continue;
                }
                for (int j = 0; j < idx; j++) {
                    if (pos[j] == np) continue NEXT;
                }
                if (t == 0 && dir != 4) {
                    for (int i = 0; i < farmers.length; i++) {
                        if ((usedFarmers[i]||collected[i]) && np == farmers[i]) continue NEXT;
                    }
                }
                pos[idx] = np;
                int v = go(t, idx + 1, pos, maxDepth, orgPos, findArr, fixed);
                if (v < ret) {
                    ret = v;
                    if (idx == pos.length - 2 && t == 0 && ret < minFind) {
                        minFind = ret;
                        System.arraycopy(pos, 0, findArr, 0, findArr.length);
                    }
                }
            }
        } else {
            int cnt = 0;
            ret = 0;
            NEXT: for (int i = 0; i < 4; i++) {
                int np = p + delta[i];
                if (grid[np] == WALL) continue;
                for (int j = 0; j < pos.length - 1; j++) {
                    if (np == pos[j]) continue NEXT;
                }
                if (t == 0) {
                    for (int j = 0; j < farmers.length; j++) {
                        if ((usedFarmers[j]||collected[j]) && np == farmers[j]) continue NEXT;
                    }
                }
                for (int j = 0; j < 4; j++) {
                    int nj = np + delta[j];
                    if (grid[nj] == WALL) continue;
                    for (int k = 0; k < pos.length - 1; k++) {
                        if (nj == pos[k]) continue NEXT;
                    }
                    if (t == 0) {
                        for (int k = 0; k < farmers.length; k++) {
                            if ((usedFarmers[k]||collected[k]) && nj == farmers[k]) continue NEXT;
                        }
                    }
                }
                pos[idx] = np;
                if (t < maxDepth) ret += go(t + 1, 0, pos, maxDepth, orgPos, findArr, fixed);
                else {
                    int dx = distBorder(x(np));
                    int dy = distBorder(y(np));
                    ret += t * 10 + 10 + Math.min(dx, dy) + dx + dy;
                }
                cnt++;
            }
            if (cnt == 0) {
                if (t < maxDepth) ret = go(t + 1, 0, pos, maxDepth, orgPos, findArr, fixed);
                else {
                    int dx = distBorder(x(p));
                    int dy = distBorder(y(p));
                    ret += t * 10 + 10 + Math.min(dx, dy) + dx + dy;
                }
            } else ret /= cnt;
            if (t == maxDepth) ret += cnt * 20;
            else ret += cnt;
            boolean frozen = true;
            for (int j = 0; j < pos.length - 1; j++) {
                if (pos[j] != orgPos[j]) {
                    frozen = false;
                    break;
                }
            }
            if (frozen) ret += 50;
            for (int j = 0; j < pos.length - 1; j++) {
                int[] dj = dist[pos[j]];
                for (int k = j + 1; k < pos.length - 1; k++) {
                    if (dj[pos[k]] == 1) ret++;
                }
            }
        }
        pos[idx] = p;
        if (t > 0) memo.put(key, ret);
        return ret;
    }

    private void catchChickens() {
        for (int i = 0; i < chickens.length; i++) {
            int ci = chickens[i];
            int idx = -1;
            int min = 1000;
            int dd = -1;
            for (int j = 0; j < farmers.length; j++) {
                if (usedFarmers[j] || collected[j]) continue;
                int fj = farmers[j];
                for (int dir = 0; dir < 4; dir++) {
                    if (fj + delta[dir] == ci) {
                        int curr = Math.min(distBorder(x(fj)), distBorder(y(fj)));
                        if (curr < min) {
                            min = curr;
                            idx = j;
                            dd = dir;
                        }
                    }
                }
            }
            if (idx >= 0) {
                int f = farmers[idx];
                grid[f] = EMPTY;
                grid[ci] = FARMER;
                moves[numMoves++] = move(f, dd);
                farmers[idx] = ci;
                collected[idx] = true;
                int[] newChickens = new int[chickens.length - 1];
                System.arraycopy(chickens, 0, newChickens, 0, i);
                System.arraycopy(chickens, i + 1, newChickens, i, chickens.length - i - 1);
                chickens = newChickens;
                i--;
            }
        }
    }

    private void moveUnassigned() {
        for (int loop = 0; loop < 2; loop++) {
            for (int i = 0; i < farmers.length; i++) {
                if (usedFarmers[i] || collected[i]) continue;
                int target = targets[i];
                if (target == -1) continue;
                int min = Integer.MAX_VALUE;
                int cnt = 0;
                int p = farmers[i];
                int ct = chickens[target];
                int[] dt = dist[ct];
                for (int dir = 0; dir < 5; dir++) {
                    int np = p + delta[dir];
                    int ng = grid[np];
                    if (ng == WALL || (ng == FARMER && np != p)) continue;
                    int nd = dt[np];
                    int score = nd * 20;
                    int[] dp = dist[np];
                    for (int j = 0; j < farmers.length; j++) {
                        if (i != j && target == targets[j]) score -= dp[farmers[j]];
                    }
                    score -= distBorder(x(np));
                    score -= distBorder(y(np));
                    if (dir == 4) score += 16;
                    if (score < min) {
                        min = score;
                        cnt = 0;
                    }
                    if (score == min) options[cnt++] = dir;
                }
                if (cnt == 0) continue;
                int dir = options[cnt == 1 ? 0 : rnd.nextInt(cnt)];
                int np = p + delta[dir];
                if (p != np) {
                    grid[p] = EMPTY;
                    grid[np] = FARMER;
                    moves[numMoves++] = move(p, dir);
                    farmers[i] = np;
                    usedFarmers[i] = true;
                }
            }
        }
    }

    private void findTargets(boolean fast) {
        Arrays.fill(usedChickens, false);
        candidates.clear();
        for (int j = 0; j < farmers.length; j++) {
            if (!usedFarmers[j]) candidates.add(j);
        }
        Arrays.fill(targets, -1);
        int cc = chickens.length;
        int[] ps = new int[2];
        boolean[] fixed = new boolean[2];
        while (!candidates.isEmpty() && cc > 0) {
            int minScore = Integer.MAX_VALUE;
            int best = -1;
            int len = Math.min(8, Math.max(2, candidates.size() / cc));
            for (int i = 0; i < chickens.length; i++) {
                if (usedChickens[i]) continue;
                int ci = chickens[i];
                int[] di = dist[ci];
                Collections.sort(candidates, new Comparator<Integer>() {
                    public int compare(Integer a, Integer b) {
                        int fa = farmers[a];
                        int fb = farmers[b];
                        return Integer.compare(di[fa], di[fb]);
                    }
                });
                int ll = Math.min(len, candidates.size());
                int score = 0;
                for (int j = 0; j < ll; j++) {
                    int idx = candidates.get(j);
                    score += di[farmers[idx]];
                    if (collected[idx]) score++;
                }
                score *= 3;
                for (int j = 0; j < chickens.length; j++) {
                    if (i == j) continue;
                    int d = di[chickens[j]];
                    if (d <= 4) score -= 5 - d;
                }
                int xc = x(ci);
                score += distBorder(xc);
                int yc = y(ci);
                score += distBorder(yc);
                int x0 = 0;
                int x1 = n + 1;
                int y0 = 0;
                int y1 = n + 1;
                for (int j = 0; j < ll; j++) {
                    int p = farmers[candidates.get(j)];
                    int xp = x(p);
                    int yp = y(p);
                    if (xp < xc && xp > x0) x0 = xp;
                    if (xp > xc && xp < x1) x1 = xp;
                    if (yp < yc && yp > y0) y0 = yp;
                    if (yp > yc && yp < y1) y1 = yp;
                    int[] dp = dist[p];
                    int dip = di[p];
                    for (int k = 0; k < chickens.length; k++) {
                        if (i == k) continue;
                        if (dp[chickens[k]] < dip) score++;
                    }
                }
                score *= n;
                for (int j = 0; j < farmers.length; j++) {
                    int d = di[farmers[j]];
                    if (d <= 5) score += 6 - d;
                }
                score += (x1 - x0 - 1) * (y1 - y0 - 1);
                if (pick.size() == 2 && score < minScore + 10 && !fast) {
                    for (int j = 0; j < ps.length; j++) {
                        int idx = pick.get(j);
                        ps[j] = farmers[idx];
                        fixed[j] = collected[idx];
                    }
                    findMoves(ps, ci, 5, fixed);
                    score += Math.min(50, minFind);
                } 
                if (score < minScore) {
                    minScore = score;
                    best = i;
                    pick.clear();
                    pick.addAll(candidates.subList(0, ll));
                }
            }
            if (best == -1) break;
            int cb = chickens[best];
            usedChickens[best] = true;
            if (!fast) {
                if (dist[cb][farmers[pick.get(0)]] <= 7) {
                    int[] pos = new int[Math.min(4, pick.size())];
                    int[] cand = new int[pos.length];
                    boolean[] ff = new boolean[pos.length];
                    for (int j = 0; j < pos.length; j++) {
                        int idx = cand[j] = pick.get(j);
                        pos[j] = farmers[idx];
                        ff[j] = collected[idx];
                    }
                    int[] found = findMoves(pos, cb, 7 - pos.length, ff);
                    int val = minFind;
                    if (cand.length >= 2 && cand.length <= 3 && val <= 40) {
                        pos = Arrays.copyOf(pos, pos.length - 1);
                        ff = Arrays.copyOf(ff, ff.length - 1);
                        int[] found2 = findMoves(pos, cb, 7 - pos.length, ff);
                        int val2 = minFind;
                        if (val2 <= val) {
                            val = val2;
                            pick.subList(pos.length, pick.size()).clear();
                            found = found2;
                            cand = Arrays.copyOf(cand, cand.length - 1);
                        }
                    }
                    if (val < 400) applyMoves(cand, found);
                }
            }
            for (int j : pick) {
                if (!usedFarmers[j]) targets[j] = best;
            }
            candidates.removeAll(pick);
            cc--;
        }
    }

    private final String movesToStr() {
        StringBuilder sb = new StringBuilder(13 * numMoves + 4);
        sb.append(numMoves).append("\n");
        for (int i = 0; i < numMoves; i++) {
            sb.append(moveToStr(moves[i]));
        }
        return sb.toString();
    }

    private static final String moveToStr(int mv) {
        int dir = mv >>> 10;
        int x = x(mv) - 1;
        int y = (y(mv) & 31) - 1;
        StringBuilder sb = new StringBuilder(13);
        sb.append(y).append(' ');
        sb.append(x).append(' ');
        if (dir == 0) x++;
        else if (dir == 1) x--;
        else if (dir == 2) y++;
        else y--;
        sb.append(y).append(' ');
        sb.append(x).append('\n');
        return sb.toString();
    }

    private static final int move(int pos, int dir) {
        return pos | (dir << 10);
    }

    private static final int pos(int x, int y) {
        return x | (y << 5);
    }

    private static final int y(int p) {
        return p >>> 5;
    }

    private static final int x(int p) {
        return p & 31;
    }

    private int distBorder(int v) {
        return Math.min(v - 1, n - v);
    }
}

class Key {
    private final short[] v;
    private final int hc;

    public Key(int a, int b, int[] arr) {
        v = new short[arr.length + 2];
        for (int i = 0; i < arr.length; i++) {
            v[i] = (short) arr[i];
        }
        Arrays.sort(v, 0, arr.length - 1);
        v[v.length - 2] = (short) a;
        v[v.length - 1] = (short) b;
        hc = Arrays.hashCode(v);
    }

    public int hashCode() {
        return hc;
    }

    public boolean equals(Object obj) {
        if (this == obj) return true;
        Key other = (Key) obj;
        return Arrays.equals(v, other.v);
    }
}
