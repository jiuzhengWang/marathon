import java.io.*;
import java.util.*;

public class Jewels {
    private static final int maxMoves = 1000, timeout1 = 9500, timeout2 = 9750;
    private static final byte empty = 10, restOffset = 11, removeMask = 32, colorMask = 31;
    private final int n, numColors, limit, numLoops;
    private final byte[] g, currGrid, order, targetGrid, bestTargetGrid, auxGrid, mirrorGrid;
    private final short[] rejectedColors;
    private final int[] currPlaceMoves, ni, nj, np, lt, pendingMoves = new int[maxMoves], colorSwaps, cs1, cs2, randomPieceIdx;
    private final int[][] li, lj, lp;
    private final byte[][][] allRandomPieces;
    private byte[][] currRandomPieces;
    private SplittableRandom rnd;
    private boolean combo = true;
    private int currMove, currPending, totPending, lastMovesLen, lastBestAdd, currBestAdd;

    private Jewels(int n, int numColors) {
        this.n = n;
        this.numColors = numColors;
        g = new byte[n << 4];
        currGrid = new byte[g.length];
        targetGrid = new byte[g.length];
        bestTargetGrid = new byte[g.length];
        mirrorGrid = new byte[g.length];
        auxGrid = new byte[g.length];
        rejectedColors = new short[g.length];
        order = new byte[numColors];
        for (byte i = 0; i < numColors; i++) {
            order[i] = i;
        }
        lt = new int[n * n];
        li = new int[numColors][n * n];
        lj = new int[numColors][n * n];
        lp = new int[numColors][n * n];
        ni = new int[numColors];
        nj = new int[numColors];
        np = new int[numColors];
        colorSwaps = new int[numColors << 4];
        currPlaceMoves = new int[maxMoves];
        lastBestAdd = 3;
        limit = (numColors == 5 ? n * 3 / 2 : numColors <= 6 ? n * 3 / 2 : n * 2) - (n <= 10 ? 1 : 0);
        cs1 = new int[numColors * (numColors - 1) / 2];
        cs2 = new int[cs1.length];
        int k = 0;
        for (int i = 0; i < numColors; i++) {
            for (int j = i + 1; j < numColors; j++) {
                cs1[k] = pos(i, j);
                cs2[k] = pos(j, i);
                k++;
            }
        }
        numLoops = 250 - numColors * 20;
        allRandomPieces = new byte[numLoops][n][256];
        randomPieceIdx = new int[n];
    }

    private String run(long runtime) {
        currMove++;
        if (currPending < totPending) return toString(pendingMoves[currPending++]);
        if (runtime > timeout2) return toString(toMove(0, 1));
        if (combo && runtime < timeout1) {
            long start = System.currentTimeMillis();
            rnd = new SplittableRandom(currMove * 999);
            for (int y = 0; y < n; y++) {
                int x1 = n - 1;
                int p = pos(0, y);
                for (int x0 = 0; x0 < n; x0++, x1--) {
                    mirrorGrid[p + x0] = currGrid[p + x1];
                    mirrorGrid[p + x1] = currGrid[p + x0];
                }
            }
            for (int i = 0; i < numLoops; i++) {
                byte[][] arpi = allRandomPieces[i];
                for (int x = 0; x < n; x++) {
                    Arrays.fill(arpi[x], empty);
                }
            }
            int maxScore = 0;
            int[] bestMoves = null;
            boolean bestMirror = false;
            int maxRaw = 0;
            int rep = 0;
            NEXT: for (; rep < 16384; rep++) {
                if ((rep & 15) == 0) {
                    if (rep == 128 && bestMoves == null) break;
                    long used = System.currentTimeMillis() - start + runtime;
                    if (rep >= 64 && used > timeout1) break;
                    if (rep >= 256 && (currMove + bestMoves.length) * timeout1 < maxMoves * used) break;
                }
                boolean mirror = (rep & 1) == 0;
                System.arraycopy(mirror ? mirrorGrid : currGrid, 0, g, 0, g.length);
                int[] currMoves = plan();
                if (currMoves != null && currMoves.length + currMove <= maxMoves) {
                    System.arraycopy(mirror ? mirrorGrid : currGrid, 0, g, 0, g.length);
                    int currRaw = 0;
                    for (int m : currMoves) {
                        int p1 = p1(m);
                        int p2 = p2(m);
                        int x1 = x(p1);
                        int x2 = x(p2);
                        int y1 = y(p1);
                        int y2 = y(p2);
                        byte aux = g[p1];
                        g[p1] = g[p2];
                        g[p2] = aux;
                        if (conn(g, aux, x2, y2, p2) || conn(g, g[p1], x1, y1, p1)) {
                            currRaw += eval(g, Math.min(x1, x2), Math.max(x1, x2), Math.min(y1, y2), Math.max(y1, y2), 0);
                        }
                    }
                    System.arraycopy(mirror ? mirrorGrid : currGrid, 0, g, 0, g.length);
                    if (bestMoves != null && currMoves.length * maxRaw > bestMoves.length * currRaw * 1.05) continue NEXT;
                    int totScore = currRaw;
                    for (int loop = 0; loop < numLoops; loop++) {
                        if ((loop & 15) == 0 && System.currentTimeMillis() - start + runtime > timeout1) break NEXT;
                        int currScore = 0;
                        Arrays.fill(randomPieceIdx, 0);
                        currRandomPieces = allRandomPieces[loop];
                        for (int m : currMoves) {
                            int p1 = p1(m);
                            int p2 = p2(m);
                            int x1 = x(p1);
                            int x2 = x(p2);
                            int y1 = y(p1);
                            int y2 = y(p2);
                            byte aux = g[p1];
                            g[p1] = g[p2];
                            g[p2] = aux;
                            if (conn(g, aux, x2, y2, p2) || conn(g, g[p1], x1, y1, p1)) {
                                currScore += eval(g, Math.min(x1, x2), Math.max(x1, x2), Math.min(y1, y2), Math.max(y1, y2), 1);
                            }
                        }
                        totScore += currScore;
                        System.arraycopy(mirror ? mirrorGrid : currGrid, 0, g, 0, g.length);
                    }
                    totScore /= numLoops + 1;
                    if (bestMoves == null || (currMove + lastMovesLen * 3 / 2 >= maxMoves ? maxScore < totScore : currMoves.length * maxScore < bestMoves.length * totScore)) {
                        maxScore = totScore;
                        maxRaw = currRaw;
                        bestMoves = currMoves;
                        lastBestAdd = currBestAdd;
                        bestMirror = mirror;
                    }
                }
            }
            if (bestMoves != null) {
                if (bestMirror) {
                    for (int i = 0; i < bestMoves.length; i++) {
                        bestMoves[i] = mirrorMove(bestMoves[i]);
                    }
                }
                System.arraycopy(bestMoves, 0, pendingMoves, totPending, bestMoves.length);
                lastMovesLen = bestMoves.length;
                totPending += bestMoves.length;
            }
            if (currPending < totPending) return toString(pendingMoves[currPending++]);
            if (currMove > maxMoves - n * 2) combo = false;
        }
        System.arraycopy(currGrid, 0, g, 0, g.length);
        boolean[][] can = new boolean[g.length][numColors];
        for (int y = 0; y < n; y++) {
            int i = y << 4;
            for (int x = 0; x < n; x++, i++) {
                byte gi = currGrid[i];
                boolean[] cani = can[i];
                for (byte c = 0; c < numColors; c++) {
                    if (c == gi) continue;
                    g[i] = c;
                    cani[c] = conn(g, c, x, y, i);
                }
                g[i] = gi;
            }
        }
        int max = -1;
        int mv = -1;
        for (int yi = 0; yi < n; yi++) {
            if (runtime > timeout1 && yi == 2) break;
            for (int yj = yi; yj < n; yj++) {
                int i = yi << 4;
                for (int xi = 0; xi < n; xi++, i++) {
                    byte gi = currGrid[i];
                    boolean[] cani = can[i];
                    int xxj = yj == yi ? xi + 1 : 0;
                    int j = pos(xxj, yj);
                    for (int xj = xxj; xj < n; xj++, j++) {
                        byte gj = currGrid[j];
                        if (gi == gj) continue;
                        boolean ci = cani[gj];
                        boolean cj = can[j][gi];
                        int xmin = 0;
                        int xmax = 0;
                        int ymin = 0;
                        int ymax = 0;
                        if (!ci && !cj) {
                            if ((xj != xi || Math.abs(yj - yi) > 2) && (yj != yi || Math.abs(xj - xi) > 2)) continue;
                            xmin = Math.min(xi, xj);
                            xmax = Math.max(xi, xj);
                            ymin = Math.min(yi, yj);
                            ymax = Math.max(yi, yj);
                        } else if (ci && cj) {
                            xmin = Math.min(xi, xj);
                            xmax = Math.max(xi, xj);
                            ymin = Math.min(yi, yj);
                            ymax = Math.max(yi, yj);
                        } else if (ci) {
                            xmin = xmax = xi;
                            ymin = ymax = yi;
                        } else {
                            xmin = xmax = xj;
                            ymin = ymax = yj;
                        }
                        g[i] = gj;
                        g[j] = gi;
                        int curr = eval(g, xmin, xmax, ymin, ymax, 0);
                        if (curr > max) {
                            max = curr;
                            mv = toMove(i, j);
                        }
                        System.arraycopy(currGrid, 0, g, 0, currGrid.length);
                    }
                }
            }
        }
        return toString(mv);
    }

    private int[] plan() {
        byte[] targetColors = new byte[3];
        int maxValue = 0;
        int bestLastMove = -1;
        currBestAdd = -1;
        for (int j = 0; j < numColors; j++) {
            int a = rnd.nextInt(numColors);
            int b = rnd.nextInt(numColors);
            if (a != b) {
                byte aux = order[a];
                order[a] = order[b];
                order[b] = aux;
            }
        }
        boolean ending = currMove + lastMovesLen + 3 * n >= maxMoves;
        int[] ccnt = new int[numColors];
        int[] colorCount = new int[numColors];
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                ccnt[g[pos(x, y)]]++;
            }
        }
        for (int rep = 0; rep < 12; rep++) {
            int maxLen = 0;
            Arrays.fill(colorSwaps, 0);
            int[][] targets = getTargets();
            int[] t0 = targets[0];
            int xx0 = -1;
            int xx1 = -1;
            for (int i : t0) {
                int y = y(i);
                if (y == 4) {
                    if (xx0 == -1) xx0 = x(i);
                    else {
                        xx1 = x(i);
                        break;
                    }
                }
            }
            int lastMove = toMove(pos(xx0, 1), pos(xx1, 1));
            System.arraycopy(ccnt, 0, colorCount, 0, numColors);
            Arrays.fill(targetColors, empty);
            for (int i = 0; i < targets.length; i++) {
                int[] t = targets[i];
                int max = -1;
                byte cc = empty;
                NEXT: for (byte c : order) {
                    if (colorCount[c] < t.length) continue;
                    for (int j = 0; j < i; j++) {
                        if (c == targetColors[j]) continue NEXT;
                    }
                    int curr = rnd.nextInt(2);
                    for (int p : t) {
                        if (g[p] == c) curr++;
                    }
                    if (curr > max) {
                        max = curr;
                        cc = c;
                    }
                }
                if (cc == empty) return null;
                targetColors[i] = cc;
                colorCount[cc] -= t.length;
            }
            Arrays.fill(targetGrid, empty);
            for (int i = 0; i < 3; i++) {
                byte c = targetColors[i];
                int[] t = targets[i];
                for (int p : t) {
                    targetGrid[p] = c;
                    colorSwaps[pos(g[p], c)]++;
                }
                maxLen += (t.length - 2) * (t.length - 2);
            }
            int maxMult = 2;
            int ymax = 1;
            byte c0 = targetColors[0];
            int aa = rnd.nextInt(Math.max(0, lastBestAdd - 1), lastBestAdd + 2);
            int add = 0;
            OUT: for (; add < aa; add++) {
                for (int i = 0; i < t0.length; i++) {
                    int p = t0[i];
                    int x = x(p);
                    int y = y(p);
                    t0[i] = pos(x, ++y);
                    if (x == 0 && y + 3 >= n) break OUT;
                    if (y == n) break OUT;
                }
                int max = -1;
                byte cc = empty;
                for (byte c : order) {
                    if (colorCount[c] < t0.length) continue;
                    if (c == targetColors[0]) continue;
                    if (add == aa && (c == targetColors[1] || c == targetColors[2])) continue;
                    if (add == aa - 1 && c == c0) continue;
                    int curr = 0;
                    for (int p : t0) {
                        byte gp = g[p];
                        if (gp == c) curr += 2;
                        else if (colorSwaps[pos(gp, c)] + 1 <= colorSwaps[pos(c, gp)]) curr++;
                    }
                    if (curr + 4 > max) {
                        curr += rnd.nextInt(5);
                        if (curr > max) {
                            max = curr;
                            cc = c;
                        }
                    }
                }
                if (cc == empty) break;
                targetColors[0] = cc;
                colorCount[cc] -= t0.length;
                for (int p : t0) {
                    targetGrid[p] = cc;
                    colorSwaps[pos(g[p], cc)]++;
                    if (x(p) == 0) ymax = y(p);
                }
                maxLen += (t0.length - 2) * (t0.length - 2);
                if (ending) {
                    int currCost = 0;
                    for (int i = 0; i < cs1.length; i++) {
                        currCost += Math.max(colorSwaps[cs1[i]], colorSwaps[cs2[i]]);
                    }
                    if (currCost + currMove + n / 2 + 3 > maxMoves) break;
                }
            }
            int[] t3 = new int[] {pos(0, 0),pos(0, ymax + 1),pos(0, ymax + 2)};
            int max = -1;
            byte cc = empty;
            for (byte c : order) {
                if (c == targetGrid[pos(0, ymax)]) continue;
                if (c == targetGrid[pos(0, 1)]) continue;
                if (colorCount[c] < t3.length) continue;
                int curr = 0;
                for (int p : t3) {
                    byte gp = g[p];
                    if (gp == c) curr += 2;
                    else if (colorSwaps[pos(gp, c)] + 1 <= colorSwaps[pos(c, gp)]) curr++;
                }
                if (curr + 2 > max) {
                    curr += rnd.nextInt(3);
                    if (curr > max) {
                        max = curr;
                        cc = c;
                    }
                }
            }
            if (cc != empty) {
                maxLen++;
                maxMult++;
                colorCount[cc] -= t3.length;
                for (int p : t3) {
                    targetGrid[p] = cc;
                    colorSwaps[pos(g[p], cc)]++;
                }
                int x0 = -1;
                int dx = 1;
                boolean[] finished = new boolean[numColors];
                for (byte c : order) {
                    if (colorCount[c] < t3.length) finished[c] = true;
                }
                boolean[] used = new boolean[numColors];
                int retry = 0;
                int chains = 0;
                byte prev = cc;
                OUT: while (++chains < limit) {
                    x0 += dx;
                    int k = 0;
                    for (int x = x0; x < x0 + t3.length; x++) {
                        if (x >= n || x < 0) {
                            dx = -dx;
                            x0 += dx;
                            continue OUT;
                        }
                        int y0 = 0;
                        int p = x;
                        if (targetGrid[p] == empty) {
                            if (targetGrid[p + 16] == empty) break OUT;
                        } else {
                            p += 16;
                            for (y0 = 2; y0 < n; y0++) {
                                if (targetGrid[p += 16] == empty) break;
                            }
                            if (y0 == n) {
                                if (++retry > 3) break OUT;
                                if (retry == 2) {
                                    dx = -dx;
                                    x0 += 2 * dx;
                                }
                                continue OUT;
                            }
                        }
                        t3[k++] = p;
                    }
                    System.arraycopy(finished, 0, used, 0, numColors);
                    used[prev] = true;
                    for (int pi : t3) {
                        int yi = y(pi);
                        if (yi == 0) {
                            int xi = x(pi);
                            if (xi == xx0) used[targetColors[1]] = true;
                            if (xi == xx1) used[targetColors[2]] = true;
                        }
                    }
                    max = -1;
                    cc = empty;
                    for (byte c : order) {
                        if (used[c]) continue;
                        int curr = 0;
                        for (int p : t3) {
                            byte gp = g[p];
                            if (gp == c) curr += 2;
                            else if (colorSwaps[pos(gp, c)] + 1 <= colorSwaps[pos(c, gp)]) curr++;
                        }
                        if (curr + 2 > max) {
                            curr += rnd.nextInt(3);
                            if (curr > max) {
                                for (int p : t3) {
                                    targetGrid[p] = c;
                                }
                                boolean ok = true;
                                for (int p : t3) {
                                    if (conn(targetGrid, c, x(p), y(p), p)) {
                                        ok = false;
                                        break;
                                    }
                                }
                                for (int p : t3) {
                                    targetGrid[p] = empty;
                                }
                                if (ok) {
                                    max = curr;
                                    cc = c;
                                }
                            }
                        }
                    }
                    if (cc == empty) break;
                    retry = 0;
                    if ((colorCount[prev = cc] -= t3.length) < t3.length) finished[cc] = true;
                    for (int p : t3) {
                        targetGrid[p] = cc;
                        colorSwaps[pos(g[p], cc)]++;
                    }
                    maxLen++;
                    maxMult++;
                    if (ending) {
                        int currCost = 0;
                        for (int i = 0; i < cs1.length; i++) {
                            currCost += Math.max(colorSwaps[cs1[i]], colorSwaps[cs2[i]]);
                        }
                        if (currCost + currMove + 2 > maxMoves) break;
                    }
                }
            }
            int currCost = 0;
            for (int i = 0; i < cs1.length; i++) {
                currCost += Math.max(colorSwaps[cs1[i]], colorSwaps[cs2[i]]);
            }
            if (currCost + currMove > maxMoves || currCost == 0) continue;
            if (maxLen * maxMult * 1000 / currCost > maxValue) {
                System.arraycopy(targetGrid, 0, auxGrid, 0, targetGrid.length);
                int p1 = p1(lastMove);
                int p2 = p2(lastMove);
                byte aux = auxGrid[p1];
                auxGrid[p1] = auxGrid[p2];
                auxGrid[p2] = aux;
                int currValue = eval(auxGrid, 0, n - 1, 0, n - 1, 0) * 1000 / currCost;
                if (currValue > maxValue) {
                    maxValue = currValue;
                    System.arraycopy(targetGrid, 0, bestTargetGrid, 0, g.length);
                    bestLastMove = lastMove;
                    currBestAdd = add;
                }
            }
        }
        if (maxValue == 0) return null;
        System.arraycopy(bestTargetGrid, 0, targetGrid, 0, g.length);
        int[] currMoves = place(bestLastMove);
        if (currMoves != null) currMoves[currMoves.length - 1] = bestLastMove;
        return currMoves;
    }

    private int[][] getTargets() {
        int[][][] opt = null;
        if (n == 8) opt = new int[][][] {{{16,20,34,35,65,37,71,38},{18,19,33,49,23},{17,21,39,55,22}},{{16,20,33,35,37,38,66,71},{17,19,23,34,50},{18,21,22,39,55}}};
        if (n == 9) opt = new int[][][] {{{16,20,34,35,65,38,72,39,21},{18,19,33,49,24},{17,22,40,56,23}}};
        if (n == 10) opt = new int[][][] {{{16,17,34,35,68,41,72,39,22,21},{18,19,36,52,24},{20,25,40,56,23}},{{16,17,34,35,68,40,73,39,21,22},{18,19,36,52,25},{20,24,41,57,23}},{{16,17,36,35,66,40,73,39,21,22},{20,19,34,50,25},{18,24,41,57,23}}};
        if (n == 11) opt = new int[][][] {{{16,17,34,35,68,21,73,39,40,22,26},{18,19,36,52,25},{20,41,57,23,24}},{{16,17,36,35,66,21,73,39,40,22,26},{20,19,34,50,25},{18,41,57,23,24}}};
        if (n == 12) opt = new int[][][] {{{16,20,21,26,27,34,35,38,39,41,65,72},{18,19,24,33,49},{17,22,23,25,40,56}}};
        if (n == 13) opt = new int[][][] {{{16,17,34,36,67,37,22,23,40,74,41,27,28},{18,20,35,51,21,26},{24,42,58,25,19}},{{16,17,35,36,66,39,22,27,40,73,42,21,28},{19,20,34,50,25},{23,24,41,57,26,18}},{{16,17,34,36,67,37,22,23,42,72,41,27,28},{18,20,35,51,21,24},{26,40,56,25,19}}};
        if (n == 14) opt = new int[][][] {{{16,17,21,22,28,29,34,36,39,40,42,43,67,73},{18,20,25,35,51},{19,23,24,26,27,41,57}}};
        if (n == 15) opt = new int[][][] {{{16,17,34,35,68,37,38,23,24,41,42,75,44,29,30},{18,19,36,52,21,22,27},{25,26,43,59,28,20}},{{16,17,22,23,29,30,34,36,37,40,41,43,44,67,74},{18,20,21,26,35,51},{19,24,25,27,28,42,58}},{{16,17,22,23,29,30,34,35,37,40,41,43,44,68,74},{18,19,21,26,36,52},{20,24,25,27,28,42,58}}};
        if (n == 16) opt = new int[][][] {{{16,17,34,35,68,37,38,23,24,41,42,75,44,45,30,31},{18,19,36,52,21,22,27},{25,26,43,59,28,29,20}}};
        if (opt == null) return null;
        if (opt.length == 1) return opt[0];
        return opt[rnd.nextInt(opt.length)];
    }

    private int[] place(int lastMove) {
        Arrays.fill(ni, 0);
        Arrays.fill(nj, 0);
        Arrays.fill(np, 0);
        int nt = 0;
        System.arraycopy(targetGrid, 0, auxGrid, 0, targetGrid.length);
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int i = pos(x, y);
                byte ti = targetGrid[i];
                if (ti != empty) {
                    int gi = g[i];
                    if (ti != gi) {
                        lt[nt++] = i;
                        li[gi][ni[gi]++] = i;
                    }
                } else {
                    auxGrid[i] = (byte) (restOffset + y);
                }
            }
        }
        Arrays.fill(rejectedColors, (short) 0);
        int p1 = p1(lastMove);
        int p2 = p2(lastMove);
        byte aux = auxGrid[p1];
        auxGrid[p1] = auxGrid[p2];
        auxGrid[p2] = aux;
        eval(auxGrid, 0, n - 1, 0, n - 1, 2);
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int i = pos(x, y);
                if (targetGrid[i] != empty) continue;
                byte gi = g[i];
                if (rejectedColors[i] != 0) lp[gi][np[gi]++] = i;
                else lj[gi][nj[gi]++] = i;
            }
        }
        shuffle(lt, nt);
        for (int c = 0; c < numColors; c++) {
            shuffle(li[c], ni[c]);
            shuffle(lj[c], nj[c]);
            shuffle(lp[c], np[c]);
        }
        int cnt = 0;
        while (nt > 0) {
            int bi = -1;
            int bj = -1;
            int bt = -1;
            int bjj = -1;
            int bk = -1;
            int max = 0;
            OUT: for (int ii = 0; ii < nt; ii++) {
                int i = lt[ii];
                byte gi = g[i];
                int ti = targetGrid[i];
                if (ti == gi) {
                    lt[ii--] = lt[--nt];
                    continue;
                }
                int xi = x(i);
                int yi = y(i);
                int mi = 1 << gi;
                for (int k = 0; k <= 2; k++) {
                    if (k == 1 && max >= 4) break;
                    if (k == 2 && max >= 3) break;
                    int[] ll = (k == 0 ? li : k == 1 ? lp : lj)[ti];
                    int nn = (k == 0 ? ni : k == 1 ? np : nj)[ti];
                    for (int jj = 0; jj < nn; jj++) {
                        int j = ll[jj];
                        byte gj = g[j];
                        if (k == 0 && gj == targetGrid[j]) continue;
                        int curr = k == 2 ? 3 : k == 1 ? ((rejectedColors[j] & mi) == 0 ? 4 : 1) : gi == targetGrid[j] ? 5 : 2;
                        if (curr <= max) continue;
                        g[i] = gj;
                        g[j] = gi;
                        boolean ok = !conn(g, gj, xi, yi, i) && !conn(g, gi, x(j), y(j), j);
                        g[i] = gi;
                        g[j] = gj;
                        if (ok) {
                            bi = i;
                            bt = ii;
                            bj = j;
                            bjj = jj;
                            bk = k;
                            max = curr;
                            if (max == 5) break OUT;
                            if (k == 2 && max >= 3) continue OUT;
                            if (k == 1 && max >= 4) continue OUT;
                        }
                    }
                }
            }
            if (nt == 0) break;
            if (bi == -1) return null;
            lt[bt] = lt[--nt];
            currPlaceMoves[cnt++] = toMove(bi, bj);
            byte gi = g[bi];
            byte gj = g[bj];
            int[] lii = li[gi];
            for (int i = ni[gi] - 1; i >= 0; i--) {
                if (lii[i] == bi) {
                    lii[i] = lii[--ni[gi]];
                    break;
                }
            }
            if (bk == 0) {
                lii = li[gj];
                lii[bjj] = lii[--ni[gj]];
                if (gi != targetGrid[bj]) li[gi][ni[gi]++] = bj;
            } else if (bk == 1) {
                int[] lpp = lp[gj];
                lpp[bjj] = lpp[--np[gj]];
                lp[gi][np[gi]++] = bj;
            } else if (bk == 2) {
                int[] ljj = lj[gj];
                ljj[bjj] = ljj[--nj[gj]];
                lj[gi][nj[gi]++] = bj;
            }
            g[bi] = gj;
            g[bj] = gi;
        }
        return Arrays.copyOf(currPlaceMoves, cnt + 1);
    }

    private void shuffle(int[] arr, int len) {
        for (int i = len - 1; i > 0; i--) {
            int p = rnd.nextInt(i + 1);
            int aux = arr[p];
            arr[p] = arr[i];
            arr[i] = aux;
        }
    }

    private boolean conn(byte[] g, byte c, int x, int y, int pos) {
        int a1 = x == 0 ? empty : g[pos - 1];
        int a2 = x == n - 1 ? empty : g[pos + 1];
        if (c == a1) {
            if (c == a2) return true;
            if (x > 1 && c == g[pos - 2]) return true;
        } else {
            if (c == a2 && x < n - 2 && c == g[pos + 2]) return true;
        }
        a1 = y == 0 ? empty : g[pos - 16];
        a2 = y == n - 1 ? empty : g[pos + 16];
        if (c == a1) {
            if (c == a2) return true;
            if (y > 1 && c == g[pos - 32]) return true;
        } else {
            if (c == a2 && y < n - 2 && c == g[pos + 32]) return true;
        }
        return false;
    }

    private int eval(byte[] grid, int xmin, int xmax, int ymin, int ymax, int mode) {
        int score = 0;
        int mult = 0;
        while (true) {
            if (mode == 2) {
                for (int x = 0; x < n; x++) {
                    int pos = pos(x, n);
                    for (int y = n - 1; y >= 0; y--) {
                        byte a = grid[pos -= 16];
                        if (a == empty) continue;
                        if (a < restOffset) break;
                        if (x >= 2 && grid[pos - 1] == grid[pos - 2] && grid[pos - 1] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos - 1];
                        if (x > 1 && x < n - 1 && grid[pos - 1] == grid[pos + 1] && grid[pos - 1] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos - 1];
                        if (x < n - 2 && grid[pos + 1] == grid[pos + 2] && grid[pos + 1] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos + 1];
                        if (y >= 2 && grid[pos - 16] == grid[pos - 32] && grid[pos - 16] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos - 16];
                        if (y < n - 2 && grid[pos + 16] == grid[pos + 32] && grid[pos + 16] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos + 16];
                        if (y > 1 && y < n - 1 && grid[pos - 16] == grid[pos + 16] && grid[pos - 16] != empty) rejectedColors[pos(x, a - restOffset)] |= 1 << grid[pos - 16];
                    }
                }
            }
            boolean done = true;
            int xmin0 = Math.max(xmin - 2, 0);
            int xmax0 = Math.min(xmax + 2, n - 1);
            int ymin0 = Math.max(ymin - 2, 0);
            int ymax0 = Math.min(ymax + 2, n - 1);
            int xminr = n - 1;
            int xmaxr = 0;
            for (int y = ymin; y <= ymax; y++) {
                int pos = pos(xmin0, y);
                byte a1 = grid[pos];
                byte a2 = grid[++pos];
                int l = 0;
                for (int x = xmin0 + 2; x <= xmax0; x++) {
                    byte a3 = grid[++pos];
                    if (a1 == a2 && a2 == a3 && a1 < empty) {
                        if (l++ == 0) {
                            grid[pos - 2] |= removeMask;
                            grid[pos - 1] |= removeMask;
                        }
                        grid[pos] |= removeMask;
                        if (x - 2 < xminr) xminr = x - 2;
                        if (x > xmaxr) xmaxr = x;
                    } else if (l > 0) {
                        score += l * l;
                        l = 0;
                        done = false;
                    }
                    a1 = a2;
                    a2 = a3;
                }
                if (l > 0) {
                    score += l * l;
                    done = false;
                }
            }
            for (int x = xmin; x <= xmax; x++) {
                int pos = pos(x, ymin0);
                byte a1 = (byte) (grid[pos] & colorMask);
                if (a1 >= empty) continue;
                byte a2 = (byte) (grid[pos += 16] & colorMask);
                if (a2 >= empty) continue;
                int l = 0;
                for (int y = ymin0 + 2; y <= ymax0; y++) {
                    byte a3 = (byte) (grid[pos += 16] & colorMask);
                    if (a3 >= empty) break;
                    if (a1 == a2 && a2 == a3) {
                        if (l++ == 0) {
                            grid[pos - 32] |= removeMask;
                            grid[pos - 16] |= removeMask;
                            if (x < xminr) xminr = x;
                            if (x > xmaxr) xmaxr = x;
                        }
                        grid[pos] |= removeMask;
                    } else if (l > 0) {
                        score += l * l;
                        l = 0;
                        done = false;
                    }
                    a1 = a2;
                    a2 = a3;
                }
                if (l > 0) {
                    score += l * l;
                    done = false;
                }
            }
            if (done) break;
            mult++;
            int xmin2 = n;
            int xmax2 = 0;
            int ymin2 = n;
            int ymax2 = 0;
            for (int x = xminr; x <= xmaxr; x++) {
                int pos = pos(x, ymin0);
                int y0 = ymin0;
                byte[] rpx = mode == 1 ? currRandomPieces[x] : null;
                for (int y = ymin0; y < n; y++, pos += 16) {
                    byte a = grid[pos];
                    if ((a & removeMask) == 0) {
                        if (y != y0) {
                            grid[pos(x, y0)] = a;
                            if (x < xmin2) xmin2 = x;
                            if (x > xmax2) xmax2 = x;
                            if (y0 < ymin2) ymin2 = y0;
                            if (y0 > ymax2) ymax2 = y0;
                        }
                        y0++;
                    }
                }
                for (int y = y0; y < n; y++) {
                    int p = pos(x, y);
                    if (mode == 1) {
                        int idx = randomPieceIdx[x]++;
                        byte v = rpx[idx];
                        if (v == empty) v = rpx[idx] = (byte) rnd.nextInt(numColors);
                        grid[p] = v;
                        if (x < xmin2) xmin2 = x;
                        if (x > xmax2) xmax2 = x;
                        if (y0 < ymin2) ymin2 = y;
                        if (y0 > ymax2) ymax2 = y;
                    } else {
                        if (grid[p] == empty) break;
                        grid[p] = empty;
                    }
                }
            }
            xmin = xmin2;
            xmax = xmax2;
            ymin = ymin2;
            ymax = ymax2;
        }
        return score * mult;
    }

    private static final String toString(int m) {
        int p1 = p1(m);
        int p2 = p2(m);
        return y(p1) + " " + x(p1) + " " + y(p2) + " " + x(p2);
    }

    private static final int x(int p) {
        return p & 15;
    }

    private static final int y(int p) {
        return p >>> 4;
    }

    private static final int pos(int x, int y) {
        return (y << 4) | x;
    }

    private static final int p1(int m) {
        return m >>> 8;
    }

    private static final int p2(int m) {
        return m & 255;
    }

    private final int mirrorMove(int m) {
        int p1 = p1(m);
        int p2 = p2(m);
        return toMove(pos(n - x(p1) - 1, y(p1)), pos(n - x(p2) - 1, y(p2)));
    }

    private static final int toMove(int p1, int p2) {
        if (p1 > p2) return toMove(p2, p1);
        return (p1 << 8) | p2;
    }

    public static void main(String[] args) {
        try {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            int n = Integer.parseInt(br.readLine());
            int numColors = Integer.parseInt(br.readLine());
            Jewels jewels = new Jewels(n, numColors);
            readGrid(br, jewels.currGrid, numColors, n);
            int runtime = 0;
            for (int i = 0; i < maxMoves; i++) {
                String move = jewels.run(runtime);
                System.out.println(move);
                System.out.flush();
                readGrid(br, jewels.currGrid, numColors, n);
                runtime = Integer.parseInt(br.readLine());
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    private static void readGrid(BufferedReader br, byte[] grid, int numColors, int n) throws IOException {
        int p = 0;
        for (int i = n * n; i > 0; i--) {
            String s = br.readLine();
            byte g = grid[p] = (byte) (s.charAt(s.length() - 1) - '0' - 1);
            if (g < 0) grid[p] = (byte) (numColors - 1);
            if ((p & 15) == n - 1) p = ((p >>> 4) + 1) << 4;
            else p++;
        }
    }
}