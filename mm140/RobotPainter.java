import java.io.*;
import java.util.*;

public class RobotPainter {
    private static final long t0 = System.currentTimeMillis();
    private static long timeout = t0 + 9600;
    private static final int[] dx = {1,1,0,-1,-1,-1,0,1}, dy = {0,1,1,1,0,-1,-1,-1}, da = {0,-1,1}, sub = new int[64];
    private static final DirToDir[] dirToDir = new DirToDir[9 << 3];
    private static final int[] commandMem = new int[1 << 26];
    private static PlaceToPlace[] placeToPlace;
    private static int[] grid, painted;
    private static int n, jumpCost, forCost, freeMem;
    private static Solution best, next, rep;
    private static final int cmdLeft = 1, cmdRight = 2, cmdUp = 3, cmdDown = 4, cmdForward = 5, cmdBackward = 6, cmdJump = 7, cmdFor = 8, cmdEnd = 9, cmdNull = 0;
    private static final SplittableRandom rnd = new SplittableRandom(9999);
    private static Beam[] states;

    public static void main(String[] args) throws Exception {
        init();
        System.err.println("INIT = " + (System.currentTimeMillis() - t0));
        int maxWidth = states[1].beamWidth;
        int width = 1;
        while (true) {
            long start = System.currentTimeMillis();
            if (start >= timeout) break;
            solve(width);
            long now = System.currentTimeMillis();
            long ellapsed = now - start;
            System.err.println(width + ":" + best.cost + ":" + ellapsed);
            if (width == maxWidth) break;
            if (now + ellapsed * 2 > timeout) width += Math.max(1, (int) ((timeout - now) * width / 2 / ellapsed));
            else width *= 2;
            if (width > maxWidth) width = maxWidth;
        }
        output(best);
    }

    private static void solve(int width) {
        for (int len = 0; len < states.length && System.currentTimeMillis() < timeout; len++) {
            Beam currStates = states[len];
            currStates.trim();
            for (int i = 0; i < width && i < currStates.size(); i++) {
                Solution curr = currStates.get(i);
                if (curr.expanded) continue;
                if (curr.cost + 1 >= best.cost) break;
                expand(curr);
                curr.expanded = true;
            }
        }
    }

    private static void expand(Solution curr) {
        for (int dd : da) {
            final int d1 = (curr.dir + dd + 8) & 7;
            final int vx1 = dx[d1];
            final int vy1 = dy[d1];
            final int d2 = (d1 + 4) & 7;
            final int vx2 = dx[d2];
            final int vy2 = dy[d2];
            for (int p : painted) {
                int px = p & 31;
                int py = p >>> 5;
                int nx = px;
                int ny = py;
                int len1 = 0;
                int k = 0;
                while (true) {
                    nx = range(nx + vx1);
                    ny = range(ny + vy1);
                    if (nx == px && ny == py) break;
                    int mask = 1 << nx;
                    if ((grid[ny] & mask) == 0) break;
                    k++;
                    if ((curr.board[ny] & mask) == 0) len1 = k;
                }
                if (len1 > 0 && k > len1 && rnd.nextBoolean()) len1 = k;
                int len2 = 0;
                if (k < n - 1) {
                    nx = px;
                    ny = py;
                    k = 0;
                    while (true) {
                        nx = range(nx + vx2);
                        ny = range(ny + vy2);
                        if (nx == px && ny == py) break;
                        int mask = 1 << nx;
                        if ((grid[ny] & mask) == 0) break;
                        k++;
                        if ((curr.board[ny] & mask) == 0) len2 = k;
                    }
                    if (len2 > 0 && k > len2 && rnd.nextBoolean()) len2 = k;
                }
                if (len1 == 0 && len2 == 0 && ((dd != 0 && n >= 10) || (curr.board[py] & (1 << px)) != 0)) continue;
                for (int turn = 0; turn < 2; turn++) {
                    if (turn == 1 && (len1 == 0 || len2 == 0)) break;
                    next.copyFrom(curr);
                    int l1 = len1;
                    int l2 = len2;
                    if (move(next, px, py, (l1 == 0 && l2 == 0) ? -1 : d1)) {
                        int aux = l1;
                        l1 = l2;
                        l2 = aux;
                    }
                    if (turn == 0) {
                        if (l1 > 0) next.add(cmdForward(l1));
                        if (l2 > 0) next.add(cmdBackward(l1 + l2));
                    } else {
                        if (l2 > 0) next.add(cmdBackward(l2));
                        if (l1 > 0) next.add(cmdForward(l1 + l2));
                    }
                    if (best.cost <= next.cost) continue;
                    next.parent = curr;
                    if (next.painted == painted.length) {
                        best = next;
                        next = new Solution();
                    } else {
                        Solution s = next;
                        if (next.painted > curr.painted && states[next.painted].add(next)) next = new Solution();
                        if (s.cost + forCost < best.cost) {
                            Solution parent = s.parent;
                            int subLen = s.numCommands;
                            if (parent.numCommands != 0) {
                                subLen += parent.numCommands;
                                System.arraycopy(commandMem, parent.offSet, sub, 0, parent.numCommands);
                                System.arraycopy(commandMem, s.offSet, sub, subLen - s.numCommands, s.numCommands);
                                parent = parent.parent;
                            } else {
                                System.arraycopy(commandMem, s.offSet, sub, 0, s.numCommands);
                            }
                            OUT: for (int i = subLen - 1; i >= 0; i--) {
                                rep.copyFrom(s);
                                rep.cost += forCost;
                                if (rep.cost >= best.cost) break;
                                int sc = s.cost;
                                for (int loop = 1; loop < 10; loop++) {
                                    int rp = rep.painted;
                                    for (int j = i; j < subLen; j++) {
                                        int cj = sub[j];
                                        if (cmdType(cj) == cmdFor) {
                                            int cnt = cmdFirstParam(cj);
                                            int end = -1;
                                            for (int l = j + 1; l < subLen; l++) {
                                                if (sub[l] == cmdEnd) {
                                                    end = l;
                                                    break;
                                                }
                                            }
                                            if (end == -1) continue OUT;
                                            sc += forCost;
                                            for (int m = 0; m < cnt; m++) {
                                                for (int l = j + 1; l < end; l++) {
                                                    int v = rep.apply(sub[l]);
                                                    if (v < 0) continue OUT;
                                                    if (m == 0) sc += v;
                                                }
                                            }
                                            j = end;
                                        } else {
                                            int v = rep.apply(sub[j]);
                                            if (v < 0) continue OUT;
                                            sc += v;
                                        }
                                    }
                                    rep.parent = null;
                                    if (rep.painted == painted.length || (rep.painted > rp && rep.cost < sc && states[rep.painted].add(rep))) {
                                        rep.alloc(subLen + 2);
                                        System.arraycopy(sub, 0, commandMem, rep.offSet, i);
                                        commandMem[rep.offSet + i] = cmdFor(loop + 1);
                                        System.arraycopy(sub, i, commandMem, rep.offSet + i + 1, subLen - i);
                                        commandMem[rep.offSet + subLen + 1] = cmdEnd;
                                        rep.parent = parent;
                                        if (rep.painted == painted.length) {
                                            best = rep;
                                            rep = new Solution();
                                            break;
                                        }
                                        Solution aux = new Solution();
                                        aux.copyFrom(rep);
                                        rep = aux;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    private static int cmdType(int cmd) {
        return cmd & 15;
    }

    private static int cmdFirstParam(int cmd) {
        return (cmd >>> 4) & 63;
    }

    private static int cmdSecondParam(int cmd) {
        return cmd >>> 10;
    }

    private static int cmdJump(int jx, int jy) {
        return cmdJump | ((jx + n) << 4) | ((jy + n) << 10);
    }

    private static int cmdFor(int loop) {
        return cmdFor | (loop << 4);
    }

    private static int cmdForward(int dist) {
        return cmdForward | (dist << 4);
    }

    private static int cmdBackward(int dist) {
        return cmdBackward | (dist << 4);
    }

    private static boolean move(Solution s, int tx, int ty, int tdir) {
        int sx = s.x;
        int sy = s.y;
        int sdir = s.dir;
        DirToDir d = dirToDir[((tdir + 1) << 3) | sdir];
        if (sx == tx && sy == ty) {
            if (!s.down) s.add(cmdDown);
            s.add(d.commands);
            return d.inv;
        }
        int minCost = jumpCost + d.cost;
        if (!s.down) minCost++;
        int key = (sy << 15) | (sx << 10) | (ty << 5) | tx;
        PlaceToPlace p = placeToPlace[key];
        DirToDir d1 = null;
        DirToDir d2 = null;
        if (p != null) {
            d1 = dirToDir[((p.dir + 1) << 3) | sdir];
            d2 = dirToDir[((tdir + 1) << 3) | d1.outDir];
            int currCost = d1.cost + d2.cost + 1;
            if (!p.continuos && s.down) currCost += 2;
            if (!s.down) currCost++;
            if (currCost < minCost) minCost = currCost;
            else p = null;
        }
        if (p != null) {
            s.add(d1.commands);
            if (s.down && !p.continuos) s.add(cmdUp);
            s.add(d1.inv ? cmdBackward(p.len) : cmdForward(p.len));
            s.add(d2.commands);
            if (!s.down) s.add(cmdDown);
            return d2.inv;
        }
        s.add(cmdJump(tx - sx, ty - sy));
        if (!s.down) s.add(cmdDown);
        s.add(d.commands);
        return d.inv;
    }

    private static int range(int v) {
        return v < 0 ? v + n : v >= n ? v - n : v;
    }

    private static void output(Solution s) {
        StringBuilder sb = new StringBuilder();
        int[] cmds = s.getCommands();
        int lines = 0;
        for (int i = 0; i < cmds.length; i++) {
            int c = cmds[i];
            int type = cmdType(c);
            int p1 = cmdFirstParam(c);
            int p2 = cmdSecondParam(c);
            if (i < cmds.length - 1 && (type == cmdBackward || type == cmdForward)) {
                int next = cmds[i + 1];
                if (type == cmdType(next)) {
                    int n1 = cmdFirstParam(next);
                    if (p1 + n1 < n) {
                        p1 += n1;
                        i++;
                    }
                }
            }
            switch (type) {
            case cmdLeft:
                sb.append('L');
                break;
            case cmdRight:
                sb.append('R');
                break;
            case cmdUp:
                sb.append('U');
                break;
            case cmdDown:
                sb.append('D');
                break;
            case cmdForward:
                sb.append('F').append(' ').append(p1);
                break;
            case cmdBackward:
                sb.append('B').append(' ').append(p1);
                break;
            case cmdJump:
                sb.append('J').append(' ').append(p2 - n).append(' ').append(p1 - n);
                break;
            case cmdFor:
                sb.append("FOR ").append(p1);
                break;
            case cmdEnd:
                sb.append("END");
                break;
            }
            sb.append('\n');
            lines++;
        }
        System.out.println(lines);
        System.out.print(sb.toString());
        System.out.flush();
    }

    private static void init() throws Exception {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        n = Integer.parseInt(in.readLine());
        jumpCost = Integer.parseInt(in.readLine());
        forCost = Integer.parseInt(in.readLine());
        grid = new int[n];
        painted = new int[n * n];
        int k = 0;
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                if (in.readLine().equals("#")) {
                    grid[y] |= 1 << x;
                    painted[k++] = (y << 5) | x;
                }
            }
        }
        in.close();
        next = new Solution();
        rep = new Solution();
        best = new Solution();
        best.cost = 9999;
        painted = Arrays.copyOf(painted, k);
        for (int a = 0; a < 8; a++) {
            DirToDir d = dirToDir[a] = new DirToDir();
            d.commands = new int[0];
            d.outDir = a;
            for (int mv = -1; mv <= 2; mv++) {
                for (int i = 0; i <= 4; i += 4) {
                    int b = (a + mv + i + 8) & 7;
                    d = dirToDir[((b + 1) << 3) | a] = new DirToDir();
                    d.outDir = (a + mv + 8) & 7;
                    if (mv == -1) d.commands = new int[] {cmdLeft};
                    else if (mv == 0) d.commands = new int[0];
                    else if (mv == 1) d.commands = new int[] {cmdRight};
                    else if (mv == 2) d.commands = new int[] {cmdRight,cmdRight};
                    d.cost = d.commands.length;
                    d.inv = i != 0;
                }
            }
        }
        placeToPlace = new PlaceToPlace[n << 15];
        for (int y0 = 0; y0 < n; y0++) {
            for (int x0 = 0; x0 < n; x0++) {
                boolean filled = (grid[y0] & (1 << x0)) != 0;
                if (!filled && (x0 != 0 || y0 != 0)) continue;
                int p0 = (y0 << 15) | (x0 << 10);
                for (int dir = 0; dir < 8; dir++) {
                    boolean cont = filled;
                    int vx = dx[dir];
                    int vy = dy[dir];
                    int x1 = x0;
                    int y1 = y0;
                    int len = 0;
                    while (true) {
                        x1 = range(x1 + vx);
                        y1 = range(y1 + vy);
                        if (x1 == x0 && y1 == y0) break;
                        len++;
                        if ((grid[y1] & (1 << x1)) == 0) cont = false;
                        else {
                            int idx1 = p0 | (y1 << 5) | x1;
                            PlaceToPlace prev = placeToPlace[idx1];
                            if (prev == null || (!prev.continuos && cont)) {
                                PlaceToPlace p = placeToPlace[idx1] = new PlaceToPlace();
                                p.continuos = cont;
                                p.dir = dir;
                                p.len = len;
                            }
                        }
                    }
                }
            }
        }
        states = new Beam[painted.length];
        int width = 15000000 / painted.length / n / n;
        for (int i = 0; i < painted.length; i++) {
            states[i] = new Beam(i == 0 ? 1 : width, i);
        }
        Solution root = new Solution();
        states[0].add(root);
    }

    private static class Solution {
        private int x, y, dir, cost, painted, numCommands, numJumps;
        private Solution parent;
        private boolean down, expanded;
        private final int[] board = new int[n];
        private int offSet;

        Solution() {
            offSet = freeMem;
            freeMem += 7;
        }

        void alloc(int newLen) {
            numCommands = newLen;
            offSet = freeMem;
            freeMem += numCommands;
        }

        int lastCmdType() {
            return numCommands == 0 ? cmdNull : cmdType(commandMem[offSet + numCommands - 1]);
        }

        int lastCmdFirstParam() {
            return numCommands == 0 ? cmdNull : cmdFirstParam(commandMem[offSet + numCommands - 1]);
        }

        int firstCmdType() {
            return numCommands == 0 ? cmdNull : cmdType(commandMem[offSet]);
        }

        int firstCmdFirstParam() {
            return numCommands == 0 ? cmdNull : cmdFirstParam(commandMem[offSet]);
        }

        void copyFrom(Solution s) {
            x = s.x;
            y = s.y;
            dir = s.dir;
            cost = s.cost;
            numJumps = s.numJumps;
            painted = s.painted;
            down = s.down;
            System.arraycopy(s.board, 0, board, 0, n);
            numCommands = 0;
        }

        int[] getCommands() {
            if (parent != null) {
                int[] ret = parent.getCommands();
                ret = Arrays.copyOf(ret, ret.length + numCommands);
                System.arraycopy(commandMem, offSet, ret, ret.length - numCommands, numCommands);
                return ret;
            }
            return new int[0];
        }

        void add(int c) {
            cost += apply(commandMem[offSet + numCommands++] = c);
            if (cmdType(c) == cmdJump) numJumps++;
        }

        int apply(int c) {
            int type = cmdType(c);
            switch (type) {
            case cmdJump:
                if (!update(cmdFirstParam(c) - n, cmdSecondParam(c) - n)) return -1;
                return jumpCost;
            case cmdRight:
                if (++dir == 8) dir = 0;
                return 1;
            case cmdLeft:
                if (--dir == -1) dir = 7;
                return 1;
            case cmdUp:
                down = false;
                return 1;
            case cmdDown:
                down = true;
                if (!update()) return -1;
                return 1;
            case cmdBackward:
                return move(-dx[dir], -dy[dir], cmdFirstParam(c));
            case cmdForward:
                return move(dx[dir], dy[dir], cmdFirstParam(c));
            }
            return -1;
        }

        private int move(int ax, int ay, int d) {
            if (!down) {
                x = range(x + ax * d);
                y = range(y + ay * d);
            } else {
                if (ay == 0) {
                    int by = board[y];
                    int gy = grid[y];
                    for (int i = d; i > 0; i--) {
                        int mask = 1 << (x = range(x + ax));
                        if ((by & mask) == 0) {
                            if ((gy & mask) == 0) return -1;
                            painted++;
                            by |= mask;
                        }
                        board[y] = by;
                    }
                } else if (ax == 0) {
                    int mask = 1 << x;
                    for (int i = d; i > 0; i--) {
                        if ((board[y = range(y + ay)] & mask) == 0) {
                            if ((grid[y] & mask) == 0) return -1;
                            painted++;
                            board[y] |= mask;
                        }
                    }
                } else {
                    for (int i = d; i > 0; i--) {
                        if (!update(ax, ay)) return -1;
                    }
                }
            }
            return 1;
        }

        void add(int[] cs) {
            for (int c : cs) {
                add(c);
            }
        }

        boolean update(int ax, int ay) {
            x = range(x + ax);
            y = range(y + ay);
            return down ? update() : true;
        }

        boolean update() {
            int mask = 1 << x;
            if ((board[y] & mask) == 0) {
                if ((grid[y] & mask) == 0) return false;
                painted++;
                board[y] |= mask;
            }
            return true;
        }

        void pack() {
            int c = firstCmdType();
            if ((c == cmdForward || c == cmdBackward) && c == parent.lastCmdType()) {
                int sum = firstCmdFirstParam() + parent.lastCmdFirstParam();
                if (sum < n) {
                    commandMem[offSet] = c == cmdForward ? cmdForward(sum) : cmdBackward(sum);
                    Solution np = new Solution();
                    np.copyFrom(parent);
                    np.parent = parent.parent;
                    np.numCommands = parent.numCommands - 1;
                    System.arraycopy(commandMem, parent.offSet, commandMem, np.offSet, np.numCommands);
                    cost--;
                    parent = np;
                }
            }
            for (int i = 1; i < numCommands; i++) {
                int a = commandMem[offSet + i - 1];
                int at = cmdType(a);
                if (at != cmdForward && at != cmdBackward) continue;
                int b = commandMem[offSet + i];
                int bt = cmdType(b);
                if (bt != at) continue;
                int sum = cmdFirstParam(a) + cmdFirstParam(b);
                if (sum < n) {
                    commandMem[offSet + i - 1] = at == cmdForward ? cmdForward(sum) : cmdBackward(sum);
                    numCommands--;
                    for (int j = i; j < numCommands; j++) {
                        commandMem[offSet + j] = commandMem[offSet + j + 1];
                    }
                    cost--;
                    i--;
                }
            }
        }
    }

    private static class DirToDir {
        int cost, outDir;
        boolean inv;
        int[] commands;
    }

    private static class PlaceToPlace {
        int len, dir;
        boolean continuos;
    }

    private static class Beam {
        private static final Solution[] aux = new Solution[65536];
        private static final EqComp eqComp = new EqComp();
        private static final EqComp costComp = new CostComp();
        private static final int alfa = 3;
        private final int beamWidth;
        private final Solution[] items;
        private final Solution cut = new Solution();
        private int size;

        Beam(int beamWidth, int numPainted) {
            this.beamWidth = Math.min(aux.length / alfa, beamWidth);
            items = new Solution[this.beamWidth * alfa];
            cut.cost = jumpCost * numPainted + 1;
            cut.numJumps = numPainted;
        }

        boolean add(Solution s) {
            if (size == items.length) trim();
            s.cost--;
            if (costComp.compare(s, cut) >= 0) {
                s.cost++;
                return false;
            }
            s.cost++;
            s.pack();
            if (costComp.compare(s, cut) >= 0) return false;
            items[size++] = s;
            return true;
        }

        void trim() {
            if (size == 0) return;
            Arrays.sort(items, 0, size, eqComp);
            System.arraycopy(items, 0, aux, 0, size);
            Solution a = aux[0];
            int pos = 0;
            for (int i = 1; i < size; i++) {
                Solution b = aux[i];
                if (eqComp.compare(a, b) == 0) {
                    if (costComp.compare(a, b) > 0) a = items[pos] = b;
                } else {
                    a = items[++pos] = b;
                }
            }
            size = pos + 1;
            Arrays.sort(items, 0, size, costComp);
            if (size > beamWidth) size = beamWidth;
            Solution last = items[size - 1];
            cut.cost = last.cost;
            cut.numJumps = last.numJumps;
        }

        int size() {
            return Math.min(beamWidth, size);
        }

        Solution get(int i) {
            return items[i];
        }
    }

    private static class CostComp extends EqComp {
        public int compare(Solution a, Solution b) {
            int cmp = Integer.compare(a.cost, b.cost);
            if (cmp != 0) return cmp;
            if ((cmp = Integer.compare(a.numJumps, b.numJumps)) != 0) return cmp;
            return super.compare(a, b);
        }
    }

    private static class EqComp implements Comparator<Solution> {
        public int compare(Solution a, Solution b) {
            int cmp = Integer.compare(a.x, b.x);
            if (cmp != 0) return cmp;
            if ((cmp = Integer.compare(a.y, b.y)) != 0) return cmp;
            if ((cmp = Integer.compare(a.dir, b.dir)) != 0) return cmp;
            for (int i = 0; i < n; i++) {
                if ((cmp = Integer.compare(a.board[i], b.board[i])) != 0) return cmp;
            }
            return 0;
        }
    }
}
