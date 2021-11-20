import java.io.*;
import java.util.*;

public class CoinCollector {
    private static int n, numDice, numRemainingCoins, numCollectedCoins, currPos, currScore, mult, maxDepth, spikeDiv, turnsRemaining, coinValue;
    private static int[] dice, gc, move, area;
    private static byte[] grid;
    private static int[] safe;
    private static String[] diceStr;
    private static int[][] memo;
    private static BufferedReader in;
    private static final int[] DX = {-1,0,1,0}, DY = {0,-1,0,1};
    private static final char[] DIRS = {'L','U','R','D'};
    private static final byte EMPTY = 0, COIN = 1, SPIKE = 2, REMOVED_COIN = 3;
    private static final int LOW = -1, ODD = -2, EVEN = -3, HIGH = -4, RANDOM = -6, NONE = -100;
    private static final int TIMEOUT = 8000;
    private static final int[] OPTIONS = {0,1,2,3,4,5,6,ODD,EVEN,LOW,HIGH,RANDOM};
    private static final int[] OPTIONS_WEIGHT = {1,1,1,1,1,1,1,3,3,3,3,6};
    private static final int[][] DISTS = new int[-RANDOM + 1][];

    public static void main(String[] args) throws Exception {
        init();
        solve();
    }

    private static void solve() throws Exception {
        turnsRemaining = n * n;
        while (turnsRemaining > 0 && numRemainingCoins > 0) {
            int[] play = play();
            int diceIdx = play[0];
            if (diceIdx == -1) break;
            int dir = play[1];
            System.out.println(DIRS[dir]);
            System.out.println(diceStr[diceIdx]);
            System.out.flush();
            int time = Integer.parseInt(in.readLine());
            if (time > TIMEOUT && maxDepth > 2) maxDepth = 2;
            int diceValue = Integer.parseInt(in.readLine());
            String s = diceStr[diceIdx] = in.readLine();
            dice[diceIdx] = toDie(s);
            currPos = move(currPos, dir, diceValue);
            gc[currPos]++;
            byte land = grid[currPos];
            if (land == COIN) {
                grid[currPos] = EMPTY;
                currScore += coinValue;
                numRemainingCoins--;
                numCollectedCoins++;
            } else if (land == SPIKE) {
                currScore /= 2;
            }
            turnsRemaining--;
        }
        System.out.println("X");
        System.out.flush();
        in.close();
    }

    private static int[] play() {
        if (grid[currPos] != SPIKE || currScore == 0) {
            for (int i = 0; i < numDice; i++) {
                if (dice[i] == 0) return new int[] {i,0};
            }
        }
        if (memo != null) Arrays.fill(memo, null);
        if (n * n - turnsRemaining > n * 2) {
            int expCoins = numCollectedCoins * turnsRemaining / (n * n - turnsRemaining);
            Arrays.fill(area, 0);
            if (expCoins < numRemainingCoins) {
                for (int pos = 0; pos < area.length; pos++) {
                    if (grid[pos] == SPIKE) continue;
                    for (int dir = 0; dir < 4; dir++) {
                        for (int dist = 1; dist <= 6; dist++) {
                            int newPos = move(pos, dir, dist);
                            if (grid[newPos] == COIN) area[pos]++;
                        }
                    }
                }
            }
        }
        return play(currScore, currPos, 0, new int[0]);
    }

    private static int playNext(int score, int pos, int depth, int idx, int[] mv) {
        int ret = 0;
        int save = dice[idx];
        if (depth == 1 && numDice == 2) {
            int tot = 0;
            for (int i = 0; i < OPTIONS.length; i++) {
                dice[idx] = OPTIONS[i];
                int w = OPTIONS_WEIGHT[i];
                tot += w;
                ret += w * play(score, pos, depth, mv)[2];
            }
            ret /= tot;
        } else {
            dice[idx] = NONE;
            ret = play(score, pos, depth, mv)[2];
        }
        dice[idx] = save;
        return ret;
    }

    private static int[] play(int score, int pos, int depth, int[] mv) {
        int key = -1;
        if (mv != null && mv.length == 4 && memo != null && grid[mv[0]] == EMPTY) {
            key = Math.min(mv[1], mv[3]) | ((Math.max(mv[1], mv[3])) << 3) | (mv[2] << 6);
            int[] ret = memo[key];
            if (ret != null) return ret;
        }
        int bestIdx = -1;
        int bestDir = -1;
        int maxVal = Integer.MIN_VALUE;
        NEXT: for (int i = 0; i < numDice; i++) {
            int die = dice[i];
            if (die == NONE) continue;
            int bonus = 0;
            int penalty = 0;
            for (int j = 0; j < numDice; j++) {
                if (i == j) continue;
                int other = dice[j];
                if (other == die) {
                    if (j < i) continue NEXT;
                    bonus += mult;
                }
                if (other == RANDOM) penalty += 4;
                else if (other == EVEN || other == ODD || other == LOW || other == HIGH) penalty += 1;
            }
            for (int dir = 0; dir < 4; dir++) {
                if (die == 0 && dir != 0) continue;
                int currVal = score;
                if (depth <= 1) currVal -= 11 * die;
                if (die >= 0) {
                    int newPos = move(pos, dir, die);
                    byte land = grid[newPos];
                    if (land == COIN) {
                        grid[newPos] = REMOVED_COIN;
                        currVal += coinValue;
                    } else if (land == SPIKE) currVal /= spikeDiv;
                    if (depth < maxDepth && (land != SPIKE || score < coinValue)) {
                        int[] mvn = null;
                        if (mv != null) {
                            mvn = Arrays.copyOf(mv, mv.length + 2);
                            mvn[mvn.length - 2] = newPos;
                            mvn[mvn.length - 1] = die;
                        }
                        currVal += (playNext(currVal, newPos, depth + 1, i, mvn) - currVal) / 2;
                    }
                    currVal += area[newPos];
                    currVal += safe[newPos];
                    if (depth <= 1) currVal -= gc[newPos];
                    if (land == COIN) grid[newPos] = COIN;
                } else {
                    int[] d = DISTS[-die];
                    int totVal = 0;
                    for (int dist : d) {
                        int v = currVal;
                        int newPos = move(pos, dir, dist);
                        byte land = grid[newPos];
                        if (land == COIN) {
                            grid[newPos] = REMOVED_COIN;
                            v += coinValue;
                        } else if (land == SPIKE) v /= spikeDiv;
                        if (depth < maxDepth && (land != SPIKE || score < coinValue)) {
                            v += (playNext(v, newPos, depth + 1, i, null) - v) / 2;
                        }
                        v += safe[newPos];
                        v += area[newPos];
                        if (depth <= 1) v -= gc[newPos];
                        totVal += v;
                        if (land == COIN) grid[newPos] = COIN;
                    }
                    currVal = totVal / d.length;
                }
                if (depth == 0) currVal += bonus;
                currVal -= penalty;
                if (currVal > maxVal) {
                    maxVal = currVal;
                    bestIdx = i;
                    bestDir = dir;
                }
            }
        }
        if (depth == 0 && numCollectedCoins > numRemainingCoins) {
            double f = maxVal * (numDice == 2 ? 0.95 : 1.0) / numCollectedCoins;
            int expCoins = Math.min(numRemainingCoins, numCollectedCoins * (turnsRemaining - 1) / (n * n - turnsRemaining + 1));
            int exp = (int) (maxVal + f * expCoins);
            if (exp <= score) bestIdx = -1;
        }
        int[] ret = new int[] {bestIdx,bestDir,maxVal};
        if (key != -1) memo[key] = ret;
        return ret;
    }

    private static int move(int p, int dir, int dist) {
        return move[(p << 5) | (dir << 3) | dist];
    }

    private static void init() throws Exception {
        in = new BufferedReader(new InputStreamReader(System.in));
        n = Integer.parseInt(in.readLine());
        numDice = Integer.parseInt(in.readLine());
        int py = Integer.parseInt(in.readLine());
        int px = Integer.parseInt(in.readLine());
        currPos = pos(px, py);
        dice = new int[numDice];
        diceStr = new String[numDice];
        for (int i = 0; i < numDice; i++) {
            String s = diceStr[i] = in.readLine();
            dice[i] = toDie(s);
        }
        grid = new byte[n * n];
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                char c = in.readLine().charAt(0);
                byte a = grid[pos(x, y)] = c == '.' ? EMPTY : c == 'C' ? COIN : SPIKE;
                if (a == COIN) numRemainingCoins++;
            }
        }
        coinValue = new int[] {0,0,200,140,200,90,110}[numDice];
        gc = new int[n * n];
        DISTS[-ODD] = new int[] {1,3,5};
        DISTS[-EVEN] = new int[] {2,4,6};
        DISTS[-LOW] = new int[] {1,2,3};
        DISTS[-HIGH] = new int[] {4,5,6};
        DISTS[-RANDOM] = new int[] {1,2,3,4,5,6};
        mult = numDice <= 3 ? 50 : 30;
        move = new int[(n * n) << 5];
        for (int p = 0; p < grid.length; p++) {
            for (int dir = 0; dir < 4; dir++) {
                for (int dist = 0; dist <= 6; dist++) {
                    int x = x(p) + DX[dir] * dist;
                    int y = y(p) + DY[dir] * dist;
                    if (x < 0) x += n;
                    else if (x >= n) x -= n;
                    if (y < 0) y += n;
                    else if (y >= n) y -= n;
                    move[(p << 5) | (dir << 3) | dist] = pos(x, y);
                }
            }
        }
        if (numDice > 2) memo = new int[grid.length << 6][];
        area = new int[n * n];
        safe = new int[n * n];
        for (int pos = 0; pos < safe.length; pos++) {
            int k = 0;
            for (int dir = 0; dir < 4; dir++) {
                boolean ok = true;
                for (int dist = 1; dist <= 6; dist++) {
                    int newPos = move(pos, dir, dist);
                    if (grid[newPos] == SPIKE) {
                        ok = false;
                        break;
                    }
                }
                if (ok) k++;
            }
            safe[pos] = k == 0 ? 0 : k + (numDice == 2 ? 16 : numDice == 3 ? 4 : 5);
        }
        spikeDiv = numDice <= 3 ? 10 : 4;
        maxDepth = numDice <= 3 ? 2 : 3;
    }

    private static int pos(int x, int y) {
        return y * n + x;
    }

    private static int x(int p) {
        return p % n;
    }

    private static int y(int p) {
        return p / n;
    }

    private static int toDie(String s) {
        if (s.equals("STAY")) return 0;
        if (s.equals("ONE")) return 1;
        if (s.equals("TWO")) return 2;
        if (s.equals("THREE")) return 3;
        if (s.equals("FOUR")) return 4;
        if (s.equals("FIVE")) return 5;
        if (s.equals("SIX")) return 6;
        if (s.equals("ODD")) return ODD;
        if (s.equals("EVEN")) return EVEN;
        if (s.equals("LOW")) return LOW;
        if (s.equals("HIGH")) return HIGH;
        if (s.equals("RANDOM")) return RANDOM;
        System.err.println("UNKNOWN:" + s);
        return 0;
    }
}
