import java.io.*;
import java.util.*;

public class Lines {
    private final int[] queue, gridHoriz, remHorizVal, remHorizIdxs, gridVert, remVertVal, remVertIdxs, gridDiag1, remDiag1Val, remDiag1Idxs, gridDiag2, remDiag2Val, remDiag2Idxs, countSeq, grid, nextBalls, offsets, savedGrid1, savedGrid2, toRem, memo;//, dest;
    private final int[][] neighborsHoriz, neighborsVert, neighborsDiag1, neighborsDiag2;
    private final int[][] seen;
    private final boolean[] reach;
    private final int n, n2, c, nn;
    private static final int delta = 2, len = 5;
    private int[] w;
    private int w1, w2, w3, w4, w5, w6, w7, remHorizIdxCnt, remVertIdxCnt, remDiag1IdxCnt, remDiag2IdxCnt, filled, evalSeq0, evalSeq1, evalSeq2, evalSeq3, evalSeq4, width1, width2, turn;
    private long runtime;

    private Lines(int n, int c) {
        this.n = n;
        this.c = c;
        n2 = n * 2;
        nn = n * n;
        countSeq = new int[c + 1];
        nextBalls = new int[3];
        grid = new int[nn];
        toRem = new int[nn];
        seen = new int[256][nn];
        savedGrid1 = new int[nn];
        savedGrid2 = new int[nn];
        reach = new boolean[nn];
        queue = new int[nn];
        gridHoriz = new int[nn];
        gridVert = new int[nn];
        gridDiag1 = new int[nn];
        gridDiag2 = new int[nn];
        remHorizVal = new int[nn];
        remVertVal = new int[nn];
        remDiag1Val = new int[nn];
        remDiag2Val = new int[nn];
        Arrays.fill(remHorizVal, Integer.MIN_VALUE);
        Arrays.fill(remVertVal, Integer.MIN_VALUE);
        Arrays.fill(remDiag1Val, Integer.MIN_VALUE);
        Arrays.fill(remDiag2Val, Integer.MIN_VALUE);
        remHorizIdxs = new int[nn];
        remVertIdxs = new int[nn];
        remDiag1Idxs = new int[nn];
        remDiag2Idxs = new int[nn];
        neighborsHoriz = new int[nn][];
        neighborsVert = new int[nn][];
        neighborsDiag1 = new int[nn][];
        neighborsDiag2 = new int[nn][];
        int[] aux = new int[nn];
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int p = y * n + x;
                int cnt = 0;
                for (int d = -delta; d <= delta; d++) {
                    int nx = x;
                    int ny = y + d;
                    if (ny - delta < 0 || ny + delta >= n) continue;
                    aux[cnt++] = ny * n + nx;
                }
                neighborsVert[p] = Arrays.copyOf(aux, cnt);
                cnt = 0;
                for (int d = -delta; d <= delta; d++) {
                    int nx = x + d;
                    int ny = y;
                    if (nx - delta < 0 || nx + delta >= n) continue;
                    aux[cnt++] = ny * n + nx;
                }
                neighborsHoriz[p] = Arrays.copyOf(aux, cnt);
                cnt = 0;
                for (int d = -delta; d <= delta; d++) {
                    int nx = x + d;
                    int ny = y + d;
                    if (nx - delta < 0 || nx + delta >= n || ny - delta < 0 || ny + delta >= n) continue;
                    aux[cnt++] = ny * n + nx;
                }
                neighborsDiag1[p] = Arrays.copyOf(aux, cnt);
                cnt = 0;
                for (int d = -delta; d <= delta; d++) {
                    int nx = x + d;
                    int ny = y - d;
                    if (nx - delta < 0 || nx + delta >= n || ny - delta < 0 || ny + delta >= n) continue;
                    aux[cnt++] = ny * n + nx;
                }
                neighborsDiag2[p] = Arrays.copyOf(aux, cnt);
            }
        }
        offsets = new int[(len + 1) << 6];
        Arrays.fill(offsets, -1);
        offsets[encode(5, 0, 0)] = 0;
        offsets[encode(4, 1, 1)] = 1;
        offsets[encode(3, 1, 1)] = 2;
        offsets[encode(3, 2, 1)] = 3;
        offsets[encode(3, 2, 2)] = 4;
        offsets[encode(2, 1, 1)] = 5;
        offsets[encode(2, 2, 1)] = 6;
        offsets[encode(2, 2, 2)] = 7;
        offsets[encode(2, 3, 1)] = 8;
        offsets[encode(2, 3, 2)] = 9;
        offsets[encode(2, 3, 3)] = 10;
        offsets[encode(1, 1, 1)] = 11;
        offsets[encode(1, 2, 1)] = 12;
        offsets[encode(1, 2, 2)] = 13;
        offsets[encode(1, 3, 1)] = 14;
        offsets[encode(1, 3, 2)] = 15;
        offsets[encode(1, 3, 3)] = 16;
        offsets[encode(1, 4, 2)] = 17;
        offsets[encode(1, 4, 3)] = 18;
        offsets[encode(1, 4, 4)] = 19;
        offsets[encode(0, 5, 5)] = 20;
        offsets[encode(0, 4, 2)] = 21;
        offsets[encode(0, 4, 3)] = 22;
        offsets[encode(0, 4, 4)] = 23;
        offsets[encode(0, 3, 1)] = 24;
        offsets[encode(0, 3, 2)] = 25;
        offsets[encode(0, 3, 3)] = 26;
        offsets[encode(0, 2, 1)] = 27;
        offsets[encode(0, 2, 2)] = 28;
        offsets[encode(0, 1, 1)] = 29;
        memo = new int[(c + 1) << 20];
        Arrays.fill(memo, Integer.MIN_VALUE);
        if (c == 3) {
            if (n == 7) {
                width1 = 10;
                width2 = 2;
            } else if (n == 8) {
                width1 = 8;
                width2 = 2;
            } else if (n == 9) {
                width1 = 6;
                width2 = 2;
            } else if (n == 10) {
                width1 = 3;
                width2 = 1;
            } else if (n == 11) {
                width1 = 3;
                width2 = 1;
            }
        } else if (c == 4) {
            if (n == 7) {
                width1 = 20;
                width2 = 2;
            } else if (n == 8) {
                width1 = 10;
                width2 = 2;
            } else if (n == 9) {
                width1 = 8;
                width2 = 1;
            } else if (n == 10) {
                width1 = 3;
                width2 = 1;
            } else if (n == 11) {
                width1 = 2;
                width2 = 1;
            }
        } else if (c == 5) {
            if (n == 7) {
                width1 = 60;
                width2 = 4;
            } else if (n == 8) {
                width1 = 10;
                width2 = 1;
            } else if (n == 9) {
                width1 = 6;
                width2 = 1;
            } else if (n == 10) {
                width1 = 3;
                width2 = 1;
            } else if (n == 11) {
                width1 = 2;
                width2 = 1;
            }
        } else if (c == 6) {
            if (n == 7) {
                width1 = 80;
                width2 = 8;
            } else if (n == 8) {
                width1 = 20;
                width2 = 4;
            } else if (n == 9) {
                width1 = 16;
                width2 = 1;
            } else if (n == 10) {
                width1 = 3;
                width2 = 1;
            } else if (n == 11) {
                width1 = 2;
                width2 = 1;
            }
        } else if (c == 7) {
            if (n == 7) {
                width1 = 80;
                width2 = 8;
            } else if (n == 8) {
                width1 = 20;
                width2 = 8;
            } else if (n == 9) {
                width1 = 20;
                width2 = 1;
            } else if (n == 10) {
                width1 = 8;
                width2 = 1;
            } else if (n == 11) {
                width1 = 5;
                width2 = 1;
            }
        } else if (c == 8) {
            if (n == 7) {
                width1 = 80;
                width2 = 16;
            } else if (n == 8) {
                width1 = 80;
                width2 = 2;
            } else if (n == 9) {
                width1 = 40;
                width2 = 1;
            } else if (n == 10) {
                width1 = 20;
                width2 = 1;
            } else if (n == 11) {
                width1 = 6;
                width2 = 1;
            }
        } else if (c == 9) {
            if (n == 7) {
                width1 = 80;
                width2 = 2;
            } else if (n == 8) {
                width1 = 80;
                width2 = 2;
            } else if (n == 9) {
                width1 = 40;
                width2 = 1;
            } else if (n == 10) {
                width1 = 20;
                width2 = 1;
            } else if (n == 11) {
                width1 = 10;
                width2 = 1;
            }
        }
        if (c == 3 && n == 7) w = new int[] {7,-1,-21,0,41,-39,-29,-50,-18,544,722,-14,-30,-48,-161,-46,-24,-18,2017,2426,15425,6,-53,321,-1,-28,22,-28,0,847,14,-1,-15,20,62,23,20,-8,841,462,601,-21,-4,-55,23,-58,152,310,3425,2706,16661,-26,-21,28,-43,-37,26,-55,123,735,10,10000,1000,50,10,50,20};
        if (c == 4 && n == 7) w = new int[] {10,-1,-23,3,125,-56,-94,-81,-17,1532,2028,-24,-146,-59,-149,-57,-21,-21,5645,6787,25098,18,-119,907,-1,-76,54,-26,0,2377,17,-3,-21,25,334,60,25,-9,2361,1305,1691,-24,-1,-138,72,-72,435,875,9582,7573,27106,-34,-24,60,-24,-23,114,-141,187,2064,10,10000,1000,50,10,50,20};
        if (c == 5 && n == 7) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 6 && n == 7) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 7 && n == 7) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 8 && n == 7) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 9 && n == 7) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 3 && n == 8) w = new int[] {7,-1,-21,0,41,-39,-29,-52,-18,544,722,-14,-30,-48,-118,-46,-24,-18,2017,2426,15425,6,-56,321,-1,-24,22,-28,0,847,14,-1,-15,20,62,11,20,-8,841,462,601,-21,-4,-38,23,-40,152,310,3425,2706,16661,-26,-21,28,-30,-37,26,-38,123,735,30,10000,1000,50,10,50,20};
        if (c == 4 && n == 8) w = new int[] {7,-1,-21,0,41,-39,-29,-50,-18,544,722,-14,-30,-48,-161,-46,-24,-18,2017,2426,15425,6,-53,321,-1,-28,22,-28,0,847,14,-1,-15,20,62,23,20,-8,841,462,601,-21,-4,-55,23,-58,152,310,3425,2706,16661,-26,-21,28,-43,-37,26,-55,123,735,10,10000,1000,50,10,50,20};
        if (c == 5 && n == 8) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 6 && n == 8) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 7 && n == 8) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 8 && n == 8) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 9 && n == 8) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 3 && n == 9) w = new int[] {14,-68,-212,20,5468,-363,-5065,33,25,1293272,1252821,-1248,-6372,-1579,-8033,-1790,-698,-1,1460072,1974196,2710498,-100,-1487,6600,-1,-1281,1739,21,-1,2806159,12211,-1,-671,1327,25740,1869,572,-1,1460072,311531,1317819,-237,24,-670,2375,-437,19560,829190,2225315,1860167,2926391,101,-2634,6433,-2312,-6127,6601,-2445,21067,1286405,128,10000,4013,50,10,115,20};
        if (c == 4 && n == 9) w = new int[] {7,-1,-21,0,41,-39,-29,-50,-18,544,722,-14,-30,-48,-161,-46,-24,-18,2017,2426,15425,6,-53,321,-1,-28,22,-28,0,847,14,-1,-15,20,62,23,20,-8,841,462,601,-21,-4,-55,23,-58,152,310,3425,2706,16661,-26,-21,28,-43,-37,26,-55,123,735,10,10000,1000,50,10,50,20};
        if (c == 5 && n == 9) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 6 && n == 9) w = new int[] {1,1,1,1,18,-18,-12,1,2,523,743,2,2,-22,-2,1,1,1,3385,3951,17502,12,-1,136,2,-6,1,1,1,135,15,5,1,15,13,13,1,2,353,28,492,2,1,-76,1,1,13,136,7221,4626,17502,1,1,1,1,1,1,-22,12,73,15,10000,1000,50,10,50,20};
        if (c == 7 && n == 9) w = new int[] {-1,-1,-1,-1,3,-1,-1,3,0,979,1145,-1,-1,-1,-1,1,1,-1,8548,14193,37233,-1,3,-2,-94,-1,3,-1,-1,-1,0,-1,-1,-1,3,0,3,-1,1415,1123,1037,-1,-8,-4,-1,-4,1,61,27483,10829,45873,-1,-1,-1,0,-1,-1,-1,-52,-1,40,10000,1000,50,-34,50,33};
        if (c == 8 && n == 9) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 9 && n == 9) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 3 && n == 10) w = new int[] {31,81,85,1736,-4152,1215,4714,70,-56,700183,121404,-693,-2203,-23652,-2486,-651,17,-335,2384215,-29860,2307270,-106,-65215,629073,-1640,17416,-8,3787,-236,1403801,2353,2517,-541,4591,169114,-28656,-2048,-2088,223457,120439,-282334,-237,-513,-270,49989,-8281,-11419,11962,2648211,319722,2926391,220,-112076,411,1018,15,-265,-490587,-4453,1286405,-620,131237,-191,127,-216,97,259};
        if (c == 4 && n == 10) w = new int[] {-1,-1,-1,-1,3,-1,-1,3,-1,979,1145,-1,-1,-1,-1,-1,1,-1,8548,8548,37233,-1,3,-1,-1,-1,3,-1,-1,-1,-1,-1,-1,-1,3,3,3,-1,1415,1123,1037,-1,-1,-4,1,-1,-1,61,27483,10829,45873,-1,-1,-1,0,0,-1,-1,3,-1,40,10000,1000,50,10,50,20};
        if (c == 5 && n == 10) w = new int[] {-1,-1,-1,-1,3,-1,-1,3,-1,979,1145,-1,-1,-1,-1,-1,1,-1,8548,8548,37233,-1,3,-1,-1,-1,3,-1,-1,-1,-1,-1,-1,-1,3,3,3,-1,1415,1123,1037,-1,-1,-4,1,-1,-1,61,27483,10829,45873,-1,-1,-1,0,0,-1,-1,3,-1,40,10000,1000,50,10,50,20};
        if (c == 6 && n == 10) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 7 && n == 10) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        if (c == 8 && n == 10) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 9 && n == 10) w = new int[] {0,-1,-1,-1,467,-2,-1,-1,-1,5321,6625,-1,-2,2,-2,-1,-1,-1,18966,18685,146130,-1,8,5584,-2,-5,381,-4,0,382,-2,0,-2,-1,0,0,-1,-1,6170,6488,1474,1,0,2,-1,-1,0,0,29659,23792,146128,-1,-1,-1,-1,-1,-1,0,-2,-4,60,10000,1000,34,10,50,20};
        if (c == 3 && n == 11) w = new int[] {-133,108,373,-524,-3799,2448,4987,-297,5016,700183,346288,-693,13021,-11993,-2569,1052,32,22,2210878,-14404,2307270,69,-65215,380482,659,18794,101,248,-656,1403801,1277,1917,-1054,253,72024,-12928,-264,4247,214524,-408265,426326,-237,586,81,-71021,-2613,-109264,5667,2648211,364741,2926391,-909,-101153,1,410,300,1572,-295889,-140,1286405,28,6761,-61,127,-216,208,-59};
        if (c == 4 && n == 11) w = new int[] {7,-1,-21,0,41,-39,-29,-81,-18,783,722,-14,13,-48,-118,-46,-24,-18,2017,2426,15425,6,-56,782,-1,-24,-7,-28,0,847,14,-1,-15,20,62,-6,19,-8,841,462,601,-21,-4,-38,36,-40,152,310,1114,2706,16661,-26,-25,28,-30,-37,26,-38,20,735,30,479,-40,-97,6,50,41};
        if (c == 5 && n == 11) w = new int[] {-1,-1,-1,-1,3,-1,-1,3,-1,979,1145,-1,-1,-1,-1,-1,1,-1,8548,8548,37233,-1,3,-1,-1,-1,3,-1,-1,-1,-1,-1,-1,-1,3,3,3,-1,1415,1123,1037,-1,-1,-4,1,-1,-1,61,27483,10829,45873,-1,-1,-1,0,0,-1,-1,3,-1,40,10000,1000,50,10,50,20};
        if (c == 6 && n == 11) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 7 && n == 11) w = new int[] {0,-1,-1,-1,54,-4,-4,-1,-1,755,907,0,-13,2,-13,3,2,-1,3579,3524,69242,0,-1,765,4,2,-1,-1,-1,53,-1,-1,3,2,2,-1,-1,-1,783,888,234,0,-1,-1,-1,-2,-1,7,4730,2941,23262,-2,-1,0,2,0,-1,-4,0,93,26,10000,1000,50,10,50,20};
        if (c == 8 && n == 11) w = new int[] {-1,-1,-1,-1,90,-3,-2,-1,-1,1270,1529,-1,-9,-1,-9,0,-1,-1,6035,5943,116817,-1,-1,1289,3,-1,-2,-1,-1,81,0,-1,2,-1,-1,-1,-1,-1,1319,1496,391,-1,-2,-1,-1,-1,-1,7,7976,4959,39242,-1,-1,-1,-1,-1,-1,-3,-1,154,38,10000,1000,50,10,50,20};
        if (c == 9 && n == 11) w = new int[] {-1,-1,-1,-1,66,-1,-1,-1,-1,968,1167,-1,-5,-1,-6,0,0,-1,4612,4541,89304,-1,-1,983,0,-1,-1,-1,-1,60,0,-1,-1,-1,-1,-1,-1,-1,1006,1142,296,-1,-1,-1,-1,0,0,3,6096,3789,29998,0,0,0,0,-1,-1,0,-1,115,31,10000,1000,50,10,50,20};
        w1 = w[60];
        w2 = w[61];
        w3 = w[62];
        w4 = w[63];
        w5 = w[64];
        w6 = w[65];
        w7 = w[66];
    }

    private int encode(int empty, int cnt, int seq) {
        return (empty << 6) | (cnt << 3) | seq;
    }

    private Beam<Move> moveEval(int width, Move parent) {
        Beam<Move> moves = new Beam<Move>(width);
        filled = 0;
        for (int i : grid) {
            if (i != 0) {
                filled++;
            }
        }
        int ff = filled;
        filled = (filled << 3) / nn;
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                int p = y * n + x;
                if (x - delta >= 0 && x + delta < n) gridHoriz[p] = evalHoriz(p);
                if (y - delta >= 0 && y + delta < n) gridVert[p] = evalVert(p);
                if (x - delta >= 0 && x + delta < n && y - delta >= 0 && y + delta < n) {
                    gridDiag1[p] = evalDiag1(p);
                    gridDiag2[p] = evalDiag2(p);
                }
            }
        }
        for (int y = 0; y < n; y++) {
            for (int x = 0; x < n; x++) {
                final int p = y * n + x;
                final int g = grid[p];
                if (g == 0) continue;
                Arrays.fill(reach, false);
                reach[p] = true;
                queue[0] = p;
                int tot = 1;
                int curr = 0;
                while (curr < tot) {
                    int q = queue[curr++];
                    int px = q % n;
                    int py = q / n;
                    for (int i = 0; i < 4; i++) {
                        int nx = i == 0 ? px - 1 : i == 1 ? px + 1 : px;
                        if (nx < 0 || nx >= n) continue;
                        int ny = i == 2 ? py - 1 : i == 3 ? py + 1 : py;
                        if (ny < 0 || ny >= n) continue;
                        int np = ny * n + nx;
                        if (grid[np] == 0 && !reach[np]) {
                            reach[np] = true;
                            queue[tot++] = np;
                        }
                    }
                }
                if (tot > 1) {
                    if (parent != null) parent.value += (tot - 1) * 2;
                    grid[p] = 0;
                    remHorizIdxCnt = 0;
                    remVertIdxCnt = 0;
                    remDiag1IdxCnt = 0;
                    remDiag2IdxCnt = 0;
                    int rem = eval(p, true) - ff * ff;
                    for (int i = 1; i < tot; i++) {
                        int np = queue[i];
                        grid[np] = g;
                        int v = eval(np, false) + rem;
                        grid[np] = 0;
                        moves.add(new Move(p, np, v));
                    }
                    grid[p] = g;
                    for (int i = 0; i < remHorizIdxCnt; i++) {
                        remHorizVal[remHorizIdxs[i]] = Integer.MIN_VALUE;
                    }
                    for (int i = 0; i < remVertIdxCnt; i++) {
                        remVertVal[remVertIdxs[i]] = Integer.MIN_VALUE;
                    }
                    for (int i = 0; i < remDiag1IdxCnt; i++) {
                        remDiag1Val[remDiag1Idxs[i]] = Integer.MIN_VALUE;
                    }
                    for (int i = 0; i < remDiag2IdxCnt; i++) {
                        remDiag2Val[remDiag2Idxs[i]] = Integer.MIN_VALUE;
                    }
                }
            }
        }
        return moves;
    }

    private String move() {
        turn++;
        int mult = filled >= 7 ? 2 : 1;
        if (runtime > 8500) width1 = width2 = mult = 1;
        Beam<Move> moves = moveEval(width1 * mult, null);
        if (moves.size() == 0) return "";
        int numSeen = 0;
        if (moves.size() > 1 && turn < 1000) {
            System.arraycopy(grid, 0, savedGrid1, 0, nn);
            NEXT: for (int i = 0; i < moves.size(); i++) {
                Move mi = moves.get(i);
                grid[mi.m2] = grid[mi.m1];
                grid[mi.m1] = 0;
                int vi = clean(mi.m2);
                if (vi > 0) {
                    for (int j = 0; j < numSeen; j++) {
                        int[] sj = seen[j];
                        if (sj[mi.m1] == grid[mi.m1] && sj[mi.m2] == grid[mi.m2]) {
                            if (Arrays.equals(sj, grid)) {
                                System.arraycopy(savedGrid1, 0, grid, 0, nn);
                                continue NEXT;
                            }
                        }
                    }
                    System.arraycopy(grid, 0, seen[numSeen++], 0, nn);
                    mi.value += vi * filled * w2;
                }
                System.arraycopy(grid, 0, savedGrid2, 0, nn);
                Beam<Move> mm1 = moveEval(width2 * mult, mi);
                int max = Integer.MIN_VALUE;
                for (int j = 0; j < mm1.size(); j++) {
                    Move mj = mm1.get(j);
                    grid[mj.m2] = grid[mj.m1];
                    grid[mj.m1] = 0;
                    int vj = clean(mj.m2);
                    int curr = mj.value * w4 / 100 + vj * w3;
                    mi.value += mj.value * w5 / 400;
                    Beam<Move> mm2 = moveEval(1, null);
                    if (mm2.size() > 0) {
                        Move m2 = mm2.get(0);
                        curr += m2.value * w6 / 400;
                        mi.value += m2.value * w7 / 3200;
                    }
                    if (curr > max) max = curr;
                    System.arraycopy(savedGrid2, 0, grid, 0, nn);
                }
                mi.value += max;
                System.arraycopy(savedGrid1, 0, grid, 0, nn);
            }
            moves.sort();
        }
        Move m = moves.get(0);
        return m.m1 / n + " " + m.m1 % n + " " + m.m2 / n + " " + m.m2 % n;
    }

    private int clean(int p) {
        int x = p % n;
        int y = p / n;
        int rem = 0;
        int g = grid[p];
        for (int i = 0; i < 4; i++) {
            int dx = new int[] {0,1,1,-1}[i];
            int dy = new int[] {1,0,1,1}[i];
            int v = 1;
            for (int dir = -1; dir <= 1; dir += 2) {
                int nx = x;
                int ny = y;
                while (true) {
                    nx += dir * dx;
                    if (nx >= n || nx < 0) break;
                    ny += dir * dy;
                    if (ny >= n || ny < 0) break;
                    if (grid[nx + ny * n] == g) v++;
                    else break;
                }
            }
            if (v >= 5) {
                for (int dir = -1; dir <= 1; dir += 2) {
                    int nx = x;
                    int ny = y;
                    while (true) {
                        nx += dir * dx;
                        if (nx >= n || nx < 0) break;
                        ny += dir * dy;
                        if (ny >= n || ny < 0) break;
                        int np = nx + ny * n;
                        if (grid[np] == g) toRem[rem++] = np;
                        else break;
                    }
                }
            }
        }
        if (rem > 0) {
            for (int i = 0; i < rem; i++) {
                grid[toRem[i]] = 0;
            }
            grid[p] = 0;
            rem++;
            return rem * (rem - 7) + 20;
        }
        return 0;
    }

    private int eval(int p, boolean rem) {
        int ret = 0;
        int[] np = neighborsHoriz[p];
        for (int q : np) {
            int v = evalHoriz(q);
            if (rem) {
                remHorizIdxs[remHorizIdxCnt++] = q;
                remHorizVal[q] = v;
                v -= gridHoriz[q];
            } else {
                int rv = remHorizVal[q];
                v -= rv == Integer.MIN_VALUE ? gridHoriz[q] : rv;
            }
            ret += v;
        }
        np = neighborsVert[p];
        for (int q : np) {
            int v = evalVert(q);
            if (rem) {
                remVertIdxs[remVertIdxCnt++] = q;
                remVertVal[q] = v;
                v -= gridVert[q];
            } else {
                int rv = remVertVal[q];
                v -= rv == Integer.MIN_VALUE ? gridVert[q] : rv;
            }
            ret += v;
        }
        np = neighborsDiag1[p];
        for (int q : np) {
            int v = evalDiag1(q);
            if (rem) {
                remDiag1Idxs[remDiag1IdxCnt++] = q;
                remDiag1Val[q] = v;
                v -= gridDiag1[q];
            } else {
                int rv = remDiag1Val[q];
                v -= rv == Integer.MIN_VALUE ? gridDiag1[q] : rv;
            }
            ret += v;
        }
        np = neighborsDiag2[p];
        for (int q : np) {
            int v = evalDiag2(q);
            if (rem) {
                remDiag2Idxs[remDiag2IdxCnt++] = q;
                remDiag2Val[q] = v;
                v -= gridDiag2[q];
            } else {
                int rv = remDiag2Val[q];
                v -= rv == Integer.MIN_VALUE ? gridDiag2[q] : rv;
            }
            ret += v;
        }
        return ret;
    }

    private int evalHoriz(int p) {
        evalSeq0 = grid[p - 2];
        evalSeq1 = grid[p - 1];
        evalSeq2 = grid[p];
        evalSeq3 = grid[p + 1];
        evalSeq4 = grid[p + 2];
        return eval(false);
    }

    private int evalVert(int p) {
        evalSeq0 = grid[p - n2];
        evalSeq1 = grid[p - n];
        evalSeq2 = grid[p];
        evalSeq3 = grid[p + n];
        evalSeq4 = grid[p + n2];
        return eval(false);
    }

    private int evalDiag1(int p) {
        evalSeq0 = grid[p - n2 - 2];
        evalSeq1 = grid[p - n - 1];
        evalSeq2 = grid[p];
        evalSeq3 = grid[p + n + 1];
        evalSeq4 = grid[p + n2 + 2];
        return eval(true);
    }

    private int evalDiag2(int p) {
        evalSeq0 = grid[p - n2 + 2];
        evalSeq1 = grid[p - n + 1];
        evalSeq2 = grid[p];
        evalSeq3 = grid[p + n - 1];
        evalSeq4 = grid[p + n2 - 2];
        return eval(true);
    }

    private int eval(boolean diag) {
        int key = (filled << 1) | (evalSeq0 << 4) | (evalSeq1 << 8) | (evalSeq2 << 12) | (evalSeq3 << 16) | (evalSeq4 << 20);
        if (diag) key |= 1;
        int r = memo[key];
        if (r != Integer.MIN_VALUE) return r;
        Arrays.fill(countSeq, 0);
        countSeq[evalSeq0]++;
        countSeq[evalSeq1]++;
        countSeq[evalSeq2]++;
        countSeq[evalSeq3]++;
        countSeq[evalSeq4]++;
        int empty = countSeq[0];
        if (empty == len) {
            int off = offsets[320];
            if (diag) off += 30;
            return memo[key] = w[off];
        }
        int color = -1;
        int maxCnt = 1;
        int c2 = -1;
        for (int i = 1; i <= c; i++) {
            int ci = countSeq[i];
            if (ci >= maxCnt) {
                maxCnt = ci;
                c2 = color;
                color = i;
            }
        }
        int maxSeq = 0;
        if (maxCnt == 1) {
            maxSeq = 1;
        } else if (maxCnt > 1) {
            maxSeq = 1;
            int seq = evalSeq0 == color ? 1 : 0;
            if (evalSeq1 == color) {
                if (++seq > maxSeq) maxSeq = seq;
            } else {
                seq = 0;
            }
            if (evalSeq2 == color) {
                if (++seq > maxSeq) maxSeq = seq;
            } else {
                seq = 0;
            }
            if (evalSeq3 == color) {
                if (++seq > maxSeq) maxSeq = seq;
            } else {
                seq = 0;
            }
            if (evalSeq4 == color && ++seq > maxSeq) maxSeq = seq;
            if (maxCnt == 2 && c2 != -1) {
                seq = evalSeq0 == c2 ? 1 : 0;
                if (evalSeq1 == c2) {
                    if (++seq > maxSeq) maxSeq = seq;
                } else {
                    seq = 0;
                }
                if (evalSeq2 == c2) {
                    if (++seq > maxSeq) maxSeq = seq;
                } else {
                    seq = 0;
                }
                if (evalSeq3 == c2) {
                    if (++seq > maxSeq) maxSeq = seq;
                } else {
                    seq = 0;
                }
                if (evalSeq4 == c2 && ++seq > maxSeq) maxSeq = seq;
            }
        }
        int ret = 0;
        if (empty + maxCnt < len) ret -= filled * w1;
        int off = offsets[encode(empty, maxCnt, maxSeq)];
        if (diag) off += 30;
        return memo[key] = w[off] + ret;
    }

    public static void main(String[] args) {
        try {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
            int n = Integer.parseInt(br.readLine());
            int c = Integer.parseInt(br.readLine());
            Lines lines = new Lines(n, c);
            OUT: while (true) {
                for (int y = 0; y < n; y++) {
                    for (int x = 0; x < n; x++) {
                        String s = br.readLine();
                        if (s == null) break OUT;
                        lines.grid[y * n + x] = Integer.parseInt(s);
                    }
                }
                for (int i = 0; i < 3; i++) {
                    lines.nextBalls[i] = Integer.parseInt(br.readLine());
                }
                lines.runtime = Long.parseLong(br.readLine());
                System.out.println(lines.move());
                System.out.flush();
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}

class Move implements Comparable<Move> {
    int m1, m2, value;

    public Move(int m1, int m2, int value) {
        this.m1 = m1;
        this.m2 = m2;
        this.value = value;
    }

    public int compareTo(Move o) {
        return o.value - value;
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

    void sort() {
        Arrays.sort(items, 0, size);
    }

    int size() {
        return size;
    }

    void clear() {
        size = 0;
    }
}