"""UNTRUSTED.  Predict the weighted K2 kernel checks of PlasmaLean/Design/KamTorusAWeightedCheck.lean.

Reads the packed torus data from PlasmaLean/Design/KamTorusAData.lean, rebuilds the Kronecker
images exactly as the Lean forms do (Dform, RRform, RZform of KamTorusAForms), and evaluates the
separable weighted digit sums `wl1KronP` with the integer weights
`p^s 2^(e(K - s))` (`p = 74315`, `e = 16`, so `p / 2^e >= exp(0.1257)`).
Prints each weighted norm and whether the stated Lean inequality holds.

Usage: python weighted_cert.py [path/to/KamTorusAData.lean]
"""
import math
import re
import sys
from fractions import Fraction

from gmpy2 import mpz

DATA = 'PlasmaLean/Design/KamTorusAData.lean'
N, M, P, Q = 32, 22, 90, 96
IQ = 10888383889117653077957113864
PW, EW = 74315, 16


def load(path):
    src = open(path).read()
    dA = int(re.search(r'def dataA : ℕ := (0x[0-9a-f]+)', src).group(1), 16)
    dB = int(re.search(r'def dataB : ℕ := (0x[0-9a-f]+)', src).group(1), 16)

    def gc(d, i, j):
        if i < N:
            return 0
        f = (i - N) * (2 * M + 1) + j
        return ((d >> (96 * f)) % 2 ** 96) - 2 ** 95
    I, J = 2 * N + 1, 2 * M + 1
    cA = [[gc(dA, i, j) for j in range(J)] for i in range(I)]
    cB = [[gc(dB, i, j) for j in range(J)] for i in range(I)]
    return cA, cB


def pack_grid(g, b, W):
    tot = mpz(0)
    for j in range(2 * M + 1):
        row = mpz(0)
        for i in range(2 * N + 1):
            row += mpz(g(i, j)) << (b * i)
        tot += row << (b * W * j)
    return tot


def kwt(K, s):
    return mpz(PW) ** s * mpz(2) ** (EW * max(K - s, 0))


def wl1kronp(Nv, b, W, R, i0, j0, Ki, Kj):
    """sum_{j<R} wB(j) sum_{i<W} wA(i) |digit(i + W j)| (balanced base-2^b digits)."""
    H = mpz(1) << (b - 1)
    S = W * R
    off = mpz(H)
    k = 1
    while k < S:
        off = off + (off << (b * k))
        k *= 2
    T = int(Nv + off)
    nb = b // 8
    bs = T.to_bytes((T.bit_length() + 7) // 8 + 1, 'little')
    wA = [kwt(Ki, abs(i - i0)) for i in range(W)]
    tot = mpz(0)
    for j in range(R):
        row = mpz(0)
        for i in range(W):
            n = i + W * j
            c = int.from_bytes(bs[n * nb:(n + 1) * nb], 'little') - H
            row += abs(c) * wA[i]
        tot += row * kwt(Kj, abs(j - j0))
    return tot


def main(path=DATA):
    cA, cB = load(path)
    gR = lambda i, j: cA[i][j] + cA[2 * N - i][2 * M - j]
    gZ = lambda i, j: cB[i][j] - cB[2 * N - i][2 * M - j]
    fns = {'Rh': gR, 'Zh': gZ, 'Rth': lambda i, j: (i - N) * gR(i, j),
           'Rps': lambda i, j: (j - M) * gR(i, j), 'Zth': lambda i, j: (i - N) * gZ(i, j),
           'Zps': lambda i, j: (j - M) * gZ(i, j)}
    sig = 2 ** (P + 1)
    x = Fraction(1257, 10000)
    ub = sum(x ** m / math.factorial(m) for m in range(6)) + x ** 6 * 7 / (720 * 6)
    print("exp(r_A) Taylor bound <= p/2^e:", ub <= Fraction(PW, 2 ** EW))
    b, W = 656, 12 * N + 1
    v = {k: pack_grid(f, b, W) for k, f in fns.items()}
    t = mpz(sig) << (b * (N + W * M))
    vP = mpz(1) << (b * W)
    Ch = (mpz(1) << (2 * b * W)) + 1
    Sv = (mpz(1) << (2 * b * W)) - 1
    Q2 = mpz(2) ** Q
    Rh, Zh = v['Rh'], v['Zh']
    E = Rh ** 2 - t ** 2
    F = Rh ** 2 - 5 * t ** 2
    T4 = 4 * (t ** 2 * Zh ** 2)
    D = 16 * (t ** 3 * vP * Rh ** 2) - t * (E ** 2 + T4) * Ch - Zh * (E * F + T4) * Sv
    PR = t * (Rh ** 4 - t ** 4 - T4) * Sv + Zh * (Rh ** 4 - 5 * t ** 4 - T4) * Ch
    PZ = 8 * (t ** 3 * Zh * Sv) + (E * F + 12 * (t ** 2 * Zh ** 2)) * Ch
    RR = D * (2 * Q2 * v['Rps'] + IQ * v['Rth']) - Q2 * (Rh * PR)
    RZ = 2 * (D * (2 * Q2 * v['Zps'] + IQ * v['Zth'])) + Q2 * (Rh ** 2 * PZ)
    S6 = mpz(2) ** (EW * (192 + 133))
    R6 = 12 * M + 3
    args6 = (b, W, R6, 6 * N, 6 * M + 1, 192, 133)
    wRR = wl1kronp(RR, *args6)
    wRZ = wl1kronp(RZ, *args6)
    wDR = wl1kronp(D * v['Rth'], *args6)
    wDZ = wl1kronp(D * v['Zth'], *args6)
    kR, kZ, kD6 = 2 ** (Q + 4) * sig ** 6, 2 ** (Q + 5) * sig ** 6, 16 * sig ** 6
    print(f"||E_R,q||_r = {float(Fraction(int(wRR), int(S6 * kR))):.5e}  check:",
          wRR * 10 ** 25 <= 5829 * kR * S6)
    print(f"||E_z,q||_r = {float(Fraction(int(wRZ), int(S6 * kZ))):.5e}  check:",
          wRZ * 10 ** 25 <= 3464 * kZ * S6)
    print(f"||D R_th||_r = {float(Fraction(int(wDR), int(S6 * kD6))):.4f}  check:",
          wDR * 100 <= 28 * kD6 * S6)
    print(f"||D z_th||_r = {float(Fraction(int(wDZ), int(S6 * kD6))):.4f}  check:",
          wDZ * 100 <= 29 * kD6 * S6)
    c0D = 1497829697890505117423261317586091192243358451745844281282756269272892177505483987164806341019131132689280335426443611037997419970979813664
    n0 = 5 * N + W * (5 * M + 1)
    S5 = mpz(2) ** (EW * (160 + 111))
    wDs = wl1kronp(D - (mpz(c0D) << (b * n0)), b, W, 10 * M + 3, 5 * N, 5 * M + 1, 160, 111)
    kD5 = 16 * sig ** 5
    print(f"d0 = {c0D / kD5:.6f}; ||D - d0||_r = {float(Fraction(int(wDs), int(S5 * kD5))):.4f}"
          "  check:", wDs * 1000 <= 483 * kD5 * S5, kD5 <= c0D, c0D * 1000 <= 1007 * kD5)
    b2, W2 = 128, 2 * N + 1
    S2 = mpz(2) ** (EW * (32 + 22))
    tg = mpz(sig) << (b2 * (N + W2 * M))
    for name, Nv, c in [('R - 1', pack_grid(gR, b2, W2) - tg, 228),
                        ('z', pack_grid(gZ, b2, W2), 224),
                        ('R_th', pack_grid(fns['Rth'], b2, W2), 236),
                        ('z_th', pack_grid(fns['Zth'], b2, W2), 231),
                        ('R_psi', pack_grid(fns['Rps'], b2, W2), 65),
                        ('z_psi', pack_grid(fns['Zps'], b2, W2), 63)]:
        w = wl1kronp(Nv, b2, W2, 2 * M + 1, N, M, 32, 22)
        print(f"||{name}||_r = {float(Fraction(int(w), int(S2 * sig))):.4f}  check:",
              w * 1000 <= c * sig * S2)


if __name__ == '__main__':
    main(*sys.argv[1:])
