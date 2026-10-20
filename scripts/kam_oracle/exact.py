"""UNTRUSTED (but exact).  Exact integer evaluation of the K2 residual polynomials, mirroring
PlasmaLean/Design/KamTorusA.lean (`Rhat`, `Zhat`, ..., `RRhat`, `RZhat`).

Formal polynomials in u = e^{i theta}, v = e^{i psi} (psi = 2 phi - pi/2) with integer
coefficients, stored as dicts {(i, j): c} meaning c u^i v^j (i, j >= 0).  With integer data
A_{km} = 2^P a_{km}, B_{km} = 2^P b_{km}, sigma = 2^{P+1}, w = u^N v^M, t = sigma w:

    Rh  = sum_{Is} A (u^{N+k} v^{M+m} + u^{N-k} v^{M-m})      = t R
    Zh  = sum_{Iz} B (u^{N+k} v^{M+m} - u^{N-k} v^{M-m})      = t (i z)
    Rth = sum_{Is} k A (u^{N+k} v^{M+m} - u^{N-k} v^{M-m})    = -i t d_theta R
    Rps = sum_{Is} m A (...same...)                            = -i t d_psi R
    Zth = sum_{Iz} k B (u^{N+k} v^{M+m} + u^{N-k} v^{M-m})    = t d_theta z
    Zps = sum_{Iz} m B (...)                                   = t d_psi z
    Ch = v^2 + 1 = 2 v cos psi,   Sv = v^2 - 1 = 2 i v sin psi,   E = Rh^2 - t^2,  F = Rh^2 - 5 t^2
    Dh  = 16 t^3 v Rh^2 - t (E^2 + 4 t^2 Zh^2) Ch - Zh (E F + 4 t^2 Zh^2) Sv
    LRh = 2^{Q+1} Rps + Iq Rth,          LZh = 2^{Q+1} Zps + Iq Zth     (iota_q = Iq / 2^Q)
    PRh = t (Rh^4 - t^4 - 4 t^2 Zh^2) Sv + Zh (Rh^4 - 5 t^4 - 4 t^2 Zh^2) Ch
    PZh = 8 t^3 Zh Sv + (E F + 12 t^2 Zh^2) Ch
    RRh = Dh LRh - 2^Q Rh PRh,            RZh = 2 Dh LZh + 2^Q Rh^2 PZh

and on |u| = |v| = 1:  RR = i RRh / (2^{Q+4} t^6 v),  Rz = RZh / (2^{Q+5} t^6 v),  D = Dh/(16 t^5 v),
where RR, Rz are the residuals of flow_torus.py with iota replaced by iota_q.
Products are computed by Kronecker substitution u -> X = 2^b, v -> X^W (W = 12N+1).
"""
import gmpy2
from gmpy2 import mpz


class Kron:
    def __init__(self, N, M, b):
        self.N, self.M, self.b = N, M, b
        self.W = 12 * N + 1
        self.rows = 12 * M + 3
        self.nslots = self.W * self.rows
        assert b % 8 == 0
        self.B = b // 8

    def pack(self, d):
        nb = self.nslots * self.B
        pos = bytearray(nb)
        neg = bytearray(nb)
        for (i, j), c in d.items():
            if c == 0:
                continue
            assert 0 <= i < self.W and 0 <= j < self.rows, (i, j)
            n = (i + self.W * j) * self.B
            if c > 0:
                pos[n:n + self.B] = int(c).to_bytes(self.B, 'little')
            else:
                neg[n:n + self.B] = int(-c).to_bytes(self.B, 'little')
        return mpz(int.from_bytes(pos, 'little')) - mpz(int.from_bytes(neg, 'little'))

    def unpack(self, Nv):
        """Balanced base-X digits (assumes all |digit| < X/2)."""
        half = mpz(1) << (self.b - 1)
        off = int.from_bytes(half.to_bytes(self.B, 'little') * self.nslots, 'little')
        T = int(Nv + off)
        assert T >= 0
        bs = T.to_bytes(self.nslots * self.B + 1, 'little')
        assert bs[-1] == 0, "overflow"
        out = {}
        h = int(half)
        for n in range(self.nslots):
            c = int.from_bytes(bs[n * self.B:(n + 1) * self.B], 'little') - h
            if c:
                out[(n % self.W, n // self.W)] = c
        return out


def formal_inputs(A, B, Is, Iz, N, M):
    Sh, Zh, Sth, Sps, Zth, Zps = {}, {}, {}, {}, {}, {}

    def add(d, key, c):
        d[key] = d.get(key, 0) + c
    for (k, m), c in zip(Is, A):
        p, q = (N + k, M + m), (N - k, M - m)
        add(Sh, p, c); add(Sh, q, c)
        add(Sth, p, k * c); add(Sth, q, -k * c)
        add(Sps, p, m * c); add(Sps, q, -m * c)
    for (k, m), c in zip(Iz, B):
        p, q = (N + k, M + m), (N - k, M - m)
        add(Zh, p, c); add(Zh, q, -c)
        add(Zth, p, k * c); add(Zth, q, k * c)
        add(Zps, p, m * c); add(Zps, q, m * c)
    return Sh, Zh, Sth, Sps, Zth, Zps


def residual_packed(K, A, B, Is, Iz, P, Q, Iq):
    """Packed integers (Kronecker values at X = 2^b) of RRh, RZh, Dh and of the inputs."""
    N, M = K.N, K.M
    ins = [K.pack(d) for d in formal_inputs(A, B, Is, Iz, N, M)]
    Rh, Zh, Rth, Rps, Zth, Zps = ins
    X = mpz(1) << K.b
    v = X ** K.W
    sigma = mpz(1) << (P + 1)
    t = sigma * X ** N * v ** M
    Ch = v * v + 1
    Sv = v * v - 1
    t2 = t * t
    Z2 = Zh * Zh
    R2 = Rh * Rh
    E = R2 - t2
    F = R2 - 5 * t2
    tZ = 4 * t2 * Z2
    Dh = 16 * t2 * t * v * R2 - t * (E * E + tZ) * Ch - Zh * (E * F + tZ) * Sv
    q1 = mpz(1) << (Q + 1)
    LRh = q1 * Rps + Iq * Rth
    LZh = q1 * Zps + Iq * Zth
    R4 = R2 * R2
    t4 = t2 * t2
    PRh = t * (R4 - t4 - tZ) * Sv + Zh * (R4 - 5 * t4 - tZ) * Ch
    PZh = 8 * t2 * t * Zh * Sv + (E * F + 3 * tZ) * Ch
    q0 = mpz(1) << Q
    RRh = Dh * LRh - q0 * Rh * PRh
    RZh = 2 * Dh * LZh + q0 * R2 * PZh
    return RRh, RZh, Dh, ins, t
