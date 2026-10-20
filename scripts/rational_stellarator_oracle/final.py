import sys, pickle
from fractions import Fraction as Fr
from gen import *
import dense
from plan import Searcher

fit = 'fit_10_5_0.1_sym.pkl'
P = load_P(fit)
G = G4()
Ib = 4398046511          # ~ 0.004 * 2^40
Ia = 1099511628          # ~ 0.001 * 2^40 (rounded up)
delta = 17592186         # ~ 4e-6 * 4 * 2^40
assert all((getD(e,1)+getD(e,2)) % 2 == 0 for c,e in P)
out = {}
# ---------------- main
Q, dQ = mainRoot(P, 1)
dsg, dze, dta = degs(Q)
print('Q degs', dsg, dze, dta, 'dQ', dQ)
A = trim(scale0(10, dsg, scale1(10, dze, Q)))
fac = 10**(dsg + dze)
tp = onePlusSq(dQ)
D = [[smul1(delta*fac, tp)], [smul1(delta*4*fac//10, tp)], [smul1(delta*4*fac//100, tp)]]
dd = (12, 13, 12)
dense.COST[0] = 0
S = Searcher('abs', (1.0, 1.0, 0.125), rem_frac=0.5, floor=int(0.64*delta*fac), dd=dd)
pl = S.search(A, D, 0, [1.0, 1.0, 1.0], 0)
print('main cost', dense.COST[0], 'leaves', S.leaves)
tree, _ = parse_plan(pl)
cps = []
top = checkpoint(tree, A, D, 0, dd, int(sys.argv[1]) if len(sys.argv) > 1 else 2, cps)
print('top plan', plan_str(top))
subcosts = []
for (Ac, Dc, rc, sp) in cps:
    dense.COST[0] = 0
    t, _ = parse_plan(sp)
    # replay to measure cost
    def replay(t, A, D, rem):
        if t[0] == 'L':
            ok = absup(A, rem) <= lower(D, 0); assert ok; return
        if t[0] == 'D':
            A2, r2 = truncate_total(A, t[1]); return replay(t[2], A2, D, rem + r2)
        ax = t[1]; d = dd[ax]
        replay(t[2], shift_ax(A, ax, -1, d), shift_ax(D, ax, -1, d), rem << d)
        replay(t[3], shift_ax(A, ax, 1, d), shift_ax(D, ax, 1, d), rem << d)
    replay(t, Ac, Dc, rc)
    subcosts.append(dense.COST[0])
print('sub costs', subcosts)
out['main'] = dict(Q=Q, A=A, D=D, dd=dd, plan=pl, top=plan_str(top), cps=cps, dsg=dsg, dze=dze, dQ=dQ)
# ---------------- I chart, faces
dI = 5
Ich = chartD(dI, 1, P)
dsI, dzI, dtI = degs(Ich)
print('I degs', dsI, dzI, dtI)
Il = trim(scale0(10, dsI, scale1(10, dzI, Ich)))
facI = 10**(dsI + dzI)
IbC = [[smul1(Ib*facI, onePlusSq(dI))]]
faces = []
for ax in (0, 1):
    for pos in (True, False):
        F = add3(IbC, neg3(restrict(ax, pos, Il)))
        Dm = [[[-1]]]
        fdd = (max(degs(F)[0], 0), max(degs(F)[1], 0), degs(F)[2])
        dense.COST[0] = 0
        S = Searcher('up', (1.0, 1.0, 0.125), rem_frac=0.1, trunc=True, dd=fdd)
        fp = S.search(F, Dm, 0, [1.0, 1.0, 1.0], 0)
        print('face', ax, pos, 'dd', fdd, 'cost', dense.COST[0], 'leaves', S.leaves, fp is not None)
        faces.append(dict(ax=ax, pos=pos, dd=fdd, plan=fp))
out['I'] = dict(Ich=Ich, Il=Il, dsI=dsI, dzI=dzI, faces=faces)
# ---------------- start
Pst = [(c*20000, e) for c, e in P] + [(c*(-10625*2**E), e) for c, e in J2] + [(17*2**E - 20000*Ia, [0, 0, 0, 0])]
Sch = chartD(dI, 1, Pst)
dsS, dzS, dtS = degs(Sch)
Sl = trim(scale0(25, dsS, scale1(25, dzS, Sch)))
sdd = degs(Sl)
dense.COST[0] = 0
S = Searcher('up', (1.0, 1.0, 0.25), rem_frac=0.3, trunc=True, dd=sdd)
spl = S.search(Sl, [[[0]]], 0, [1.0, 1.0, 1.0], 0)
print('start degs', dsS, dzS, 'dd', sdd, 'cost', dense.COST[0], 'leaves', S.leaves, spl is not None)
out['start'] = dict(Pst=Pst, Sl=Sl, dsS=dsS, dzS=dzS, dd=sdd, plan=spl)
out['P'] = P; out['G'] = G; out['Ib'] = Ib; out['Ia'] = Ia; out['delta'] = delta
pickle.dump(out, open('final.pkl', 'wb'))
