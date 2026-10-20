import random
random.seed(1)
D=2**64
rows=[]
seen=set()
while len(rows)<100:
    e=(random.randint(0,6),random.randint(0,6),random.randint(0,3))
    if e in seen: continue
    seen.add(e)
    rows.append(f"{random.randint(-D,D)} {random.randint(0,1000)} {e[0]} {e[1]} {e[2]}")
bp=";\n".join(rows)
leaves=[]
for i in range(200):
    c0=random.randint(-D//10,D//10); c1=random.randint(-D//10,D//10); c2=random.randint(-D,D)
    leaves.append(f"theorem leaf{i} : boundOK (evalB T1 [⟨{c0}, {D//100}⟩, ⟨{c1}, {D//100}⟩, ⟨{c2}, {D//50}⟩]) 1000 = true := by decide +kernel")
open('/tmp/rsc/lt/T1.lean','w').write(f'''import PlasmaLean.Theory.Kinetic.AveragedTrapping
open PlasmaLean.Kinetic.LiePoly
def boundOK (b : FBall) (A : ℕ) : Bool := decide (b.c.natAbs + b.r ≤ A * Dk)
def T1 : BPoly := bpoly% "{bp}"
'''+"\n".join(leaves)+"\n")
