# |B| on the magnetic axis of Landreman families 1 and 2 (closed forms from the Lean files),
# checked against the field formula. Any weak-QS generator that is nonvanishing on the axis
# forces |B| to be constant on the axis (N-27, Claim 3).
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, sympy as sp
from qs_family import family2, family1, x, y, z
for eps, S in [(0.25, 4.0), (2.0, 1.0), (1/16, 4.0)]:
    h = np.sqrt(4*S**2 + eps**2); a = np.sqrt((h-eps)/2); b = np.sqrt((h+eps)/2)
    B, _ = family2(eps, S, 15.0); f = sp.lambdify((x, y, z), sp.sqrt((B.T*B)[0]))
    zs = np.linspace(0, np.pi, 7)
    num = np.array([f(a*np.cos(t), b*np.sin(t), 0.0) for t in zs])
    cf = np.cosh(eps/2*np.sin(2*zs))/np.sqrt(2*(h + eps*np.cos(2*zs)))
    print(f"family2 eps={eps} S={S}: |B|_axis in [{num.min():.5f},{num.max():.5f}], "
          f"rel. variation {(num.max()-num.min())/num.mean():.3e}, closed-form error {abs(num-cf).max():.1e}")
for eps in [0.3, 0.5]:
    B, _ = family1(eps); f = sp.lambdify((x, y, z), sp.sqrt((B.T*B)[0]))
    zs = np.linspace(0, np.pi, 7); R = np.sqrt(1-eps**2)
    num = np.array([f(R*np.cos(t), R*np.sin(t), eps/2*np.sin(2*t)) for t in zs])
    cf = np.sqrt(1 - eps**2 + eps**2*np.cos(2*zs)**2)
    print(f"family1 eps={eps}: |B|_axis in [{num.min():.5f},{num.max():.5f}], closed-form error {abs(num-cf).max():.1e}")
