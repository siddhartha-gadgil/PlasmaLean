"""UNTRUSTED helper.  Torus selection for the Lean emitters of the Dommaschk KAM certificate.

The emitters (`emit_torus.py`, `emit_adm.py`, `emit_res.py`) were written for the certification torus C
(`iota_C = -(85 + sqrt 5)/361`, modules `Design/DommaschkKamC*`, namespace `DommaschkKamC`).  The same
emitters produce the chain of torus A (`iota_A = -(19 + sqrt 5)/89`, the outer torus of the nested
certified region) when called with `--tag A`:

  * the input data module is `DommaschkKam<tag>Data.lean`; torus A reuses the moving centre of torus C
    (same magnetic axis), read from `DommaschkKamCData.lean`;
  * every generated text passes through `retarget`, which is the identity for torus C (so the C outputs
    are byte-identical to the original emitters) and, for torus A, renames the torus-specific modules
    (`DommaschkKamC<X>` -> `DommaschkKamA<X>`, except the torus-independent modules in `GENERIC`), the
    namespace (`DommaschkKamA`, opening `DommaschkKamC` for the generic declarations: names of the
    current namespace take precedence over opened ones in Lean 4), and the few torus-specific
    identifiers and phrases (`u0C`, `z0C`, `iotaqC`, `dkIotaC`, `iota_C`, `torus C`).
"""
import re

TAG = 'C'

# torus-independent modules of the C chain, reused by the A chain
GENERIC = ('KronW', 'AdmFrame', 'Jet', 'ResKron')

TORI = {
    'C': dict(ia=85, ib=361, iota_abs_up=(2417, 10000), iota_txt='−(85 + √5)/361 ≈ −0.2416512',
              gam=0.2671, dlow=0.1208, oracle_e='5.9e-29'),
    'A': dict(ia=19, ib=89, iota_abs_up=(2387, 10000), iota_txt='−(19 + √5)/89 ≈ −0.2386075',
              gam=0.3645, dlow=0.1193, oracle_e='2.9e-27'),
}


def select(tag):
    global TAG
    assert tag in TORI, tag
    TAG = tag


def cfg():
    return TORI[TAG]


def data_module():
    return 'DommaschkKam%sData.lean' % TAG


_MOD = re.compile(r'DommaschkKamC([A-Z][A-Za-z0-9]*)')
_IDENT = [('u₀C', 'u₀A'), ('z₀C', 'z₀A'), ('iotaqC', 'iotaqA'), ('dkIotaC', 'dkIotaA'), ('ι_C', 'ι_A'),
          ('torus-C', 'torus-A'), ('torus C', 'torus A'), ('Torus C', 'Torus A'),
          ('(85 + √5)/361', '(19 + √5)/89'), ('0.2416512', '0.2386075'),
          ('e₀ ≲ 1.3e-23', 'e₀ ≲ 6.1e-24'), ('≈ 1.3·10⁻²³', '≈ 6.1·10⁻²⁴')]


def _mod(m):
    return m.group(0) if m.group(1) in GENERIC else 'DommaschkKamA' + m.group(1)


def retarget(text):
    """The torus-A version of a generated torus-C text (identity for torus C)."""
    if TAG == 'C':
        return text
    t = _MOD.sub(_mod, text)
    # the torus data (`Uo`, `Zo`, `Iqc`, ...) of the generic imports belong to torus C: add the A torus
    t = re.sub(r'(public import PlasmaLean\.Design\.DommaschkKamC(?:KronW|ResKron)\n)',
               r'\1public import PlasmaLean.Design.DommaschkKamATorus\n', t)
    opn = '\n\nopen PlasmaLean.Design.DommaschkKamC' if 'import PlasmaLean.' in t else ''
    t = re.sub(r'^namespace PlasmaLean\.Design\.DommaschkKamC$',
               'namespace PlasmaLean.Design.DommaschkKamA' + opn, t, flags=re.M)
    t = re.sub(r'^end PlasmaLean\.Design\.DommaschkKamC$', 'end PlasmaLean.Design.DommaschkKamA', t,
               flags=re.M)
    t = t.replace('DommaschkKamC.', 'DommaschkKamA.')
    for a, b in _IDENT:
        t = t.replace(a, b)
    return t


def out_name(mod):
    """The module name of a generated C module for the selected torus."""
    return retarget(mod)
