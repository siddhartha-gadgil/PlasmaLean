# Bridge/

Composition theorems: they connect kernel laws to each other and to theory or certificate
results, with every hypothesis explicit, so that conclusions about one object can be combined.

- [`Example.lean`](Example.lean): `OscillatorLaw.shift` (time translation), `OscillatorLaw.add`
  and `OscillatorLaw.smul` (superposition), `energy_eq_of_law`, and `amplitude_bound`
  (conservation composed with the potential bound), used by `Certificates/Example`.
