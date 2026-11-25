"""Normalize a physical first-mirror height area on the original embedded torus birth."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import re

from verify_backward_physical_prefix import compile_modules
from verify_coarse_action_models import env
from verify_common_endpoint_traces import ENDPOINTS
from verify_mirror_physical_hit import admitted
from verify_physical_trace_slabs import DESIGN, ROOT, digest, save


def from_ordered_passage(origin):
    """Normalize the exact two cap widths, retaining the original passage as a hypothesis."""
    label = origin['endpoint']
    parent = origin['passage']
    certified = 'DommaschkArea' + label.upper() + 'Certified'
    if parent['module'] != certified:
        raise ValueError('the original ordered sign proof is required')
    roots = list(map(Path, parent['import_paths']))
    accepted = admitted(roots[0], certified, parent['key'])
    if f'PlasmaLean.Design.{certified}.from_original_passage' not in accepted['theorems']:
        raise ValueError('the accepted certificate does not prove the original passage implication')
    (k, n), (l, m) = origin['brackets']
    if not (0 < k < n <= k + 10 and 0 < l < m <= l + 10):
        raise ValueError('unexpected bracket width')
    band = Fraction(1292367655761, 2500000000000000)
    probability = (band - Fraction(n - k + m - l, 64 * 1250)) / band
    stem = 'DommaschkArea' + label.upper()
    name = 'DommaschkFirstMirrorSampling' + label.upper() + 'AtCaps'
    src = f'''module
public import FirstMirrorAreaPassageCache.{certified}
public import PlasmaLean.Design.DommaschkFirstMirrorHeightSampling

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch DommaschkEndpointTraceFamily Certificates.PositionFrameSlabs
open DommaschkFirstMirrorHeightSampling DommaschkFirstMirrorLaunchSign
set_option maxRecDepth 65536
set_option linter.style.longLine false

theorem probability_from_passage {{c : Checkpoint}} {{uC zC uA zA : Theory.KAM.FA}} {{φ : ℝ}}
    {{F B : List Step}} (path : c.Passage .{label} uC zC uA zA φ)
    (angle : |φ - azimuth (MirrorEndpoint.opposite .{label})| ≤ 1 / 64)
    (fl : c.forwardRows.length = c.length) (bl : c.backwardRows.length = c.length)
    (f : c.forwardRows = {stem}Fwd.rows ++ F) (b : c.backwardRows = {stem}Back.rows ++ B) :
    Birth .{label} c {k} {n-1} {l} {m-1} uC zC uA zA φ
      ({probability.numerator} / {probability.denominator}) := by
  have hit := {certified}.from_original_passage path angle fl bl f b
  have rate : bracketRate ({k} / 64) (({n-1} + 1) / 64) ({l} / 64) (({m-1} + 1) / 64) =
      {probability.numerator} / {probability.denominator} := by norm_num [bracketRate,height]
  rw [← rate]
  apply of_launch_width hit _ _ fl bl
  · rw [f]
    exact {stem}Sides.fwd F
  · rw [b]
    exact {stem}Sides.back B

end PlasmaLean.Design.{name}
'''
    return (name, src, ['probability_from_passage']), roots, parent, probability


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--area',type=Path,required=True)
    p.add_argument('--from-passage', action='store_true',
                   help='prove the bracket-specific implication conditional on an original passage')
    p.add_argument('--cache',type=Path,default=ROOT/'.lake/physical-mirror-height-sampling')
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    origin=json.loads(a.area.read_text())
    if a.from_passage:
        item, roots, parent, rate = from_ordered_passage(origin)
        env(a)
        keys = [a.version, parent['key'], origin['packet_sha256'],
                digest(DESIGN/'DommaschkFirstMirrorHeightSampling.trace')]
        dest, rec = compile_modules(a.cache/item[0], [item], roots, keys, a, 'PhysicalMirrorSamplingCache')
        result = {k: v for k, v in rec.items() if k != 'artifacts'}
        result.update(endpoint=origin['endpoint'], passage=parent['key'], original_birth=False,
                      uniform_fraction=str(rate), brackets=origin['brackets'],
                      import_paths=list(map(str, [dest, *roots])))
        save(a.output, result)
        print(item[0], rec['key'])
        return
    if not origin['original_birth']:
        p.error('a verified trajectory through the original birth and exterior mirror caps is required')
    record=origin['physical']
    label=origin['endpoint']
    if label not in ENDPOINTS:
        p.error('unknown physical launch label')
    match=re.fullmatch('DommaschkFirstMirrorArea'+label.upper()+r'On([0-9]+(?:_[0-9]+){7})',record['module'])
    if not match:
        p.error('the signed area theorem does not belong to this endpoint family')
    (k,n),(l,m)=origin['brackets']
    counts=list(map(int,match[1].split('_')))
    if not (0<k<n<=counts[ENDPOINTS.index(label)] and 0<l<m<=counts[ENDPOINTS.index(label)]):
        p.error('the physical signed line does not cover its claimed brackets')
    roots=list(map(Path,record['import_paths']))
    marker=admitted(roots[0],record['module'],record['key'])
    if f"PlasmaLean.Design.{record['module']}.from_common_tori" not in marker['theorems']:
        p.error('missing the original torus birth theorem')
    env(a)
    name='DommaschkFirstMirrorSampling'+label.upper()+'On'+match[1]
    family='DommaschkCommonEndpointTraces'+match[1]
    src=f'''module
public import FirstMirrorAreaFamilyCache.{record['module']}
public import PlasmaLean.Design.DommaschkFirstMirrorHeightSampling

@[expose] public section
noncomputable section
namespace PlasmaLean.Design.{name}
open DommaschkMirrorLaunch DommaschkFirstMirrorHeightSampling
open DommaschkKamC KamNewton Contract Forms Fields.VacuumBoozer Theory.KAM WEll1Z2
open {family} (checkpoint)
set_option maxRecDepth 65536
set_option linter.style.longLine false

theorem original_birth_probability :
    ∃ (uC zC uA zA : FA) (R₀ z₀ : ℝ → ℝ) (ΘC ΘA : ℝ → ℝ → ℝ),
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uC) (Zof zC) DommaschkKamDio.dkIotaC ∧
      IotaOnTorus (DommaschkQA2R.field DommaschkQA2R.candidate) (RofC uA) (Zof zA) DommaschkKamDio.dkIotaA ∧
      DommaschkKamNested.NestedTori (RofC uC) (Zof zC) (RofC uA) (Zof zA) R₀ z₀ ΘC ΘA ∧
      EmbeddedTorus (RofC uC) (Zof zC) ∧ EmbeddedTorus (RofC uA) (Zof zA) ∧
      ∀ φ : ℝ, |φ-azimuth (MirrorEndpoint.opposite .{label})| ≤ MirrorEndpoint.width .{label} →
        Birth .{label} (checkpoint .{label}) {k} {n-1} {l} {m-1} uC zC uA zA φ := by
  obtain ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,actual⟩ := {record['module']}.from_common_tori
  exact ⟨uC,zC,uA,zA,R,Z,C,A,ic,ia,nested,ec,ea,fun φ small => of_launch (actual φ small)⟩

end PlasmaLean.Design.{name}
'''
    item=name,src,['original_birth_probability']
    keys=[a.version,record['key'],origin['packet_sha256'],digest(DESIGN/'DommaschkFirstMirrorHeightSampling.trace')]
    dest,rec=compile_modules(a.cache/name,[item],roots,keys,a,'PhysicalMirrorSamplingCache')
    result={k:v for k,v in rec.items() if k!='artifacts'}
    result.update(endpoint=label,physical_area=record['key'],brackets=origin['brackets'],
                  original_birth=True, uniform_fraction='667367655761/1292367655761',
                  import_paths=list(map(str,[dest,*roots])))
    save(a.output,result)
    print(name,rec['key'])


if __name__=='__main__':
    main()
