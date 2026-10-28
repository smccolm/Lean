from pathlib import Path
import json
p=Path(__file__).parent
src=(p/'SourceParabolicBinaryRationalSpan.lean').read_text(encoding='utf-8')
start=src.index('private theorem cocycle_ext_generators')
finish=src.index('/-- Rational parabolic cocycles')
helpers=src[start:finish]
oldbody=src[src.index('  classical',finish):src.rindex('\n\n\nend')]
tail=oldbody.index('  exact Submodule.sum_mem')
body=oldbody[:tail]
header='''import SourceParabolicIntegralCoordinateSpan
import SourceOriginalBinaryCuspWitnesses

/-! DUB17/18 -> original all-weight association -> original integral
parabolic Hecke character. The original period cocycle is reconstructed
from finitely many actual rational coordinates. Their whole-cusp witnesses
give integral parabolic denominators. Reconstruction helpers are reused
verbatim from the already checked local rational-span proof. -/
namespace Dubon2026
noncomputable section
open MvPolynomial Matrix.SpecialLinearGroup CongruenceSubgroup groupCohomology
open scoped MatrixGroups

'''
statement=json.loads(r'"theorem sourceComplexCuspBinaryCocycle_mem_integralParabolic_span\n    (Q w : \u2115) [NeZero Q]\n    (c : cocycles\u2081 (sourceBinaryCoefficientRep \u2102 Q w))\n    (hc : \u2200 \u03b2 : OnePoint \u211a, \u2203 v : sourceBinaryCoefficientRep \u2102 Q w,\n      \u2200 \u03b3 : Gamma0 Q, mapGL \u211a \u03b3.val \u2022 \u03b2 = \u03b2 \u2192\n        c \u03b3 = (sourceBinaryCoefficientRep \u2102 Q w).\u03c1 \u03b3 v - v) :\n    c \u2208 Submodule.span \u2102 (sourceBinaryCocyclesChange (Int.castRingHom \u2102) Q w \u0027\u0027\n      (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep \u2124 Q w) :\n        Set (cocycles\u2081 (sourceBinaryCoefficientRep \u2124 Q w)))) := by\n"')
ending='''  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (sourceRationalCuspBinaryCocycle_mem_integralParabolic_span Q w _
      (sourceBinaryAdditiveCocycles_cusp_witnesses (sourceComplexRationalCoordinate i) Q w c hc))

'''
consumer=json.loads(r'"theorem sourceOriginalBinaryPeriodCocycle_mem_integralParabolic_span\n    (Q : \u2115) [NeZero Q] (k : \u2124) (hk : 2 \u2264 k)\n    (f : CuspForm ((Gamma0 Q).map (mapGL \u211d)) k) :\n    sourceOriginalBinaryPeriodCocycle Q k hk f \u2208\n      Submodule.span \u2102 (sourceBinaryCocyclesChange (Int.castRingHom \u2102) Q (k - 2).toNat \u0027\u0027\n        (sourceParabolicCocycles (Gamma0 Q) (sourceBinaryCoefficientRep \u2124 Q (k - 2).toNat) :\n          Set (cocycles\u2081 (sourceBinaryCoefficientRep \u2124 Q (k - 2).toNat)))) :=\n  sourceComplexCuspBinaryCocycle_mem_integralParabolic_span Q (k - 2).toNat _\n    (sourceOriginalBinaryPeriodCocycle_cusp_witnesses Q k hk f)\n\nend\nend Dubon2026\n"')
f=p/'SourceOriginalIntegralParabolicCocycleSpan.lean'
assert not f.exists()
f.write_text(header+helpers+statement+body+ending+consumer,encoding='utf-8')
print(f)
