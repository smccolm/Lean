import Mathlib
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import P2M.Util
namespace P2MW.S_AlgebraicCurve_residueTheorem_of_residueTheoremK

set_option maxHeartbeats 3200000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.ResidueTheorem K F := by
  intro _hPD ω hω f
  have key := h (fun v => HasCanonicalLocalResidueKStar.dataKStar v) hω f
  rw [weilOfKaehlerK_apply] at key
  rw [weilOfKaehler_apply]
  exact key
