import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_ord_add_eq_of_lt

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f :=
  AlgebraicCurve.FF2S.ord_add_eq_of_lt v hf hg h
