import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import P2M.Util
namespace P2MW.S_AlgebraicCurve_Place_ord_natCast

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord_algebraMap"
namespace FF2S
p2m_open "AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_natCast (v : Place K F) (n : ℕ) : v.ord (n : F) = 0 := by
  rw [show (n : F) = algebraMap K F n by simp]
  exact v.ord_algebraMap n

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (n : ℕ) :
    v.ord (n : F) = 0 :=
  AlgebraicCurve.FF2S.ord_natCast v n
