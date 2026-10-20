import Dubon2026.CMFiniteAdelicIntegralClassFiniteness
import Dubon2026.DoubleCosetFiniteOpenRefinement

/-! # Finiteness of the original definite unitary arithmetic classes at every open level

The actual integral unitary level is compact and has a proved finite
arithmetic double-coset quotient. The native finite-index theorem now
passes this to every original open subgroup, including the source's
prescribed local refinements. This removes arithmetic class finiteness
as an assumption from DUB-17's original auxiliary-module comparison.
-/

namespace Dubon2026

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual definite CM unitary arithmetic double-coset quotient is finite for every original open level. -/
theorem cmFiniteAdelicDoubleCoset_finite (H : Matrix ι ι K)
    (hH : ∀ φ : K →+* ℂ, (φ.mapMatrix H).PosDef)
    (U : Subgroup (cmFiniteAdelicUnitaryGroup K H))
    (hU : IsOpen (U : Set (cmFiniteAdelicUnitaryGroup K H))) :
    Finite (DoubleCoset.Quotient (G := cmFiniteAdelicUnitaryGroup K H)
      ((cmHermitianFiniteAdeleHom H).codRestrict (cmFiniteAdelicUnitaryGroup K H)
        (cmFiniteAdelicUnitaryGroup_principal K H)).range U) := by
  letI := cmFiniteAdelicIntegralDoubleCoset_finite K H hH
  exact doubleCoset_finite_of_compact_level _ (cmFiniteAdelicIntegralLevel K H) U
    (cmFiniteAdelicIntegralLevel_isCompact K H) hU

end
end Dubon2026
