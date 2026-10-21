import Dubon2026.SourceCurvePlaceRestriction
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-! DUB-17/18 -> regular differential dimension -> Riemann--Roch inputs.
Divisors are actual finite integer sums of places, and degree uses the actual
residue-field dimensions. The curve interface follows the selected definitions
in anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Def_AlgebraicCurve_DivisorClassGroup
and Def_AlgebraicCurve_IsCurveOver. Its original-field instance is proved in
SourceOriginalPrincipalDivisors, rather than supplied as an assumption there.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- A finite integer combination of actual places. -/
abbrev Divisor := Place K F →₀ ℤ

namespace Divisor
variable {K F}

/-- Degree weights each actual place by its residue degree over the constants. -/
def degree : Divisor K F →+ ℤ :=
  Finsupp.liftAddHom fun v => AddMonoidHom.mulRight (Module.finrank K v.ResidueField : ℤ)

theorem degree_eq_finsum (D : Divisor K F) :
    degree D = ∑ᶠ v : Place K F, D v * (Module.finrank K v.ResidueField : ℤ) := by
  classical
  rw [finsum_eq_finsetSum_of_support_subset _ (s := D.support) (by
    intro v hv
    exact Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul hv))]
  rfl

end Divisor

/-- The principal-divisor existence and degree-zero property. -/
class HasPrincipalDivisors : Prop where
  /-- Each nonzero function gives its literal normalized-order divisor of degree zero. -/
  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,
    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0

/-- The source curve interface needed by regular-differential dimension theory. -/
class IsCurveOver : Prop extends HasPrincipalDivisors K F where
  /-- Actual places have finite residue degree. -/
  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField
  /-- Actual relative differentials form a free vector space of dimension one. -/
  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

end
end Dubon2026.SourceCurve
