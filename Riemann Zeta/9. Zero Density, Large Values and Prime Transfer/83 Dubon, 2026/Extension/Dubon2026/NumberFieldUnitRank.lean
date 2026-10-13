import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite

/-! # Ordinary-unit rank on the pinned toolchain

Finite roots of unity have rank zero, so the pinned Dirichlet theorem for
the quotient gives the original unit rank. This feeds the already proved
S-unit valuation kernel and the global norm-index dependency of DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

/-- The original ordinary units have the Dirichlet rank; finite torsion contributes zero. -/
theorem numberField_unit_finrank (K : Type*) [Field K] [NumberField K] :
    Module.finrank ℤ (Additive (𝓞 K)ˣ) = NumberField.Units.rank K := by
  classical
  letI : CommGroup ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    QuotientGroup.Quotient.commGroup _
  let f : Additive (𝓞 K)ˣ →ₗ[ℤ]
      Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K) :=
    (QuotientGroup.mk' (NumberField.Units.torsion K)).toAdditive.toIntLinearMap
  haveI : Finite f.ker := by
    dsimp [f]
    rw [QuotientGroup.ker_mk']
    exact (inferInstance : Finite (Additive (NumberField.Units.torsion K)))
  have hz : Module.rank ℤ f.ker = 0 :=
    rank_eq_zero_iff_isTorsion.mpr
      (AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite)
  have h := LinearMap.rank_eq_of_surjective (f := f)
    (QuotientGroup.mk'_surjective (NumberField.Units.torsion K))
  rw [hz, add_zero] at h
  exact (congrArg Cardinal.toNat h).trans (NumberField.Units.rank_modTorsion K)

end
end Dubon2026
