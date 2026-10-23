import Dubon2026.SourceLaurentRootTwist

/-! DUB-17/18 -> good reduction -> exact residue-field degree -> prime
j nonmembership -> discriminant norm. This computes the actual twist of
the discriminant's leading q monomial and of coefficient constants. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem qTwist_single {R : Type*} [CommRing R] (u : Rˣ) (g : ℤ) (r : R) :
    qTwist u (HahnSeries.single g r) = HahnSeries.single g ((u ^ g : Rˣ) * r) := by
  ext k
  rw [qTwist_coeff]
  by_cases hk : k = g
  · subst k
    rw [HahnSeries.coeff_single_same, HahnSeries.coeff_single_same]
  · rw [HahnSeries.coeff_single_of_ne hk, HahnSeries.coeff_single_of_ne hk, mul_zero]

end
end Dubon2026.SourceFunctionField
