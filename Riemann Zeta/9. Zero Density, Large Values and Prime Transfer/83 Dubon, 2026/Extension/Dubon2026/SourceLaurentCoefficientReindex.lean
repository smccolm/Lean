import Dubon2026.SourceLaurentReindex


/-! DUB-17/18 -> cusp-form lower dimension bound -> original regular
differential realization -> finite function-field extension -> monic relations.
This is the literal finite conjugate product and its coefficient descent.
SourcePrimeCoefficientPolynomialDescent proves analytic invariance and
polynomial descent, and SourcePrimeMonicRelation assembles the monic relation.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_coeffMap_qExpand.lean; original coefficient embedding compatibility.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries HahnSeries Polynomial

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk,
      qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffMap_coeffEmb {K : Type*} [Field K] [Algebra ℚ K]
    (σ : K ≃ₐ[ℚ] K) (x : LaurentSeries ℚ) :
    coeffMap (σ : K →+* K) (coeffEmb K x) = coeffEmb K x := by
  ext m
  rw [coeffMap_coeff, coeffEmb_coeff]
  exact σ.commutes (x.coeff m)

end
end Dubon2026.SourceFunctionField
