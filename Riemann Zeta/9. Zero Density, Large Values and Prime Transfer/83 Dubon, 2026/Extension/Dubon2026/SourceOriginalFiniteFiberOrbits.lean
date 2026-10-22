import Dubon2026.SourceOriginalFinitePlaceExhaustion
import Dubon2026.SourceAnalyticJOrbitSeparation

/-! DUB-17/18 -> numerical modular genus -> finite ramification fibers.
The actual original finite places are now realized by translates of any
chosen upper-half-plane point with their j-value. This composes proved
finite-place exhaustion with analytic j-orbit separation. The finer
Gamma0 orbit relation and normalized ramification remain to be proved.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem originalAnalyticPlace_eq_implies_full_orbit (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (h : originalAnalyticPlace N τ = originalAnalyticPlace N τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by
  apply JOrbitSeparation.exists_smul_eq_of_j_eq
  apply (originalAnalyticPlace_j_value N τ' _).mp
  rw [← h]
  exact originalAnalyticPlace_j_sub_pos N τ

theorem original_finite_fiber_full_orbit (N : ℕ) [NeZero N]
    (P : SourceCurve.Place ℂ (modularFunctionFieldOver N ℂ)) (τ : ℍ)
    (hP : 0 < P.ord (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ))) :
    ∃ γ : SL(2, ℤ), originalAnalyticPlace N (γ • τ) = P := by
  obtain ⟨τ', hτ', hj⟩ := original_finite_fiber_realization N P _ hP
  obtain ⟨γ, hγ⟩ := JOrbitSeparation.exists_smul_eq_of_j_eq τ τ' hj.symm
  refine ⟨γ, ?_⟩
  rw [hγ]
  exact hτ'

end
end Dubon2026.SourceFunctionField
