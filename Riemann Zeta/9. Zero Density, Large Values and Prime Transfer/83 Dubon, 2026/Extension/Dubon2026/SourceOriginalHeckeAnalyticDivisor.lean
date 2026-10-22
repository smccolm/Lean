import Dubon2026.SourceOriginalHeckeCosetMultiplicity
import Dubon2026.SourceOriginalHeckeFiniteFiber
import Dubon2026.SourceOriginalHeckeAlphaPlaces
import Dubon2026.SourceOriginalHeckePicard

/-! DUB-17/18 -> original Picard-period Hecke comparison -> exact
analytic divisor formula. Analytic fiber exhaustion and the proved
ramification count identify the literal beta pullback with the quotient
coset sum. Alpha pushforward then gives the actual Hecke divisor operator.
No unramified-point restriction or abstract place dictionary is assumed.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve CongruenceSubgroup
open scoped MatrixGroups
variable (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]

private local instance : Fintype (Gamma0 N ⧸ heckeUpperSubgroup N ℓ) :=
  sourceHeckeUpperFintype N ℓ

theorem originalHeckeBeta_pullback_single_analytic (τ : ℍ) :
    Divisor.finitePullbackAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
        (Finsupp.single (originalAnalyticPlace N τ) 1) =
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ,
        Finsupp.single (originalAnalyticPlace (N * ℓ) (originalHeckeCosetPoint N ℓ τ q)) 1 := by
  classical
  ext W
  rw [Divisor.finitePullbackAlong_apply, Finset.sum_apply']
  by_cases hW : Place.restrictAlong (originalHeckeBeta ℂ N ℓ)
      (originalHeckeBeta_finite ℂ N ℓ) W = originalAnalyticPlace N τ
  · rw [hW, Finsupp.single_eq_same, one_mul]
    obtain ⟨w, rfl⟩ := exists_original_analytic_place_of_restrict_heckeBeta N ℓ W τ hW
    have he : originalAnalyticPlace N (levelRaiseMatrix ℓ • w) = originalAnalyticPlace N τ := by
      rw [← originalAnalyticPlace_restrict_heckeBeta N ℓ w]
      exact hW
    obtain ⟨g₀, hg₀⟩ := (originalAnalyticPlace_eq_iff_gamma0_orbit N τ
      (levelRaiseMatrix ℓ • w)).mp he.symm
    rw [originalHeckeBeta_ramification_eq_coset_card N ℓ τ w g₀ hg₀]
    simp only [Finsupp.single_apply, Finset.sum_boole]
  · rw [Finsupp.single_eq_of_ne hW, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro q _
    apply Finsupp.single_eq_of_ne
    intro hq
    apply hW
    rw [hq]
    exact originalHeckeCosetPoint_restrict_beta N ℓ τ q

theorem originalHeckeDivisor_single_analytic_cosets (τ : ℍ) :
    originalHeckeDivisor ℂ N ℓ (Finsupp.single (originalAnalyticPlace N τ) 1) =
      ∑ q : Gamma0 N ⧸ heckeUpperSubgroup N ℓ,
        Finsupp.single (originalAnalyticPlace N (originalHeckeCosetPoint N ℓ τ q)) 1 := by
  change Divisor.geometricPushforwardAlong (originalHeckeAlpha ℂ N ℓ)
    (originalHeckeAlpha_finite ℂ N ℓ)
    (Divisor.finitePullbackAlong (originalHeckeBeta ℂ N ℓ) (originalHeckeBeta_finite ℂ N ℓ)
      (Finsupp.single (originalAnalyticPlace N τ) 1)) = _
  rw [originalHeckeBeta_pullback_single_analytic, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Divisor.geometricPushforwardAlong_single, originalAnalyticPlace_restrict_heckeAlpha]

end
end Dubon2026.SourceFunctionField
