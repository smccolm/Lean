import Dubon2026.SourceOriginalWeilCoverDisc
import Dubon2026.SourceCurveConvergentPlaceFamily

/-! DUB-17/18 -> original Weil nondegeneracy -> auxiliary Kummer point division.
The literal torsion-cover common disk supplies a family of actual normalized
cover places centered at every specified place. The meromorphic functions
retain their exact Laurent representations in the original local extension.
Injectivity, overlap compatibility, global Abel comparison and division remain open. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve CuspTaylor Polynomial Metric SourceCurve.AnalyticDisc
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (f : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (X ^ n - C f : FF[X])

local instance coverFamilyIntegral : Algebra.IsIntegral FF EE := Place.kummerIntegral n f

theorem exists_originalWeil_cover_place_family
    (D : Divisor ℂ FF) (hf : f ≠ 0)
    (hfD : ∀ v : Place ℂ FF, v.ord f = (n : ℤ) * D v) (w : Place ℂ EE) :
    ∃ (e : EE →ₐ[ℂ] realizedField) (R : ℝ) (G : EE → ℂ → ℂ)
      (δ : ℝ) (γ : ℂ → Place ℂ EE), 0 < R ∧ 0 < δ ∧ γ 0 = w ∧
      (∀ g : FF, e (algebraMap FF EE g) = chartLaurentHom N (w.restrict FF) g) ∧
      (∀ a, MeromorphicOn (G a) (ball 0 R) ∧ Represents (e a).val (G a)) ∧
      ∀ z ∈ ball 0 δ, z ∈ ball 0 R ∧
        (∀ a, a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z) ∧
        (∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ)) ∧
        AnalyticAt ℂ (normal R G w.uniformizer) z ∧
        deriv (normal R G w.uniformizer) z ≠ 0 := by
  obtain ⟨e, R, hR, he, hex⟩ := exists_originalWeil_cover_common_disc N n f D hf hfD w
  have hG : ∀ a : EE, ∃ H : ℂ → ℂ, MeromorphicOn H (ball 0 R) ∧
      Represents (e a).val H ∧
      (a ≠ 0 → meromorphicOrderAt H 0 = (w.ord a : WithTop ℤ)) := by
    intro a
    obtain ⟨H, hm, hr, ho, _⟩ := hex a
    exact ⟨H, hm, hr, ho⟩
  obtain ⟨G, δ, γ, hδ, hγ, hm, hall⟩ := exists_place_family_of_common_disc e hR w hG
  exact ⟨e, R, G, δ, γ, hR, hδ, hγ, he, hm, hall⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
