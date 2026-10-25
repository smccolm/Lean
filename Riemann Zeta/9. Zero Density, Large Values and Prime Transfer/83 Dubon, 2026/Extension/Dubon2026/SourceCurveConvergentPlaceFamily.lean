import Dubon2026.SourceCurveConvergentDiscPlaces

/-! DUB-17/18 -> auxiliary cover analytic charts -> assemble actual disk functions.
Select the already proved meromorphic representatives and consume the
normalized-place family construction. The retained Laurent representations
connect every chosen function to the specified convergent field embedding. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open SourceFunctionField.CuspTaylor Filter Metric
open scoped Topology

theorem exists_place_family_of_common_disc {E : Type*} [Field E] [Algebra ℂ E]
    (e : E →ₐ[ℂ] realizedField) {R : ℝ} (hR : 0 < R) (w : Place ℂ E)
    (hex : ∀ a : E, ∃ G : ℂ → ℂ, MeromorphicOn G (ball 0 R) ∧
      Represents (e a).val G ∧
      (a ≠ 0 → meromorphicOrderAt G 0 = (w.ord a : WithTop ℤ))) :
    ∃ (G : E → ℂ → ℂ) (δ : ℝ) (γ : ℂ → Place ℂ E), 0 < δ ∧ γ 0 = w ∧
      (∀ a, MeromorphicOn (G a) (ball 0 R) ∧ Represents (e a).val (G a)) ∧
      ∀ z ∈ ball 0 δ, z ∈ ball 0 R ∧
        (∀ a, a ∈ (γ z).toValuationSubring ↔ 0 ≤ meromorphicOrderAt (G a) z) ∧
        (∀ a, a ≠ 0 → meromorphicOrderAt (G a) z = ((γ z).ord a : WithTop ℤ)) ∧
        AnalyticAt ℂ (normal R G w.uniformizer) z ∧
        deriv (normal R G w.uniformizer) z ≠ 0 := by
  classical
  choose G hm hr ho using hex
  obtain ⟨δ, γ, hδ, hγ, hall⟩ := exists_place_family e hR G hm hr w ho
  exact ⟨G, δ, γ, hδ, hγ, fun a => ⟨hm a, hr a⟩, hall⟩

end
end Dubon2026.SourceCurve.AnalyticDisc
