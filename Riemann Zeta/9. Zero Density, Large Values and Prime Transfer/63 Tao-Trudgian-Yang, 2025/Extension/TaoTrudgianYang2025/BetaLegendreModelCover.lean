import TaoTrudgianYang2025.BetaLegendreFamily

/-!
# Simultaneous source model families on the finite canonical cover

The cover is selected before the source family. The original model-family
hypothesis then supplies a model family on every chart, with one eventual
index condition for all charts and every point of each retained interval.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

theorem modelPhaseLegendreDual_finite_model_family
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1) :
    ∃ S : Finset (Icc a b), S.Nonempty ∧
      ∃ l r A : Icc a b → ℝ, ∃ χ : Icc a b → ℝ → ℝ,
      (∀ i ∈ S, (2 : ℝ)^(-σ) < l i ∧ l i ≤ r i ∧ r i < 1 ∧
        0 < A i ∧ A i < l i ∧ r i < 2*A i ∧
        ContDiff ℝ ∞ (χ i) ∧ HasCompactSupport (χ i) ∧
        ∀ v ∈ Icc (l i) (r i), χ i v = 1) ∧
      (∀ v ∈ Icc a b, ∃ i ∈ S, v ∈ Ioo (l i) (r i)) ∧
      ∀ F : VariableFunction (VariableObject.fixed ℝ) ℝ,
        IsModelPhaseFunctionWith F σ →
      ∃ G : S → VariableFunction (VariableObject.fixed ℝ) ℝ,
        (∀ j, IsModelPhaseFunctionWith (G j) σ⁻¹ ∧ IsModelPhaseFunction (G j)) ∧
        ∀ᶠ n in atTop, ∀ j : S,
          G j n = canonicalLegendrePhase (χ j) (F n) σ (A j) (l j) ∧
          Icc (l j) (r j) ⊆ modelPhaseSlopeRange (F n) ∧
          ∀ v ∈ Icc (l j) (r j), v/A j ∈ Ioo (1 : ℝ) 2 ∧
            G j n (v/A j) =
              (A j)^(σ⁻¹-1)*
                (modelPhaseLegendreDual (F n) v-modelPhaseLegendreDual (F n) (l j)) +
                referenceModelPrimitive σ⁻¹ (l j/A j) := by
  classical
  obtain ⟨S,hS,l,r,A,χ,hgeom,hcover,huniform⟩ :=
    modelPhaseLegendreDual_finite_canonical_cover hσ ha hab hb
  refine ⟨S,hS,l,r,A,χ,hgeom,hcover,?_⟩
  intro F hF
  have he (j : S) : ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop, IsApproximateModelPhaseFunction
        (canonicalLegendrePhase (χ j) (F n) σ (A j) (l j)) σ⁻¹ Q ε := by
    intro Q ε hε
    obtain ⟨δ,hδ,_,hall⟩ := huniform Q ε hε
    filter_upwards [hF.eventually_isApproximate (legendreFiniteInputOrder (Q+1)) hδ]
      with n hn
    exact (hall (F n) hn j j.property).2.1
  choose G hG heq using fun j : S => modelPhaseWith_finite_initial_repair σ⁻¹ (he j)
  refine ⟨G,fun j => ⟨hG j,(hG j).isModelPhaseFunction (inv_pos.mpr hσ)⟩,?_⟩
  have heqall : ∀ᶠ n in atTop, ∀ j : S,
      G j n = canonicalLegendrePhase (χ j) (F n) σ (A j) (l j) :=
    Filter.eventually_all.mpr heq
  obtain ⟨δ,hδ,_,hall⟩ := huniform 0 1 zero_lt_one
  filter_upwards [heqall,hF.eventually_isApproximate (legendreFiniteInputOrder (0+1)) hδ]
    with n hn happrox
  intro j
  obtain ⟨hJ,_,hvalues⟩ := hall (F n) happrox j j.property
  exact ⟨hn j,hJ,fun v hv => ⟨(hvalues v hv).1,
    by rw [hn j]; exact (hvalues v hv).2⟩⟩

end TaoTrudgianYang2025
