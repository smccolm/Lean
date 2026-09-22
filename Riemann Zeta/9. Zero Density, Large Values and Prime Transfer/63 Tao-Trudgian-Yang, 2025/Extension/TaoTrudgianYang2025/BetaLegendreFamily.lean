import TaoTrudgianYang2025.BetaLegendreCover

/-!
# The source variable-family model predicate for canonical dual phases

The finite-order extension theorem is consumed by the original ANTEDB
choicewise-infinitesimal predicate. A finite initial segment may be replaced
by the exact reference primitive so that every family member is smooth.
The actual canonical Legendre formula holds eventually, uniformly in u.
-/

noncomputable section

open Set Expdb Filter
open scoped Topology ContDiff

namespace TaoTrudgianYang2025

theorem modelPhaseWith_of_eventual_approximation
    {G : VariableFunction (VariableObject.fixed ℝ) ℝ} {s : ℝ}
    (hG : IsPhaseFunction G)
    (he : ∀ (P : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in atTop, IsApproximateModelPhaseFunction (G i) s P ε) :
    IsModelPhaseFunctionWith G s := by
  refine ⟨hG,?_⟩
  intro p
  apply (VariableFunction.isChoicewiseInfinitesimal_iff_forall_pos_uniform
    (VariableObject.fixed phaseInterval)
    (fun _ => ⟨1,by simp [phaseInterval]⟩) (modelPhaseError G s p)).mpr
  intro ε hε
  filter_upwards [he p (ε/2) (by linarith)] with i hi
  intro u
  exact ((hi.2 p le_rfl u).trans_lt (by linarith))

theorem modelPhaseWith_finite_initial_repair
    {H : VariableFunction (VariableObject.fixed ℝ) ℝ} (s : ℝ)
    (he : ∀ (P : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in atTop, IsApproximateModelPhaseFunction (H i) s P ε) :
    ∃ G : VariableFunction (VariableObject.fixed ℝ) ℝ,
      IsModelPhaseFunctionWith G s ∧ (∀ᶠ i : ℕ in atTop, G i = H i) := by
  classical
  let G : VariableFunction (VariableObject.fixed ℝ) ℝ := fun i =>
    if IsApproximateModelPhaseFunction (H i) s 0 1 then H i
    else referenceModelPrimitive s
  have heq : ∀ᶠ i : ℕ in atTop, G i = H i := by
    filter_upwards [he 0 1 zero_lt_one] with i hi
    simp only [G,if_pos hi]
  refine ⟨G,modelPhaseWith_of_eventual_approximation ?_ ?_,heq⟩
  · intro i
    dsimp [G]
    split_ifs with hi
    · exact hi.1
    · exact (referenceModelPrimitive_approximate s 0).1
  · intro P ε hε
    filter_upwards [heq,he P ε hε] with i hi happrox
    rwa [hi]

theorem modelPhaseLegendreDual_canonical_family
    {σ a b : ℝ} (hσ : 0 < σ)
    (ha : (2 : ℝ)^(-σ) < a) (hab : a ≤ b) (hb : b < 1)
    (hr : b < 2*a)
    {F : VariableFunction (VariableObject.fixed ℝ) ℝ}
    (hF : IsModelPhaseFunctionWith F σ) :
    ∃ A : ℝ, 0 < A ∧ A < a ∧ b < 2*A ∧
      ∃ χ : ℝ → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∃ G : VariableFunction (VariableObject.fixed ℝ) ℝ,
        IsModelPhaseFunctionWith G σ⁻¹ ∧ IsModelPhaseFunction G ∧
        ∀ᶠ i in atTop,
          G i = canonicalLegendrePhase χ (F i) σ A a ∧
          Icc a b ⊆ modelPhaseSlopeRange (F i) ∧
          ∀ v ∈ Icc a b, v/A ∈ Ioo (1 : ℝ) 2 ∧
            G i (v/A) =
              A^(σ⁻¹-1)*(modelPhaseLegendreDual (F i) v-modelPhaseLegendreDual (F i) a) +
                referenceModelPrimitive σ⁻¹ (a/A) := by
  obtain ⟨A,hA,hAa,hbA,χ,hχ,hcompact,_,huniform⟩ :=
    modelPhaseLegendreDual_canonical_extension hσ ha hab hb hr
  have he : ∀ (Q : ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in atTop, IsApproximateModelPhaseFunction
        (canonicalLegendrePhase χ (F i) σ A a) σ⁻¹ Q ε := by
    intro Q ε hε
    obtain ⟨δ,hδ,_,hall⟩ := huniform Q ε hε
    filter_upwards [hF.eventually_isApproximate (legendreFiniteInputOrder (Q+1)) hδ]
      with i hi
    exact (hall (F i) hi).2.1
  obtain ⟨G,hG,heq⟩ := modelPhaseWith_finite_initial_repair σ⁻¹ he
  refine ⟨A,hA,hAa,hbA,χ,hχ,hcompact,G,hG,
    hG.isModelPhaseFunction (inv_pos.mpr hσ),?_⟩
  obtain ⟨δ,hδ,_,hall⟩ := huniform 0 1 zero_lt_one
  filter_upwards [heq,hF.eventually_isApproximate (legendreFiniteInputOrder (0+1)) hδ]
    with i hi happrox
  obtain ⟨hJ,_,hvalues⟩ := hall (F i) happrox
  exact ⟨hi,hJ,fun v hv => ⟨(hvalues v hv).1,by rw [hi]; exact (hvalues v hv).2⟩⟩

end TaoTrudgianYang2025
