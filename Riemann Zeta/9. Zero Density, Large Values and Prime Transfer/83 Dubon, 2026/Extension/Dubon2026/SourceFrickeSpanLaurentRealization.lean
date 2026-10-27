import Dubon2026.SourceFrickeCoefficientTwist

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> preservation of cusp conditions under coefficient twists. Finite sums of
actual cyclotomic Fricke fractions have literal Laurent cusp expansions.
Twisting the finite complex coefficients maps that Laurent expansion
coefficientwise, while holomorphy and periodicity remain proved on the actual
function span. No continuity of an arbitrary complex field automorphism is
required or asserted. -/
namespace Dubon2026.SourceFricke
noncomputable section
open Module UpperHalfPlane SourceFunctionField
open scoped Manifold

theorem frickeSpan_holomorphic {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) : MDiff F := by
  induction hF using Submodule.span_induction with
  | mem f hf => exact hf.1
  | zero => exact mdifferentiable_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact MDifferentiable.const_smul c hf

theorem frickeSpan_periodic {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hF : F ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    Function.Periodic (F ∘ ofComplex) N := by
  induction hF using Submodule.span_induction with
  | mem f hf => exact holomorphicCyclotomicFrickeFractions_periodic hf
  | zero => intro z; rfl
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf =>
    intro z
    exact congrArg (fun w : ℂ => c * w) (hf z)

theorem coeffMap_cyclotomic_scalar_sum (N : ℕ) (σ : ℂ ≃ₐ[kN N] ℂ)
    {ι : Type} (s : Finset ι) (c : ι → ℂ) (A : ι → LaurentSeries (kN N)) :
    coeffMap σ.toRingHom (∑ i ∈ s, c i • coeffMap (algebraMap (kN N) ℂ) (A i)) =
      ∑ i ∈ s, σ (c i) • coeffMap (algebraMap (kN N) ℂ) (A i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext n
  simp only [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul]
  change σ (c i) * σ (algebraMap (kN N) ℂ ((A i).coeff n)) = _
  rw [σ.commutes]

theorem exists_fricke_twist_laurent (N : ℕ) [NeZero N] (σ : ℂ ≃ₐ[kN N] ℂ)
    (F : Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    ∃ A : LaurentSeries ℂ,
      CuspTaylor.Represents A (cuspFunction N (F : ℍ → ℂ)) ∧
      CuspTaylor.Represents (coeffMap σ.toRingHom A)
        (cuspFunction N (frickeCoefficientTwist N σ F : ℍ → ℂ)) := by
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.mp F.property
  let G : Fin n → (cyclotomicHolomorphicFrickeAlgebra N).toSubmodule :=
    fun i => ⟨g i, (g i).property⟩
  have hr : ∀ i, ∃ X : LaurentSeries (kN N),
      CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) X) (cuspFunction N (G i : ℍ → ℂ)) := by
    intro i
    obtain ⟨_, a, ha, b, hb, hb0, he⟩ := (g i).property
    exact exists_cyclotomic_fraction_represents ha hb hb0 he
  choose X hX using hr
  have hsum : (∑ i, c i • cyclotomicFrickeSpanInclusion N (G i)) = F := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hg
  have hfun : (∑ i, c i • (G i : ℍ → ℂ)) = (F : ℍ → ℂ) := hg
  have hrep := CuspTaylor.Represents.cusp_smul_sum Finset.univ c (fun i _ => hX i)
  rw [hfun] at hrep
  refine ⟨∑ i, c i • coeffMap (algebraMap (kN N) ℂ) (X i), hrep, ?_⟩
  rw [coeffMap_cyclotomic_scalar_sum]
  have htw := frickeCoefficientTwist_sum_original N σ Finset.univ c G
  rw [hsum] at htw
  have ht := CuspTaylor.Represents.cusp_smul_sum Finset.univ (fun i => σ (c i))
    (fun i _ => hX i)
  rw [← htw] at ht
  exact ht

end
end Dubon2026.SourceFricke