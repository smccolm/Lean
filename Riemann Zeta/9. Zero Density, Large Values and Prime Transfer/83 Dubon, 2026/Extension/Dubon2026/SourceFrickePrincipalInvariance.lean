import Dubon2026.SourceFrickeCyclotomicModularAction

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> elliptic divisibility transport. Principal-level invariance follows from
the actual generator invariance, algebra generation and analytic-domain
cancellation of each original nonzero denominator. It is then inherited by
the complex function span, rather than supplied as an extra hypothesis. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField
open scoped MatrixGroups Manifold

theorem smul_eq_self_cyclotomicLevelRing {N : ℕ} [NeZero N]
    {f : ℍ → ℂ} (hf : f ∈ cyclotomicLevelRing N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : γ • f = f := by
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    funext τ
    exact (LevelGens.std N).invariant f hf γ⁻¹ ((CongruenceSubgroup.Gamma N).inv_mem hγ) τ
  | algebraMap c => rfl
  | add f g _ _ hf hg => rw [smul_add, hf, hg]
  | mul f g _ _ hf hg => rw [smul_mul', hf, hg]

theorem smul_eq_self_holomorphicCyclotomicFrickeFractions {N : ℕ} [NeZero N]
    {f : ℍ → ℂ} (hf : f ∈ holomorphicCyclotomicFrickeFractions N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma N) : γ • f = f := by
  obtain ⟨hh, a, ha, b, hb, hb0, he⟩ := hf
  have ht := congrArg (fun g : ℍ → ℂ => γ • g) he
  dsimp only at ht
  rw [smul_mul', smul_eq_self_cyclotomicLevelRing hb hγ,
    smul_eq_self_cyclotomicLevelRing ha hγ] at ht
  have hm : (γ • f - f) * b = 0 := by
    rw [sub_mul, ht, he, sub_self]
  have hz := ((UpperHalfPlane.mul_eq_zero_iff ((mdifferentiable_slFn hh γ).sub hh)
    (cyclotomicLevelRing_holomorphic hb)).mp hm).resolve_right hb0
  exact sub_eq_zero.mp hz

theorem smul_eq_self_frickeSpan {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : f ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N))
    {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N) : γ • f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf => exact smul_eq_self_holomorphicCyclotomicFrickeFractions hf hγ
  | zero => exact smul_zero γ
  | add f g _ _ hf hg => rw [smul_add, hf, hg]
  | smul c f _ hf => rw [smul_comm γ c f, hf]

theorem principalInvariant_frickeSpan {N : ℕ} [NeZero N] {f : ℍ → ℂ}
    (hf : f ∈ Submodule.span ℂ (holomorphicCyclotomicFrickeFractions N)) :
    ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, f (γ • τ) = f τ := by
  intro γ hγ τ
  have he := congrFun (smul_eq_self_frickeSpan hf ((CongruenceSubgroup.Gamma N).inv_mem hγ)) τ
  simpa only [sl_smul_apply, inv_inv] using he
end
end Dubon2026.SourceFricke