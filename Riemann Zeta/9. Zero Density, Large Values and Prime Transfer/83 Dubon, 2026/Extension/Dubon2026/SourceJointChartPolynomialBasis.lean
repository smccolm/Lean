import Mathlib

/-! DUB-17/18 -> original-field Kummer power lifting -> genus inequality ->
common residue constants -> finite localized chart overlap. A residue chart
stable under the coordinate has a finite polynomial basis once it embeds
in a finite polynomial module. This supplies the lifted chart basis needed
to bound representatives of the overlap quotient. Adapted from Apache-2.0
FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2; native PID module
theory performs the finite freeness step. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {k : Type*} [Field k] {E : Type*} [CommRing E] [Algebra k E]

theorem exists_polynomial_basis (fb : E) (M : Submodule k E)
    (hM : ∀ m ∈ M, fb * m ∈ M)
    (htf : ∀ (q : k[X]) (h : E), aeval fb q * h = 0 → q = 0 ∨ h = 0)
    {γ : Type*} [Fintype γ] (g : γ → E)
    (hN : ∀ m ∈ M, ∃ q : γ → k[X], m = ∑ c, aeval fb (q c) * g c) :
    ∃ (d : ℕ) (zb : Fin d → E), (∀ σ, zb σ ∈ M) ∧
      (∀ q q' : Fin d → k[X],
        ∑ σ, aeval fb (q σ) * zb σ = ∑ σ, aeval fb (q' σ) * zb σ → q = q') ∧
      (∀ m ∈ M, ∃ q : Fin d → k[X], m = ∑ σ, aeval fb (q σ) * zb σ) ∧
      (∀ (d' : ℕ) (zb' : Fin d' → E), (∀ τ, zb' τ ∈ M) →
        (∀ q q' : Fin d' → k[X],
          ∑ τ, aeval fb (q τ) * zb' τ = ∑ τ, aeval fb (q' τ) * zb' τ → q = q') → d' ≤ d) := by
  classical

  letI inst : Module k[X] E := Module.compHom E (aeval fb).toRingHom
  have hsmul : ∀ (q : k[X]) (h : E), q • h = aeval fb q * h := fun _ _ => rfl

  let M' : Submodule k[X] E :=
    { carrier := M
      add_mem' := fun ha hb => M.add_mem ha hb
      zero_mem' := M.zero_mem
      smul_mem' := by
        intro q m hm
        change q • m ∈ M
        rw [hsmul]
        induction q using Polynomial.induction_on' with
        | add p q hp hq => rw [map_add, add_mul]; exact M.add_mem hp hq
        | monomial n a =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aeval_C, aeval_X, mul_assoc,
            Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
          refine M.smul_mem a ?_
          induction n with
          | zero => rwa [pow_zero, one_mul]
          | succ n ih => rw [pow_succ', mul_assoc]; exact hM _ ih }
  have hM'mem : ∀ {m : E}, m ∈ M' ↔ m ∈ M := Iff.rfl

  let N' : Submodule k[X] E := Submodule.span k[X] (Set.range g)
  have hle : M' ≤ N' := by
    intro m hm
    obtain ⟨q, rfl⟩ := hN m hm
    refine N'.sum_mem fun c _ => ?_
    rw [← hsmul]
    exact N'.smul_mem _ (Submodule.subset_span ⟨c, rfl⟩)
  haveI : IsNoetherian k[X] N' := isNoetherian_of_fg_of_noetherian _
    (Submodule.fg_span (Set.finite_range g))
  haveI : IsNoetherian k[X] M' := isNoetherian_of_le hle
  haveI : Module.Finite k[X] M' := inferInstance
  haveI : Module.IsTorsionFree k[X] M' := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun q m hqm => ?_
    have h0 : aeval fb q * (m : E) = 0 := by
      rw [← hsmul]; exact congrArg Subtype.val hqm
    rcases htf q m h0 with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext h)
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := k[X]) (M := M')
  refine ⟨d, fun σ => (b σ : E), fun σ => (b σ).2, ?_, ?_, ?_⟩
  ·
    intro q q' hqq'
    have hsum : ∀ r : Fin d → k[X],
        ((∑ σ, r σ • b σ : M') : E) = ∑ σ, aeval fb (r σ) * (b σ : E) := by
      intro r
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl fun σ _ => rfl
    have h1 : (∑ σ, q σ • b σ : M') = ∑ σ, q' σ • b σ := by
      apply Subtype.ext
      rw [hsum, hsum, hqq']
    have h2 : ∑ σ, (q σ - q' σ) • b σ = (0 : M') := by
      have hsub : ∀ σ, (q σ - q' σ) • b σ = q σ • b σ - q' σ • b σ := fun σ => sub_smul (q σ) (q' σ) (b σ)
      simp_rw [hsub, Finset.sum_sub_distrib, h1, sub_self]
    have h3 := Fintype.linearIndependent_iff.mp b.linearIndependent (fun σ => q σ - q' σ) h2
    funext σ
    exact sub_eq_zero.mp (h3 σ)
  ·
    intro m hm
    refine ⟨fun σ => b.repr ⟨m, hm⟩ σ, ?_⟩
    have h := congrArg (fun x : M' => (x : E)) (b.sum_repr ⟨m, hm⟩)
    simp only [Submodule.coe_sum] at h
    exact h.symm.trans (Finset.sum_congr rfl fun σ _ => rfl)
  ·
    intro d' zb' hzb' hind
    let v : Fin d' → M' := fun τ => ⟨zb' τ, hzb' τ⟩
    have hv : LinearIndependent k[X] v := by
      rw [Fintype.linearIndependent_iff]
      intro q hq τ
      have h0 : ∑ τ, aeval fb (q τ) * zb' τ = ∑ τ, aeval fb ((0 : Fin d' → k[X]) τ) * zb' τ := by
        have h := congrArg (fun x : M' => (x : E)) hq
        simp only [Submodule.coe_sum, ZeroMemClass.coe_zero] at h
        rw [show ∑ τ, aeval fb ((0 : Fin d' → k[X]) τ) * zb' τ = 0 by simp]
        rw [← h]
        exact Finset.sum_congr rfl fun τ _ => rfl
      exact congrFun (hind q 0 h0) τ
    have := hv.fintype_card_le_finrank
    rwa [Fintype.card_fin, Module.finrank_eq_card_basis b, Fintype.card_fin] at this


end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
