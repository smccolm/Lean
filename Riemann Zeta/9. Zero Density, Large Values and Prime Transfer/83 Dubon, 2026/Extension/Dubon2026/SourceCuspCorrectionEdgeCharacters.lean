import Dubon2026.SourceCuspCorrectionCyclicCosets

/-! DUB-17/18 -> original Gamma1 Picard/H1 -> Abel-Jacobi -> unitary
multiplier lifting -> integral parabolic-character lifting -> actual cusp
value correction. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.
The native finite edge-chain construction supplies the named dependency.
No external compatibility shim or linter suppression is imported. -/
namespace Dubon2026.SourceCuspCorrection
noncomputable section
open Subgroup Monoid Monoid.CoprodI MulAction
section Eval

variable (H : Subgroup Gp) [H.FiniteIndex]

open scoped Classical

theorem sum_ite_enum_eq (g : Gp) (y : X H) :
    (∑ j ∈ Finset.range (wd H (g : X H)), if enum H g j = y then (1 : ℤ) else 0)
      = if cusp H y = cusp H (g : X H) then 1 else 0 := by
  by_cases h : cusp H y = cusp H (g : X H)
  · rw [if_pos h]
    obtain ⟨j, hj, hjy⟩ := exists_enum_eq_of_cusp_eq H g h
    have hfilt : (Finset.range (wd H (g : X H))).filter (fun k => enum H g k = y) = {j} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hj, hjy⟩, ?_⟩
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      exact enum_injOn_range H g hk1 hj (hk2.trans hjy.symm)
    rw [← Finset.sum_filter, hfilt, Finset.sum_singleton]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j _ => if_neg fun hjy => h ?_
    rw [← hjy, cusp_enum]

theorem edgeChainHom_genAt_apply (g : Gp) (e : X H) :
    edgeChainHom H (Additive.ofMul (genAt H g)) e
      = (if cusp H (flip H e) = cusp H (g : X H) then 1 else 0)
        - (if cusp H e = cusp H (g : X H) then 1 else 0) := by
  rw [edgeChainHom_genAt_raw]
  simp only [Finsupp.coe_sub, Finsupp.finsetSum_apply, Pi.sub_apply,
    Finsupp.single_apply, Finset.sum_sub_distrib]
  rw [sum_enum_succ H g (fun x => if x = e then (1 : ℤ) else 0), sum_ite_enum_eq]
  congr 1
  calc ∑ j ∈ Finset.range (wd H (g : X H)),
          (if flip H (enum H g j) = e then (1 : ℤ) else 0)
      = ∑ j ∈ Finset.range (wd H (g : X H)),
          (if enum H g j = flip H e then (1 : ℤ) else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        congr 1
        exact propext ⟨fun h => by rw [← h, flip_flip], fun h => by rw [h, flip_flip]⟩
    _ = if cusp H (flip H e) = cusp H (g : X H) then 1 else 0 := sum_ite_enum_eq H g (flip H e)

/-- The integer difference between the cusp orbits joined by an edge. -/
def cuspDiffAt (e : X H) : Cu H → ℤ :=
  Pi.single (cusp H (flip H e)) 1 - Pi.single (cusp H e) 1

/-- Evaluation of the actual integer edge-chain character at a coset. -/
def edgeChar (e : X H) : Additive H →+ ℤ := (Finsupp.applyAddHom e).comp (edgeChainHom H)

theorem edgeChar_genAt (e : X H) (g : Gp) :
    edgeChar H e (Additive.ofMul (genAt H g)) = cuspDiffAt H e (cusp H (g : X H)) := by
  show edgeChainHom H (Additive.ofMul (genAt H g)) e = _
  rw [edgeChainHom_genAt_apply, cuspDiffAt, Pi.sub_apply, Pi.single_apply, Pi.single_apply]
  simp only [@eq_comm _ (cusp H (g : X H))]

omit [H.FiniteIndex] in
theorem single_sub_single_mem_span_of_smul (k : Gp) (e : X H) :
    (Pi.single (cusp H (k • e)) 1 - Pi.single (cusp H e) 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
  have htop : k ∈ (⊤ : Subgroup Gp) := mem_top k
  rw [← closure_sA_τ] at htop
  have key : ∀ e', (Pi.single (cusp H (k • e')) 1
        - Pi.single (cusp H e') 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
    induction htop using Subgroup.closure_induction with
    | one => intro e'; rw [one_smul, sub_self]; exact Submodule.zero_mem _
    | mul x y _ _ hx hy =>
      intro e'
      rw [mul_smul]
      have := Submodule.add_mem _ (hx (y • e')) (hy e')
      rwa [sub_add_sub_cancel] at this
    | inv x _ hx =>
      intro e'
      have h1 := Submodule.neg_mem _ (hx (x⁻¹ • e'))
      rw [smul_inv_smul, neg_sub] at h1
      exact h1
    | mem x hx =>
      intro e'
      rcases hx with rfl | rfl
      · exact Submodule.subset_span ⟨e', rfl⟩
      · rw [cusp_τ_smul, sub_self]; exact Submodule.zero_mem _
  exact key e

omit [H.FiniteIndex] in
theorem single_sub_single_mem_span_cuspDiffAt (c c' : Cu H) :
    (Pi.single c' 1 - Pi.single c 1 : Cu H → ℤ)
      ∈ Submodule.span ℤ (Set.range (cuspDiffAt H)) := by
  obtain ⟨e, rfl⟩ := cusp_surjective H c
  obtain ⟨e', rfl⟩ := cusp_surjective H c'
  induction e using QuotientGroup.induction_on with | H k =>
  induction e' using QuotientGroup.induction_on with | H k' =>
  have heq : ((k' : Gp) : X H) = (k' * k⁻¹) • ((k : Gp) : X H) := by
    show QuotientGroup.mk k' = QuotientGroup.mk ((k' * k⁻¹) * k)
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [heq]
  exact single_sub_single_mem_span_of_smul H (k' * k⁻¹) _

theorem exists_addChar_of_mem_span {v : Cu H → ℤ}
    (hv : v ∈ Submodule.span ℤ (Set.range (cuspDiffAt H))) :
    ∃ φ : Additive H →+ ℤ, ∀ g : Gp, φ (Additive.ofMul (genAt H g)) = v (cusp H (g : X H)) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, rfl⟩ := hx
    exact ⟨edgeChar H e, fun g => edgeChar_genAt H e g⟩
  | zero => exact ⟨0, fun g => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨φ, hφ⟩ := hx
    obtain ⟨ψ, hψ⟩ := hy
    exact ⟨φ + ψ, fun g => by rw [AddMonoidHom.add_apply, hφ, hψ, Pi.add_apply]⟩
  | smul n x _ hx =>
    obtain ⟨φ, hφ⟩ := hx
    exact ⟨n • φ, fun g => by rw [AddMonoidHom.smul_apply, hφ, Pi.smul_apply]⟩

end Eval

end
end Dubon2026.SourceCuspCorrection
