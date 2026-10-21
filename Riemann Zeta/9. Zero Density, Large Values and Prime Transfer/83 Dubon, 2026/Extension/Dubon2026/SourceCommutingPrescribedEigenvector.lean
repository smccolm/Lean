import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.RingTheory.Artinian.Module

/-! A prescribed Hecke character is realized on a nonzero tensor eigenvector.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> residual H1 eigensystem
-> nonzero tensor eigenclass with the already constructed original character.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom.lean
(Apache-2.0; retained LICENSE and NOTICE).
SourceBinaryH1HeckeCommute proves the original full H1 Hecke commutativity;
SourceOriginalResidualH1Eigensystem consumes it without an extra premise.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct
open TensorProduct


variable {F : Type*} [Field F]

private theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module F M] (f : M →ₗ[F] M)
    (P : Submodule F M) (h : ∀ v ∈ P, f v ∈ P) (k : ℕ) (v : ↥P) :
    (((f.restrict h) ^ k) v : M) = (f ^ k) (v : M) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

private theorem exists_common_ker_of_nilpotent : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) → Nontrivial M →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT hnil hM hd
  by_cases hz : ∀ i, T i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hz i, LinearMap.zero_apply]⟩
  push Not at hz
  obtain ⟨i₀, hi₀⟩ := hz
  set P : Submodule F M := LinearMap.ker (T i₀) with hP
  have hPtop : P ≠ ⊤ := fun h => hi₀ (LinearMap.ker_eq_top.mp h)
  have hPbot : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (T i₀) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hnil i₀
    have hinjk : Function.Injective ((T i₀) ^ k) := by
      rw [Module.End.coe_pow]; exact Function.Injective.iterate hinj k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (hinjk (by rw [hk, map_zero, LinearMap.zero_apply]))
  have hstab : ∀ i, ∀ v ∈ P, T i v ∈ P := by
    intro i v hv
    rw [hP, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, (hT i₀ i).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P →ₗ[F] ↥P := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hnil' : ∀ i, IsNilpotent (T' i) := by
    intro i
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    change ((((T i).restrict (hstab i)) ^ k) v : M) = ((0 : ↥P →ₗ[F] ↥P) v : M)
    rw [coe_restrict_pow, hk]
    rfl
  haveI : Nontrivial ↥P := Submodule.nontrivial_iff_ne_bot.mpr hPbot
  have hlt : Module.finrank F ↥P < d := hd ▸ Submodule.finrank_lt hPtop
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' hnil' inferInstance rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

private theorem exists_common_ker_of_range_le : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → ∀ (P : Submodule F M), P ≠ ⊤ → (∀ i x, T i x ∈ P) →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT P hP hTP hd
  by_cases hall : ∀ i, IsNilpotent (T i)
  ·
    have hex : ∃ v : M, v ∉ P := by
      by_contra h
      push Not at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push Not at hall
  obtain ⟨i₀, hi₀⟩ := hall
  set f := T i₀ with hf

  obtain ⟨k, hk, hk1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and (Filter.eventually_ge_atTop 1)).exists
  set P' : Submodule F M := LinearMap.ker (f ^ k) with hP'
  set Q : Submodule F M := LinearMap.range (f ^ k) with hQ
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hi₀
    exact ⟨k, LinearMap.range_eq_bot.mp h⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    have hdis := hk.disjoint
    rw [h] at hdis
    exact hQbot (top_disjoint.mp hdis)

  have hQP : Q ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hfk : f ^ k = f * f ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
    rw [hfk, Module.End.mul_apply]
    exact hTP i₀ _

  have hP'P : P.comap P'.subtype ≠ ⊤ := by
    intro h
    have hle : P' ≤ P := fun v hv => by
      have : (⟨v, hv⟩ : ↥P') ∈ P.comap P'.subtype := by rw [h]; trivial
      exact this
    apply hP
    rw [eq_top_iff, ← hk.codisjoint.eq_top]
    exact sup_le hle hQP

  have hstab : ∀ i, ∀ v ∈ P', T i v ∈ P' := by
    intro i v hv
    rw [hP', LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ((hT i₀ i).pow_left k).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P' →ₗ[F] ↥P' := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hTP' : ∀ i (x : ↥P'), T' i x ∈ P.comap P'.subtype := fun i x => hTP i (x : M)
  have hlt : Module.finrank F ↥P' < d := hd ▸ Submodule.finrank_lt hP'top
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' (P.comap P'.subtype) hP'P hTP' rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

/-- Commuting operators with a nonzero quotient carrying specified scalars have
a nonzero common eigenvector with precisely those scalars. -/
theorem sourceCommutingOperators_exists_prescribedEigenvector {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {ι : Type*} (T : ι → M →ₗ[F] M) (hT : ∀ i j, Commute (T i) (T j)) (c : ι → F)
    (P : Submodule F M) (hP : P ≠ ⊤) (hTP : ∀ i x, T i x - c i • x ∈ P) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = c i • v := by
  let T' : ι → M →ₗ[F] M := fun i => T i - c i • 1
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    refine Commute.sub_left (Commute.sub_right (hT i j) ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.refl (1 : M →ₗ[F] M)).smul_right _).smul_left _
  have hTP' : ∀ i x, T' i x ∈ P := fun i x => by
    simpa [T', LinearMap.sub_apply, LinearMap.smul_apply] using hTP i x
  obtain ⟨v, hv, hTv⟩ := exists_common_ker_of_range_le _ T' hT' P hP hTP' rfl
  refine ⟨v, hv, fun i => ?_⟩
  have := hTv i
  simp only [T', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this


end
end Dubon2026
