import Dubon2026.SourceManinOrbitCount
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> parabolic Hecke
realization -> reverse period dimension bound -> finite Manin relations.
Selected from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_Period_six_mul_finrank_parabolicHoms_add_le_index.lean.
The pinned finite-action orbit count and dual annihilator dimension
theorems provide the required relation bound. External global options,
attribute removals and auxiliary framework commands are not imported.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Module

section ManinRel

variable (K : Type*) [Field K] {X : Type*} (σ₂ σ₃ : Equiv.Perm X)

/-- Functions satisfying the exact two-term and three-term Manin relations. -/
def relSpace : Submodule K (X → K) where
  carrier := {m | (∀ x, m x + m (σ₂ x) = 0) ∧ ∀ x, m x + m (σ₃ x) + m (σ₃ (σ₃ x)) = 0}
  zero_mem' := ⟨fun x => by simp, fun x => by simp⟩
  add_mem' := by
    rintro m n ⟨hm2, hm3⟩ ⟨hn2, hn3⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · simp only [Pi.add_apply]; linear_combination hm2 x + hn2 x
    · simp only [Pi.add_apply]; linear_combination hm3 x + hn3 x
  smul_mem' := by
    rintro c m ⟨hm2, hm3⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, hm2 x, mul_zero]
    · simp only [Pi.smul_apply, smul_eq_mul]; rw [← mul_add, ← mul_add, hm3 x, mul_zero]

variable {K σ₂ σ₃} in
theorem mem_relSpace {m : X → K} :
    m ∈ relSpace K σ₂ σ₃ ↔
      (∀ x, m x + m (σ₂ x) = 0) ∧ ∀ x, m x + m (σ₃ x) + m (σ₃ (σ₃ x)) = 0 :=
  Iff.rfl

variable [Fintype X]

/-- Pair the two orbit-function spaces with functions on the original finite set. -/
noncomputable def orbFun : ((Orb σ₂ → K) × (Orb σ₃ → K)) →ₗ[K] Module.Dual K (X → K) :=
  LinearMap.mk₂ K
    (fun ab m => ∑ x, m x * (ab.1 (orbQ σ₂ x) + ab.2 (orbQ σ₃ x)))
    (fun ab ab' m => by
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun c ab m => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun ab m m' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring)
    (fun c ab m => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => by ring)

theorem orbFun_apply (ab : (Orb σ₂ → K) × (Orb σ₃ → K)) (m : X → K) :
    orbFun K σ₂ σ₃ ab m = ∑ x, m x * (ab.1 (orbQ σ₂ x) + ab.2 (orbQ σ₃ x)) := rfl

variable [CharZero K]

theorem relSpace_le_dualCoannihilator :
    relSpace K σ₂ σ₃ ≤ (LinearMap.range (orbFun K σ₂ σ₃)).dualCoannihilator := by
  intro m hm
  rw [mem_relSpace] at hm
  obtain ⟨hm2, hm3⟩ := hm
  rw [Submodule.mem_dualCoannihilator]
  rintro _ ⟨⟨a, b⟩, rfl⟩
  rw [orbFun_apply]
  simp only [mul_add, Finset.sum_add_distrib]
  have hA : ∑ x, m x * a (orbQ σ₂ x) = 0 := by
    have hre : ∑ x, m (σ₂ x) * a (orbQ σ₂ (σ₂ x)) = ∑ x, m x * a (orbQ σ₂ x) :=
      Equiv.sum_comp σ₂ (fun x => m x * a (orbQ σ₂ x))
    simp only [orbQ_apply_perm] at hre
    have h2s : (2 : K) * ∑ x, m x * a (orbQ σ₂ x) = 0 := by
      rw [two_mul]
      nth_rewrite 2 [← hre]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← add_mul, hm2 x, zero_mul]
    exact (mul_eq_zero.mp h2s).resolve_left two_ne_zero
  have hB : ∑ x, m x * b (orbQ σ₃ x) = 0 := by
    have hre1 : ∑ x, m (σ₃ x) * b (orbQ σ₃ (σ₃ x)) = ∑ x, m x * b (orbQ σ₃ x) :=
      Equiv.sum_comp σ₃ (fun x => m x * b (orbQ σ₃ x))
    have hre2 : ∑ x, m (σ₃ (σ₃ x)) * b (orbQ σ₃ (σ₃ (σ₃ x))) =
        ∑ x, m (σ₃ x) * b (orbQ σ₃ (σ₃ x)) :=
      Equiv.sum_comp σ₃ (fun x => m (σ₃ x) * b (orbQ σ₃ (σ₃ x)))
    simp only [orbQ_apply_perm] at hre1 hre2
    have h3s : (3 : K) * ∑ x, m x * b (orbQ σ₃ x) = 0 := by
      have e3 : (3 : K) * ∑ x, m x * b (orbQ σ₃ x) =
          ∑ x, m x * b (orbQ σ₃ x) + ∑ x, m (σ₃ x) * b (orbQ σ₃ x)
            + ∑ x, m (σ₃ (σ₃ x)) * b (orbQ σ₃ x) := by
        rw [hre2, hre1]; ring
      rw [e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun x _ => ?_
      rw [← add_mul, ← add_mul, hm3 x, zero_mul]
    exact (mul_eq_zero.mp h3s).resolve_left three_ne_zero
  rw [hA, hB, add_zero]

/-- Joint invariance under the two actual permutations forces constancy. -/
def Connected (σ₂ σ₃ : Equiv.Perm X) (K : Type*) : Prop :=
  ∀ f : X → K, (∀ x, f (σ₂ x) = f x) → (∀ x, f (σ₃ x) = f x) → ∀ x y, f x = f y

omit [CharZero K] in
theorem ker_orbFun_le (hconn : Connected σ₂ σ₃ K) :
    LinearMap.ker (orbFun K σ₂ σ₃) ≤
      LinearMap.range (LinearMap.toSpanSingleton K _
        ((fun _ => (1 : K), fun _ => (-1 : K)) : (Orb σ₂ → K) × (Orb σ₃ → K))) := by
  classical
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  have hpt : ∀ x, a (orbQ σ₂ x) + b (orbQ σ₃ x) = 0 := by
    intro x₀
    have := LinearMap.congr_fun hab (fun x => if x = x₀ then 1 else 0)
    rw [orbFun_apply, LinearMap.zero_apply] at this
    simpa [ite_mul, Finset.sum_ite_eq'] using this
  have hinv2 : ∀ x, a (orbQ σ₂ (σ₂ x)) = a (orbQ σ₂ x) := fun x => by rw [orbQ_apply_perm]
  have hinv3 : ∀ x, a (orbQ σ₂ (σ₃ x)) = a (orbQ σ₂ x) := fun x => by
    have e1 := hpt x
    have e2 := hpt (σ₃ x)
    rw [orbQ_apply_perm] at e2
    linear_combination e2 - e1
  have hconst := hconn (fun x => a (orbQ σ₂ x)) hinv2 hinv3
  rw [LinearMap.mem_range]
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · refine ⟨0, ?_⟩
    ext y
    · exact (hX.false (orbQ_surjective σ₂ y).choose).elim
    · exact (hX.false (orbQ_surjective σ₃ y).choose).elim
  refine ⟨a (orbQ σ₂ x₀), ?_⟩
  ext y
  · obtain ⟨x, rfl⟩ := orbQ_surjective σ₂ y
    simp [LinearMap.toSpanSingleton_apply, hconst x x₀]
  · obtain ⟨x, rfl⟩ := orbQ_surjective σ₃ y
    have := hpt x
    simp only [LinearMap.toSpanSingleton_apply, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      mul_neg, mul_one]
    have hc : a (orbQ σ₂ x₀) = a (orbQ σ₂ x) := hconst x₀ x
    rw [hc]; linear_combination (-1 : K) * this

theorem relSpace_rank_bound (h2 : σ₂ ^ 2 = 1) (h3 : σ₃ ^ 3 = 1) (hconn : Connected σ₂ σ₃ K) :
    6 * Module.finrank K (relSpace K σ₂ σ₃) + 3 * Nat.card {x // σ₂ x = x}
        + 4 * Nat.card {x // σ₃ x = x} ≤ 6 + Nat.card X := by
  classical
  have hO2 := two_mul_natCard_orb σ₂ h2
  have hO3 := three_mul_natCard_orb σ₃ h3

  have hco := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (LinearMap.range (orbFun K σ₂ σ₃))
  have hV : Module.finrank K (relSpace K σ₂ σ₃) ≤
      Module.finrank K (LinearMap.range (orbFun K σ₂ σ₃)).dualCoannihilator :=
    Submodule.finrank_mono (relSpace_le_dualCoannihilator K σ₂ σ₃)
  have hXK : Module.finrank K (X → K) = Nat.card X := by
    rw [Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

  have hrn := LinearMap.finrank_range_add_finrank_ker (orbFun K σ₂ σ₃)
  have hdom : Module.finrank K ((Orb σ₂ → K) × (Orb σ₃ → K)) = Nat.card (Orb σ₂) + Nat.card (Orb σ₃) := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hker : Module.finrank K (LinearMap.ker (orbFun K σ₂ σ₃)) ≤ 1 := by
    refine (Submodule.finrank_mono (ker_orbFun_le K σ₂ σ₃ hconn)).trans ?_
    refine (LinearMap.finrank_range_le _).trans ?_
    rw [Module.finrank_self]
  omega

end ManinRel


end
end Dubon2026.SourceManin
