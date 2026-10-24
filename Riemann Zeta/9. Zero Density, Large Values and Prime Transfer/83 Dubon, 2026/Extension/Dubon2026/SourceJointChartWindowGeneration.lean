import Dubon2026.SourceJointChartWindows

/-! DUB-17/18 -> Picard torsion injectivity -> original-field Kummer
power lifting -> genus inequality -> two-chart dimension comparison.
These helpers identify the actual residue chart windows with products of
pole spaces. Adapted from Apache-2.0 FLT commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Existing valuation-ring closure
replaces separate order-addition and scalar-order lemmas. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
noncomputable section
open Polynomial
universe u v w

section WindowRank

variable {k : Type u} [Field k] {ι : Type v} {Fb : ι → Type w} [∀ i, Field (Fb i)]
  [∀ i, Algebra k (Fb i)]

/-- The product of submodules identified with its coordinate submodule. -/
def piEquiv (p : ∀ i, Submodule k (Fb i)) : ↥(Submodule.pi Set.univ p) ≃ₗ[k] ∀ i, ↥(p i) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun y := ⟨fun i => y i, fun i _ => (y i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem finite_pi (p : ∀ i, Submodule k (Fb i)) [∀ i, FiniteDimensional k ↥(p i)] [Finite ι] :
    FiniteDimensional k ↥(Submodule.pi Set.univ p) :=
  Module.Finite.equiv (piEquiv p).symm

theorem finrank_pi (p : ∀ i, Submodule k (Fb i)) [∀ i, FiniteDimensional k ↥(p i)] [Fintype ι] :
    Module.finrank k ↥(Submodule.pi Set.univ p) = ∑ i, Module.finrank k ↥(p i) := by
  rw [(piEquiv p).finrank_eq, Module.finrank_pi_fintype]

theorem card_le_finrank_inf [Fintype ι] (u : ∀ i, Fb i)
    [FiniteDimensional k ↥(Bsub (k := k) u ⊓ Bsub' u)] :
    Fintype.card ι ≤ Module.finrank k ↥(Bsub (k := k) u ⊓ Bsub' u) := by
  let c : (ι → k) →ₗ[k] (∀ i, Fb i) :=
    LinearMap.pi fun i => (Algebra.linearMap k (Fb i)).comp (LinearMap.proj i)
  have hc : Function.Injective c := by
    intro a b hab
    ext i
    have := congr_fun hab i
    simpa [c] using this
  have hrange : LinearMap.range c ≤ Bsub u ⊓ Bsub' u := by
    rintro _ ⟨a, rfl⟩
    refine ⟨fun i w _ => ?_, fun i w _ => ?_⟩ <;> simp [c, Place.ord_algebraMap]
  calc Fintype.card ι = Module.finrank k (ι → k) := (Module.finrank_fintype_fun_eq_card k).symm
    _ = Module.finrank k ↥(LinearMap.range c) := (LinearMap.finrank_range_of_inj hc).symm
    _ ≤ _ := Submodule.finrank_mono hrange

theorem pow_mul_single [DecidableEq ι] (u : ∀ i, Fb i) (i : ι) (j : ℕ) (y : Fb i) :
    u ^ j * Pi.single i y = Pi.single i (u i ^ j * y) := by
  ext i'
  by_cases h : i' = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem single_mem_window [DecidableEq ι] (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (D : ∀ i, Divisor k (Fb i)) (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i)))
    (M : ℕ) (i : ι) (y : Fb i) (hy : y ∈ LSpace (M • D i)) :
    Pi.single i y ∈
      Bsub u ⊓ (Bsub' u).map ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M) := by
  rw [window_eq u hu D hD M, Submodule.mem_pi]
  intro i' _
  by_cases h : i' = i
  · subst h; simpa using hy
  · rw [Pi.single_eq_of_ne h]; exact Submodule.zero_mem _

theorem divisor_nonneg (u : ∀ i, Fb i) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (i : ι) : 0 ≤ D i :=
  fun w => by rw [hD i w]; exact le_max_left _ _

theorem nsmul_divisor_mono (u : ∀ i, Fb i) (D : ∀ i, Divisor k (Fb i))
    (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i))) (i : ι) {a b : ℕ}
    (hab : a ≤ b) : a • D i ≤ b • D i := fun w => by
  simp only [nsmul_divisor_apply]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) (divisor_nonneg u D hD i w)

theorem Bsub_le_iSup (u : ∀ i, Fb i) (hu : ∀ i, u i ≠ 0)
    (D : ∀ i, Divisor k (Fb i)) (hD : ∀ i (w : Place k (Fb i)), D i w = max 0 (-w.ord (u i)))
    (M₁ : ℕ) [Fintype ι]
    (hspan : ∀ i, ∃ Mi : ℕ, Mi ≤ M₁ ∧ ∀ h : Fb i,
      (∀ w : Place k (Fb i), 0 ≤ w.ord (u i) → 0 ≤ w.ord h) →
        h ∈ Submodule.span k {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • D i), g = u i ^ j * y}) :
    Bsub u ≤ ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
      ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M₁)).map
        ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ j) := by
  classical
  intro h hh
  rw [← Finset.univ_sum_single h]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨Mi, hMi, hsp⟩ := hspan i
  have hhi := hsp (h i) (fun w hw => hh i w hw)
  have hle : (Submodule.span k
      {g : Fb i | ∃ j : ℕ, ∃ y ∈ LSpace (Mi • D i), g = u i ^ j * y}).map
        (LinearMap.single k Fb i) ≤
      ⨆ j : ℕ, (Bsub u ⊓ (Bsub' u).map
        ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ M₁)).map
          ((mulEquiv (k := k) u hu : (∀ i, Fb i) →ₗ[k] (∀ i, Fb i)) ^ j) := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨g, ⟨j, y, hy, rfl⟩, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨Pi.single i y,
      single_mem_window u hu D hD M₁ i y (lSpace_mono (nsmul_divisor_mono u D hD i hMi) hy), ?_⟩
    rw [mulEquiv_pow_apply, LinearMap.coe_single, pow_mul_single]
  exact hle ⟨h i, hhi, rfl⟩

end WindowRank

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartAssembly
