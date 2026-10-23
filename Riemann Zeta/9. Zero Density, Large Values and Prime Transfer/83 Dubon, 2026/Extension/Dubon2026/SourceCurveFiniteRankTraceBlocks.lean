import Dubon2026.SourceCurveFiniteRankTraceAdd
import Mathlib.LinearAlgebra.Pi

/-! DUB-17/18 -> higher symmetric-power continuation -> original Frobenius/inertia
-> good reduction -> reverse genus -> global residues -> field-trace comparison.
An integral basis represents multiplication by a matrix. This module proves
that its finite-rank commutator trace is the sum of the diagonal block traces.
Adapted from the verified FLT `S_AlgebraicCurve_tateTraceCompat_of_isSeparable`,
using the existing finite-image trace and native product linear maps. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V M N P : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup P] [Module K P]

/-- A finite-rank middle factor makes a composite finite rank. -/
theorem finite_range_comp_middle (a : N →ₗ[K] P) (b : M →ₗ[K] N) (c : V →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range b)] :
    FiniteDimensional K (LinearMap.range (a ∘ₗ b ∘ₗ c)) := by
  haveI : FiniteDimensional K (LinearMap.range (b ∘ₗ c)) :=
    Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range c b)
  rw [LinearMap.range_comp]
  exact Module.Finite.map _ _

/-- A finite sum of finite-rank endomorphisms has finite rank. -/
theorem finite_range_sum {ι : Type*} (s : Finset ι) (T : ι → V →ₗ[K] V)
    [∀ i, FiniteDimensional K (LinearMap.range (T i))] :
    FiniteDimensional K (LinearMap.range (∑ i ∈ s, T i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (finite_range_zero (K := K) (V := V))
  | @insert i s hi ih =>
    haveI := ih
    have he : (∑ j ∈ insert i s, T j) = T i + ∑ j ∈ s, T j := Finset.sum_insert hi
    exact he.symm ▸ finite_range_add (T i) (∑ j ∈ s, T j)

/-- Finite-rank trace commutes with finite sums of finite-rank endomorphisms. -/
theorem finrankTrace_sum {ι : Type*} (s : Finset ι) (T : ι → V →ₗ[K] V)
    [∀ i, FiniteDimensional K (LinearMap.range (T i))] :
    finrankTrace (∑ i ∈ s, T i) = ∑ i ∈ s, finrankTrace (T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, finrankTrace_zero]
  | @insert i s hi ih =>
    haveI := finite_range_sum s T
    rw [Finset.sum_insert hi, Finset.sum_insert hi, finrankTrace_add, ih]

/-- A single block contributes its trace exactly when it is diagonal. -/
theorem finrankTrace_single_block {ι : Type*} [DecidableEq ι] (i j : ι)
    (T : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range T)] :
    finrankTrace (LinearMap.single K (fun _ : ι => V) i ∘ₗ T ∘ₗ
      (LinearMap.proj j : (ι → V) →ₗ[K] V)) = if j = i then finrankTrace T else 0 := by
  let a : V →ₗ[K] (ι → V) := LinearMap.single K (fun _ : ι => V) i ∘ₗ T
  let b : (ι → V) →ₗ[K] V := LinearMap.proj j
  have hab : b ∘ₗ a = if j = i then T else 0 := by
    apply LinearMap.ext
    intro x
    by_cases h : j = i
    · subst j
      simp [a, b]
    · simp [a, b, h]
  haveI : FiniteDimensional K (LinearMap.range (a ∘ₗ b)) :=
    finite_range_comp_middle (LinearMap.single K (fun _ : ι => V) i) T b
  haveI : FiniteDimensional K (LinearMap.range (b ∘ₗ a)) := by
    by_cases h : j = i
    · have he : b ∘ₗ a = T := by rw [hab, if_pos h]
      exact he.symm ▸ (inferInstance : FiniteDimensional K (LinearMap.range T))
    · have he : b ∘ₗ a = 0 := by rw [hab, if_neg h]
      exact he.symm ▸ finite_range_zero
  change finrankTrace (a ∘ₗ b) = _
  rw [← finrankTrace_comp_comm a b, hab]
  split_ifs <;> simp only [finrankTrace_zero]

/-- The trace of a finite block operator is the sum of its diagonal block traces. -/
theorem finrankTrace_blockSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ι → ι → V →ₗ[K] V)
    [∀ i j, FiniteDimensional K (LinearMap.range (T i j))] :
    finrankTrace (∑ i, ∑ j, LinearMap.single K (fun _ : ι => V) i ∘ₗ T i j ∘ₗ
      (LinearMap.proj j : (ι → V) →ₗ[K] V)) = ∑ i, finrankTrace (T i i) := by
  haveI : ∀ i j, FiniteDimensional K (LinearMap.range
      (LinearMap.single K (fun _ : ι => V) i ∘ₗ T i j ∘ₗ
        (LinearMap.proj j : (ι → V) →ₗ[K] V))) :=
    fun i j => finite_range_comp_middle _ _ _
  haveI : ∀ i, FiniteDimensional K (LinearMap.range
      (∑ j, LinearMap.single K (fun _ : ι => V) i ∘ₗ T i j ∘ₗ
        (LinearMap.proj j : (ι → V) →ₗ[K] V))) := fun i => finite_range_sum _ _
  rw [finrankTrace_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [finrankTrace_sum]
  simp only [finrankTrace_single_block, Finset.sum_ite_eq', Finset.mem_univ, if_true]

end Dubon2026.SourceCurve.ResidueTrace
