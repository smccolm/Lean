import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import RiemannZeta.GuthMaynard.ZeroDetector
import Mathlib.Tactic

open Complex Finset RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable def powCoeff_alt (N k : ℕ) (m : ℕ) : ℂ :=
  ∑ p ∈ (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m),
    ∏ x : Fin k, detectorCoeff N (p x)

noncomputable def powPoly_alt (N k : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc (N^k) ((2*N)^k), powCoeff_alt N k m * (m : ℂ) ^ (-s)

theorem prod_cpow_nat {ι : Type*} (s : Finset ι) (p : ι → ℕ) (z : ℂ) :
  (∏ i ∈ s, (p i : ℂ) ^ z) = (∏ i ∈ s, (p i : ℂ)) ^ z := by
  classical
  induction' s using Finset.induction_on with a s ha ih
  · simp
  · rw [prod_insert ha, prod_insert ha, ih]
    have := natCast_mul_natCast_cpow (p a) (∏ i ∈ s, p i) z
    push_cast at this ⊢
    rw [this]

lemma prod_bound_Icc {N k : ℕ} {p : Fin k → ℕ} (hp : p ∈ Fintype.piFinset fun _ => Ioc N (2 * N)) :
  (∏ i, p i) ∈ Icc (N ^ k) ((2 * N) ^ k) := by
  rw [Fintype.mem_piFinset] at hp
  rw [mem_Icc]
  constructor
  · have h1 : ∏ i : Fin k, N ≤ ∏ i : Fin k, p i := by
      apply Finset.prod_le_prod
      · intro i _
        exact zero_le N
      · intro i _
        have := (mem_Ioc.mp (hp i)).1
        exact le_of_lt this
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  · have h2 : ∏ i : Fin k, p i ≤ ∏ i : Fin k, (2 * N) := by
      apply Finset.prod_le_prod
      · intro i _
        exact Nat.zero_le (p i)
      · intro i _
        exact (mem_Ioc.mp (hp i)).2
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    exact h2

theorem polynomialPowerIdentity_alt (N k : ℕ) (s : ℂ) :
  (detectPoly N s) ^ k = powPoly_alt N k s := by
  dsimp [detectPoly, powPoly_alt, powCoeff_alt]
  have h1 := Finset.sum_pow' (Ioc N (2 * N)) (fun (n : ℕ) => detectorCoeff N n * (n : ℂ) ^ (-s)) k
  rw [h1]
  
  have hRHS : (∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
      (∑ p ∈ (Fintype.piFinset fun _ => Ioc N (2 * N)).filter fun p => ∏ x : Fin k, p x = m,
        ∏ x : Fin k, detectorCoeff N (p x)) * (m : ℂ) ^ (-s)) =
    ∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
      ∑ p ∈ (Fintype.piFinset fun _ => Ioc N (2 * N)).filter fun p => ∏ x : Fin k, p x = m,
        (∏ x : Fin k, detectorCoeff N (p x)) * ((∏ x : Fin k, p x) : ℂ) ^ (-s) := by
    apply sum_congr rfl
    intro m _
    apply sum_congr rfl
    intro p hp
    rw [mem_filter] at hp
    rw [hp.2]
  rw [hRHS]

  have hRHS2 : (∑ m ∈ Icc (N ^ k) ((2 * N) ^ k),
      ∑ p ∈ (Fintype.piFinset fun _ => Ioc N (2 * N)).filter fun p => ∏ x : Fin k, p x = m,
        (∏ x : Fin k, detectorCoeff N (p x)) * ((∏ x : Fin k, p x) : ℂ) ^ (-s)) = 
    ∑ p ∈ Fintype.piFinset fun _ => Ioc N (2 * N),
      (∏ x : Fin k, detectorCoeff N (p x)) * ((∏ x : Fin k, p x) : ℂ) ^ (-s) := by
    exact (Finset.sum_fiberwise_of_maps_to prod_bound_Icc (fun p => (∏ x : Fin k, detectorCoeff N (p x)) * ((∏ x : Fin k, p x) : ℂ) ^ (-s))).symm
  rw [hRHS2]

  apply sum_congr rfl
  intro p _
  rw [prod_mul_distrib, prod_cpow_nat]
