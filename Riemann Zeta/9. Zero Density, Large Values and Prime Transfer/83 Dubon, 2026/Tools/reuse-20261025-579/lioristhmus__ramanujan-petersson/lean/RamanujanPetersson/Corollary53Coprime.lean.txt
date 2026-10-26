import Mathlib

open scoped BigOperators

namespace RamanujanPetersson

/--
Lean-generated witness form of the coprime-index clause in Corollary 5.3.

Instead of deriving multiplicativity and the divisor-count identity from the Euler
product, this theorem assumes an explicit finite witness decomposition of `aₙ`
into prime-power factors together with the corresponding real identities for the
divisor count and the power of `n`.
-/
theorem corollary53_coprimeIndices_witnessForm
    {ι : Type*} [DecidableEq ι]
    {a : ℂ} {n N k d : ℕ}
    (s : Finset ι) (apow : ι → ℂ) (p m : ι → ℕ)
    (hnCoprime : Nat.Coprime n N)
    (ha : a = Finset.prod s (fun i => apow i))
    (hbound :
      ∀ i ∈ s,
        ‖apow i‖ ≤
          (m i + 1 : ℝ) * (((p i : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (m i)))
    (hd : (d : ℝ) = Finset.prod s (fun i => (m i + 1 : ℝ)))
    (hn :
      Finset.prod s (fun i => (((p i : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (m i))) =
        (n : ℝ) ^ ((k - 1 : ℝ) / 2)) :
    ‖a‖ ≤ d * (n : ℝ) ^ ((k - 1 : ℝ) / 2) := by
  let _ := hnCoprime
  rw [ha]
  have hnorm :
      ‖Finset.prod s (fun i => apow i)‖ ≤ Finset.prod s (fun i => ‖apow i‖) := by
    simpa using (norm_prod_le (s := s) (f := fun i => apow i))
  refine hnorm.trans ?_
  calc
    Finset.prod s (fun i => ‖apow i‖)
      ≤ Finset.prod s (fun i => (m i + 1 : ℝ) * (((p i : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (m i))) := by
        refine Finset.prod_le_prod ?_ ?_
        · intro i hi
          positivity
        · intro i hi
          exact hbound i hi
    _ = Finset.prod s (fun i => (m i + 1 : ℝ)) *
          Finset.prod s (fun i => (((p i : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (m i))) := by
        rw [Finset.prod_mul_distrib]
    _ = d * Finset.prod s (fun i => (((p i : ℝ) ^ ((k - 1 : ℝ) / 2)) ^ (m i))) := by
        rw [← hd]
    _ = d * (n : ℝ) ^ ((k - 1 : ℝ) / 2) := by
        rw [hn]

end RamanujanPetersson
