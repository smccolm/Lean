import Mathlib
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.ZeroDetector

open Complex Finset
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

lemma pow_coeff_subset (N k m : ℕ) (hm : 0 < m) :
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc N (2 * N))).filter (fun p => (∏ x : Fin k, p x) = m) ⊆
  (Fintype.piFinset (fun (_ : Fin k) => Finset.Ioc 1 m)).filter (fun p => (∏ x : Fin k, p x) = m) := by
  intro p hp
  rw [mem_filter] at hp ⊢
  rcases hp with ⟨hp_pi, hp_prod⟩
  refine ⟨?_, hp_prod⟩
  rw [Fintype.mem_piFinset] at hp_pi ⊢
  intro x
  have hpx := hp_pi x
  rw [mem_Ioc] at hpx ⊢
  rcases hpx with ⟨hpx1, hpx2⟩
  constructor
  · by_cases hN : N = 0
    · rw [hN] at hpx1 hpx2
      linarith
    · have hN_pos : N ≥ 1 := Nat.pos_of_ne_zero hN
      linarith
  · have hdvd : p x ∣ ∏ y : Fin k, p y := dvd_prod_of_mem (fun y => p y) (mem_univ x)
    rw [hp_prod] at hdvd
    exact Nat.le_of_dvd hm hdvd

end RiemannZeta.GuthMaynard
