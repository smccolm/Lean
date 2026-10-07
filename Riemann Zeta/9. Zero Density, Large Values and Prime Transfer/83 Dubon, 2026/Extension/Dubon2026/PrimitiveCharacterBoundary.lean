import Dubon2026.PrimeDirichletCancellation
import Dubon2026.PrimeCharacterConvergence
import Dubon2026.SatakeSymmetricTrace

/-! # Actual primitive prime characters and the analytic boundary criterion

The arithmetic bound and analytic boundary continuation remain explicit
unproved inputs. Wiener--Ikehara, logarithmic-weight removal, the finite
ramified set and the genuine weak probability limit are derived here.
-/

namespace Dubon2026

open Filter
open scoped Topology

noncomputable section

/-- The actual unramified symmetric-power prime character, with only the finite ramified set removed. -/
def primitivePrimeCharacter {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (r p : ℕ) : ℝ :=
  if p ∣ Q then 0 else (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re

/-- The genuine local prime bound controls every actual unramified symmetric-power prime character. -/
theorem abs_primitivePrimeCharacter_le {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (r : ℕ) {p : ℕ} (hp : Nat.Prime p) : |primitivePrimeCharacter f r p| ≤ (r : ℝ) + 1 := by
  by_cases hpQ : p ∣ Q
  · simp only [primitivePrimeCharacter, if_pos hpQ, abs_zero]
    positivity
  · rw [primitivePrimeCharacter, if_neg hpQ]
    exact (Complex.abs_re_le_norm _).trans
      (primitive_primePower_norm_le_of_prime_bound f hp hpQ (hbound p hp hpQ) r)

/-- The actual primitive Sato--Tate law follows from the explicit local bound and continuous boundary extensions of its genuine prime-character Dirichlet series. -/
theorem primitive_satoTate_of_character_boundary {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k)
    (hbound : ∀ p, Nat.Prime p → ¬p ∣ Q → ‖normalizedCuspCoefficients f.toCuspForm p‖ ≤ 2)
    (hboundary : ∀ r : ℕ, 0 < r → ∃ G : ℂ → ℂ,
      ContinuousOn G {s | 1 ≤ s.re} ∧
      Set.EqOn G (LSeries (fun n => (primeLogCoefficients (primitivePrimeCharacter f r) n : ℂ)))
        {s | 1 < s.re}) :
    Tendsto (primeEmpirical (fun p => (normalizedCuspCoefficients f.toCuspForm p).re))
      atTop (𝓝 satoTateProbability) := by
  apply primitive_satoTate_of_primePower_averages f hbound
  intro r hr
  obtain ⟨G,hG,hseries⟩ := hboundary r hr
  have hg := prime_average_zero_of_boundary_continuation (C := (r : ℝ) + 1) (by positivity)
    (fun p hp => abs_primitivePrimeCharacter_le f hbound r hp) G hG hseries
  have hd := tendsto_prime_average_difference_of_good_eq (Q := Q) (Nat.pos_of_neZero Q)
    (u := fun p => (normalizedCuspCoefficients f.toCuspForm (p ^ r)).re)
    (v := primitivePrimeCharacter f r)
    (fun p _ hpQ => by simp only [primitivePrimeCharacter, if_neg hpQ])
  simpa only [sub_add_cancel, add_zero] using hd.add hg

end
end Dubon2026
