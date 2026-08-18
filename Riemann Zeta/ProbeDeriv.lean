import RiemannZeta.GuthMaynard.HughesYoungCentralArithmeticBridge
import Mathlib.Analysis.Calculus.SmoothSeries

open Complex

noncomputable section

namespace RiemannZeta.GuthMaynard

def probeLogA (h l : ℕ) : ℂ :=
  Complex.log (Nat.gcd h (l + 1) : ℂ) - Complex.log (l + 1 : ℂ)

theorem probe_term_eq (h k : ℕ) (a b c : ℂ) (r l : ℕ) :
    hughesYoungEquation96Term h k a b c r l =
      ramanujanSum (l + 1) (r + 1) *
        (Nat.gcd h (l + 1) : ℂ) ^ a *
        (Nat.gcd k (l + 1) : ℂ) ^ b *
        (l + 1 : ℂ) ^ (-a - b) *
        (r + 1 : ℂ) ^ (-c) := by
  unfold hughesYoungEquation96Term
  have hl : ((l + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
  have hr : ((r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero r
  rw [show -a - b = -(a + b) by ring]
  rw [Complex.cpow_neg, Complex.cpow_neg]
  field_simp
  simp only [Nat.cast_add, Nat.cast_one]

theorem probe_hasDerivAt_a (h k : ℕ) (a b c : ℂ) (r l : ℕ) :
    HasDerivAt (fun z => hughesYoungEquation96Term h k z b c r l)
      (hughesYoungEquation96Term h k a b c r l * probeLogA h l) a := by
  rw [probe_term_eq]
  have hg : (Nat.gcd h (l + 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.gcd_pos_of_pos_right h (Nat.succ_pos l) |>.ne'
  have hl : ((l + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero l
  have hga := (Complex.hasStrictDerivAt_const_cpow
    (x := (Nat.gcd h (l + 1) : ℂ)) (y := a) (Or.inl hg)).hasDerivAt
  have hla0 := (Complex.hasStrictDerivAt_const_cpow
    (x := ((l + 1 : ℕ) : ℂ)) (y := -a - b) (Or.inl hl)).hasDerivAt
  have hla : HasDerivAt
      (fun z : ℂ => ((l + 1 : ℕ) : ℂ) ^ (-z - b))
      (((l + 1 : ℕ) : ℂ) ^ (-a - b) * Complex.log ((l + 1 : ℕ) : ℂ) * (-1)) a := by
    simpa only [Function.comp_apply, id] using
      hla0.comp a ((hasDerivAt_id a).neg.sub_const b)
  have hram : HasDerivAt (fun _ : ℂ => ramanujanSum (l + 1) (r + 1)) 0 a :=
    hasDerivAt_const a _
  have hgk : HasDerivAt (fun _ : ℂ => (Nat.gcd k (l + 1) : ℂ) ^ b) 0 a :=
    hasDerivAt_const a _
  have hrc : HasDerivAt (fun _ : ℂ => ((r + 1 : ℕ) : ℂ) ^ (-c)) 0 a :=
    hasDerivAt_const a _
  have hp := (((hram.mul hga).mul hgk).mul hla).mul hrc
  convert hp using 1
  · funext z
    simp only [Function.comp_apply, Pi.mul_apply, probe_term_eq,
      Nat.cast_add, Nat.cast_one]
  · simp only [Function.comp_apply, Pi.mul_apply, id_eq, probeLogA,
      Nat.cast_add, Nat.cast_one, zero_mul, zero_add, mul_zero, add_zero]
    ring

end RiemannZeta.GuthMaynard
