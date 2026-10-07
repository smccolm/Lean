import Dubon2026.Gamma0PrincipalFactor
import Dubon2026.RectangularLatticeRows

/-! # The exact finite Epstein expansion of the congruence-sieved series -/

namespace Dubon2026

open UpperHalfPlane

noncomputable section

/-- Möbius inversion expresses each actual sieved row as a finite sum of rectangular sublattice rows. -/
theorem gamma0SievedTerm_eq_moebius_sum (Q : ℕ) (hQ : Q ≠ 0) (s : ℂ) (z : ℍ)
    (v : Fin 2 → ℤ) :
    gamma0SievedTerm Q s z v = ∑ d ∈ Q.divisors,
      (ArithmeticFunction.moebius d : ℂ) *
        (rectangularLatticeRows Q d).indicator (fun w => nonholomorphicEisensteinTerm s w z) v := by
  classical
  calc
    _ = (if (Q : ℤ) ∣ v 0 ∧ Nat.Coprime (v 1).natAbs Q then (1 : ℂ) else 0) *
        nonholomorphicEisensteinTerm s v z := by
      simp only [gamma0SievedTerm, Set.indicator_apply, gamma0SievedRows, Set.mem_setOf_eq]
      split_ifs <;> simp
    _ = (∑ d ∈ Q.divisors,
        if (Q : ℤ) ∣ v 0 ∧ (d : ℤ) ∣ v 1 then (ArithmeticFunction.moebius d : ℂ) else 0) *
          nonholomorphicEisensteinTerm s v z := by
      rw [gamma0SievedRows_indicator_moebius Q hQ]
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      simp only [Set.indicator_apply, rectangularLatticeRows, Set.mem_setOf_eq]
      split_ifs <;> simp

/-- Absolute convergence justifies the exact finite Möbius interchange with the lattice sum. -/
theorem gamma0SievedSeries_eq_rectangular (Q : ℕ) (hQ : Q ≠ 0) {s : ℂ}
    (hs : 1 < s.re) (z : ℍ) :
    gamma0SievedSeries Q s z = ∑ d ∈ Q.divisors,
      (ArithmeticFunction.moebius d : ℂ) * ((1 / 2 : ℂ) *
        ∑' v : rectangularLatticeRows Q d, nonholomorphicEisensteinTerm s v.val z) := by
  classical
  have hsum (d : ℕ) : Summable (fun v : Fin 2 → ℤ => (ArithmeticFunction.moebius d : ℂ) *
      (rectangularLatticeRows Q d).indicator (fun w => nonholomorphicEisensteinTerm s w z) v) :=
    ((summable_norm_nonholomorphicEisensteinTerm hs z).of_norm.indicator _).mul_left _
  rw [gamma0SievedSeries]
  simp_rw [gamma0SievedTerm_eq_moebius_sum Q hQ s z]
  rw [Summable.tsum_finsetSum (fun d _ => hsum d), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [tsum_mul_left,
    tsum_subtype (rectangularLatticeRows Q d) (fun v => nonholomorphicEisensteinTerm s v z)]
  ring

/-- The actual congruence-sieved series is a finite sum of genuine rescaled Epstein series. -/
theorem gamma0SievedSeries_eq_epstein (Q : ℕ) (hQ : 0 < Q) {s : ℂ}
    (hs : 1 < s.re) (z : ℍ) :
    gamma0SievedSeries Q s z = ∑ d : Q.divisors,
      (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
        latticeEpsteinSeries
          (rectangularLatticePoint Q d.val hQ (Nat.pos_of_mem_divisors d.property) z) s := by
  classical
  rw [gamma0SievedSeries_eq_rectangular Q (Nat.ne_of_gt hQ) hs z, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro d hd
  rw [rectangularLatticeSeries_eq_epstein Q d.val hQ (Nat.pos_of_mem_divisors d.property) z hs]
  ring

/-- The exact finite completed lattice expression, formed from actual Mellin continuations. -/
def gamma0CompletedLattice (Q : ℕ) (hQ : 0 < Q) (z : ℍ) (s : ℂ) : ℂ :=
  ∑ d : Q.divisors,
    (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
      latticeCompletedMellin
        (rectangularLatticePoint Q d.val hQ (Nat.pos_of_mem_divisors d.property) z) s

/-- In the defining half-plane, the completed lattice expression is the completed actual sieved sum. -/
theorem gamma0CompletedLattice_eq_sieved (Q : ℕ) (hQ : 0 < Q) (z : ℍ)
    {s : ℂ} (hs : 1 < s.re) :
    gamma0CompletedLattice Q hQ z s =
      ((Real.pi : ℂ) ^ (-s) * Complex.Gamma s) * gamma0SievedSeries Q s z := by
  rw [gamma0CompletedLattice, gamma0SievedSeries_eq_epstein Q hQ hs z, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [latticeCompletedMellin_eq_epstein _ hs]
  ring

/-- The finite actual lattice continuation completes the genuine primitive Gamma0 Eisenstein series. -/
theorem gamma0CompletedLattice_eq_eisenstein (Q : ℕ) [NeZero Q] (z : ℍ)
    {s : ℂ} (hs : 1 < s.re) :
    gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z s =
      gamma0CompletionFactor Q s * gamma0Eisenstein Q s z := by
  rw [gamma0CompletedLattice_eq_sieved Q (Nat.pos_of_neZero Q) z hs,
    gamma0SievedSeries_eq_LFunction_eisenstein Q hs z, gamma0CompletionFactor]
  ring

end
end Dubon2026
