import Dubon2026.Gamma0EpsteinSieve

/-! # The genuine general-level Eisenstein continuation and its exact residue -/

namespace Dubon2026

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-- Each finite lattice coefficient is an entire function of the spectral parameter. -/
theorem differentiable_gamma0LatticeCoefficient (Q : ℕ) (hQ : 0 < Q) (d : Q.divisors) :
    Differentiable ℂ (fun s : ℂ =>
      (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s)) := by
  intro s
  exact ((differentiableAt_id.neg).const_cpow (Or.inl (mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hQ))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.pos_of_mem_divisors d.property)))))).const_mul _

/-- The finite completed lattice expression is holomorphic away from its two possible poles. -/
theorem differentiableAt_gamma0CompletedLattice (Q : ℕ) (hQ : 0 < Q) (z : ℍ)
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (gamma0CompletedLattice Q hQ z) s := by
  apply DifferentiableAt.fun_sum
  intro d hd
  exact (differentiable_gamma0LatticeCoefficient Q hQ d s).mul
    (differentiableAt_latticeCompletedMellin _ hs0 hs1)

/-- The exact complex Möbius divisor identity reuses the proved real totient formula. -/
theorem sum_moebius_div_complex (Q : ℕ) (hQ : Q ≠ 0) :
    (∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) / d.val) =
      (Q.totient : ℂ) / Q := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) (sum_moebius_div_eq_totient_div Q hQ)
  push_cast at h
  rw [← Finset.sum_coe_sort] at h
  exact h

/-- The genuine completed general-level lattice expression has residue phi(Q)/(2Q^2). -/
theorem gamma0CompletedLattice_residue_one (Q : ℕ) (hQ : 0 < Q) (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * gamma0CompletedLattice Q hQ z s)
      (𝓝[≠] 1) (𝓝 ((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2))) := by
  have ht (d : Q.divisors) : Tendsto
      (fun s : ℂ => (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
        ((s - 1) * latticeCompletedMellin
          (rectangularLatticePoint Q d.val hQ (Nat.pos_of_mem_divisors d.property) z) s))
      (𝓝[≠] 1)
      (𝓝 ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val)⁻¹ * (1 / 2))) := by
    have hc : Tendsto (fun s : ℂ =>
        (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s))
        (𝓝[≠] 1) (𝓝 ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-(1 : ℂ)))) :=
      (differentiable_gamma0LatticeCoefficient Q hQ d 1).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds
    simpa only [Complex.cpow_neg_one] using hc.mul
      (latticeCompletedMellin_residue_one
        (rectangularLatticePoint Q d.val hQ (Nat.pos_of_mem_divisors d.property) z))
  have h := tendsto_finsetSum Finset.univ (fun d _ => ht d)
  have he : (∑ d : Q.divisors,
      (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val)⁻¹ * (1 / 2)) =
        (Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2) := by
    calc
      _ = (∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) / d.val) / (2 * Q) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro d hd
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [sum_moebius_div_complex Q (Nat.ne_of_gt hQ)]
        ring
  rw [he] at h
  convert h using 1
  funext s
  rw [gamma0CompletedLattice, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- The continuation of the actual primitive Gamma0(Q) Eisenstein series. -/
def gamma0EisensteinContinuation (Q : ℕ) [NeZero Q] (z : ℍ) (s : ℂ) : ℂ :=
  gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z s / gamma0CompletionFactor Q s

/-- The constructed continuation equals the actual convergent primitive-row series. -/
theorem gamma0EisensteinContinuation_eq (Q : ℕ) [NeZero Q] (z : ℍ)
    {s : ℂ} (hs : 1 < s.re) :
    gamma0EisensteinContinuation Q z s = gamma0Eisenstein Q s z := by
  rw [gamma0EisensteinContinuation, gamma0CompletedLattice_eq_eisenstein Q z hs]
  exact mul_div_cancel_left₀ _ (gamma0CompletionFactor_ne_zero Q (by linarith))

/-- The genuine general-level continuation is holomorphic in Re(s)>1/2 away from s=1. -/
theorem differentiableAt_gamma0EisensteinContinuation (Q : ℕ) [NeZero Q] (z : ℍ)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (gamma0EisensteinContinuation Q z) s := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re] at hs
    linarith
  exact (differentiableAt_gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z hs0 hs1).div
    (differentiableAt_gamma0CompletionFactor Q hs) (gamma0CompletionFactor_ne_zero Q hs)

/-- The exact pole residue of the actual primitive general-level Eisenstein continuation. -/
theorem gamma0EisensteinContinuation_residue_one (Q : ℕ) [NeZero Q] (z : ℍ) :
    Tendsto (fun s : ℂ => (s - 1) * gamma0EisensteinContinuation Q z s)
      (𝓝[≠] 1)
      (𝓝 ((Real.pi : ℂ) * Q.totient /
        (2 * (Q : ℂ) ^ 2 * DirichletCharacter.LFunctionTrivChar Q 2))) := by
  have hd : Tendsto (gamma0CompletionFactor Q) (𝓝[≠] (1 : ℂ))
      (𝓝 (gamma0CompletionFactor Q 1)) :=
    (differentiableAt_gamma0CompletionFactor Q (s := 1) (by norm_num)).continuousAt.tendsto
      |>.mono_left nhdsWithin_le_nhds
  have h := (gamma0CompletedLattice_residue_one Q (Nat.pos_of_neZero Q) z).div hd
    (gamma0CompletionFactor_ne_zero Q (s := 1) (by norm_num))
  change Tendsto (fun s : ℂ => ((s - 1) * gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z s) /
    gamma0CompletionFactor Q s) (𝓝[≠] 1)
    (𝓝 (((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) / gamma0CompletionFactor Q 1)) at h
  have he : ((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) / gamma0CompletionFactor Q 1 =
      (Real.pi : ℂ) * Q.totient /
        (2 * (Q : ℂ) ^ 2 * DirichletCharacter.LFunctionTrivChar Q 2) := by
    rw [gamma0CompletionFactor_one]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
    ring
  simpa only [he, gamma0EisensteinContinuation, mul_div_assoc] using h

end
end Dubon2026
