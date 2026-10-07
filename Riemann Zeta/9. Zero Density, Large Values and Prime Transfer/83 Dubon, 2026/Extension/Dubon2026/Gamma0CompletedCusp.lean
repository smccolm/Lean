import Dubon2026.LatticeCuspResidue
import Dubon2026.Gamma0EisensteinResidue

/-! # The actual finite lattice assembly under the cusp integral -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory CongruenceSubgroup Matrix.SpecialLinearGroup Filter
open scoped Topology

noncomputable section

/-- The completed general-level lattice kernel is integrable against the actual cusp density. -/
theorem integrableOn_gamma0CompletedLattice_petersson {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    IntegrableOn (fun z : ℍ => gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z s *
      petersson k f f z) (gamma0FundamentalDomain Q) := by
  simp only [gamma0CompletedLattice, Finset.sum_mul, mul_assoc]
  apply integrable_finsetSum
  intro d hd
  simpa only [mul_assoc] using (integrableOn_rectangular_lattice_completed_petersson f Q d.val
    (Nat.pos_of_neZero Q) (Nat.pos_of_mem_divisors d.property) s).const_mul
      ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s))

/-- The literal completed general-level lattice integral against the actual Petersson density. -/
def gamma0CompletedCusp {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) : ℂ :=
  ∫ z : ℍ in gamma0FundamentalDomain Q,
    gamma0CompletedLattice Q (Nat.pos_of_neZero Q) z s * petersson k f f z

/-- The finite Möbius lattice expansion passes through the actual cusp integral. -/
theorem gamma0CompletedCusp_eq_sum {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) (s : ℂ) :
    gamma0CompletedCusp f s =
      ∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
        rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q)
          (Nat.pos_of_mem_divisors d.property) s := by
  simp only [gamma0CompletedCusp, gamma0CompletedLattice, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [integral_const_mul, integral_const_mul]
    rfl
  · intro d hd
    simpa only [mul_assoc] using (integrableOn_rectangular_lattice_completed_petersson f Q d.val
      (Nat.pos_of_neZero Q) (Nat.pos_of_mem_divisors d.property) s).const_mul
        ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s))

/-- The true completed cusp integral is holomorphic away from its two possible poles. -/
theorem differentiableAt_gamma0CompletedCusp {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (gamma0CompletedCusp f) s := by
  simp only [funext (gamma0CompletedCusp_eq_sum f)]
  apply DifferentiableAt.fun_sum
  intro d hd
  exact (differentiable_gamma0LatticeCoefficient Q (Nat.pos_of_neZero Q) d s).mul
    (differentiableAt_rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q)
      (Nat.pos_of_mem_divisors d.property) hs0 hs1)

/-- The completed cusp integral has residue phi(Q)/(2Q²) times the genuine Petersson pairing. -/
theorem gamma0CompletedCusp_residue_one {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k) :
    Tendsto (fun s : ℂ => (s - 1) * gamma0CompletedCusp f s) (𝓝[≠] 1)
      (𝓝 (((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) * cuspPetersson f f)) := by
  have ht (d : Q.divisors) : Tendsto
      (fun s : ℂ => (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s) *
        ((s - 1) * rectangularLatticeCuspCompleted f Q d.val (Nat.pos_of_neZero Q)
          (Nat.pos_of_mem_divisors d.property) s)) (𝓝[≠] 1)
      (𝓝 ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val)⁻¹ *
        (cuspPetersson f f / 2))) := by
    have hc : Tendsto (fun s : ℂ =>
        (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-s))
        (𝓝[≠] 1) (𝓝 ((ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val) ^ (-(1 : ℂ)))) :=
      (differentiable_gamma0LatticeCoefficient Q (Nat.pos_of_neZero Q) d 1).continuousAt.tendsto
        |>.mono_left nhdsWithin_le_nhds
    simpa only [Complex.cpow_neg_one] using hc.mul
      (rectangularLatticeCuspCompleted_residue_one f Q d.val (Nat.pos_of_neZero Q)
        (Nat.pos_of_mem_divisors d.property))
  have h := tendsto_finsetSum Finset.univ (fun d _ => ht d)
  have he : (∑ d : Q.divisors,
      (ArithmeticFunction.moebius d.val : ℂ) * ((Q : ℂ) * d.val)⁻¹ * (cuspPetersson f f / 2)) =
        ((Q.totient : ℂ) / (2 * (Q : ℂ) ^ 2)) * cuspPetersson f f := by
    calc
      _ = (∑ d : Q.divisors, (ArithmeticFunction.moebius d.val : ℂ) / d.val) /
          (2 * Q) * cuspPetersson f f := by
        rw [Finset.sum_div, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by
        rw [sum_moebius_div_complex Q (NeZero.ne Q)]
        ring
  rw [he] at h
  convert h using 1
  funext s
  rw [gamma0CompletedCusp_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

end
end Dubon2026
