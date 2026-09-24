import TaoTrudgianYang2025.ClassicalReflectedFourier

/-!
# All-index reflected families

Reality of the literal reflected coefficients merges the two Poisson signs
before dyadic selection. Every original index receives a bounded positive
height shift and a dyadic label. No large-cardinality subset is substituted
for the original family, so the full perturbation-energy estimate applies.
-/

noncomputable section
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

theorem norm_wideDirichletPoly_normalizedTypeIReflectedCoeff_neg
    (sigma t : ℝ) (Q k M : ℕ) :
    ‖wideDirichletPoly Q k (normalizedTypeIReflectedCoeff sigma M) (-t)‖ =
      ‖wideDirichletPoly Q k (normalizedTypeIReflectedCoeff sigma M) t‖ := by
  have hcoeff (n : ℕ) :
      star (normalizedTypeIReflectedCoeff sigma M n) =
        normalizedTypeIReflectedCoeff sigma M n :=
    congr_fun (conjugateCoeffs_normalizedTypeIReflectedCoeff sigma M) n
  have hstar :
      star (wideDirichletPoly Q k (normalizedTypeIReflectedCoeff sigma M) t) =
        wideDirichletPoly Q k (normalizedTypeIReflectedCoeff sigma M) (-t) := by
    unfold wideDirichletPoly
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [star_mul, hcoeff,
      mul_comm (star ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))
        (normalizedTypeIReflectedCoeff sigma M n)]
    congr 1
    have hnArg : (n : ℂ).arg ≠ Real.pi := by
      change (((n : ℝ) : ℂ).arg ≠ Real.pi)
      rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_ne_zero.symm
    have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
    rw [hnCast]
    have hConj := Complex.cpow_conj (((n : ℝ) : ℂ))
      (-(t : ℂ) * Complex.I) hnArg
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I] at hConj
    simp only [Complex.ofReal_neg]
    convert hConj.symm using 1
    ring_nf
  rw [← hstar, norm_star]

theorem exists_positive_reflected_shift
    (sigma t H S : ℝ) (M : ℕ)
    (hEach :
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(t + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (t - u)‖)) :
    ∃ v ∈ Set.Icc (-H) H,
      S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (t + v)‖ := by
  rcases hEach with ⟨u,hu,hlarge⟩ | ⟨u,hu,hlarge⟩
  · refine ⟨u,hu,?_⟩
    simpa only [norm_wideDirichletPoly_normalizedTypeIReflectedCoeff_neg] using hlarge
  · refine ⟨-u,?_,?_⟩
    · rcases hu with ⟨hl,hu⟩
      constructor <;> linarith
    · simpa only [sub_eq_add_neg] using hlarge

theorem exists_reflected_bounded_dyadic_family
    {ι : Type*} [Fintype ι]
    (M : ℕ) (sigma H S : ℝ) (W : ι → ℝ) (hM : 1 < M)
    (hEach : ∀ x,
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (-(W x + u))‖) ∨
      (∃ u ∈ Set.Icc (-H) H,
        S < ‖wideDirichletPoly 1 (Nat.clog 2 M)
          (normalizedTypeIReflectedCoeff sigma M) (W x - u)‖)) :
    ∃ (W' : ι → ℝ) (label : ι → Fin (Nat.clog 2 M)),
      (∀ x, |W' x - W x| ≤ H) ∧
      (∀ x, S / Nat.clog 2 M ≤
        ‖dirichletPoly (2 ^ (label x).val)
          (normalizedTypeIReflectedCoeff sigma M) (W' x)‖) ∧
      approximateAdditiveEnergyOf 1 W ≤
        (4 * Nat.ceil (1 + 4 * H) + 6) *
          approximateAdditiveEnergyOf 1 W' := by
  classical
  have hshift := fun x => exists_positive_reflected_shift sigma (W x) H S M (hEach x)
  choose v hv hwide using hshift
  let W' := fun x => W x+v x
  have hJ : 0 < Nat.clog 2 M := Nat.clog_pos Nat.one_lt_two hM
  have hblocks : ∀ x, ∃ j ∈ Finset.range (Nat.clog 2 M),
      S / Nat.clog 2 M ≤
        ‖dirichletPoly (2 ^ j) (normalizedTypeIReflectedCoeff sigma M) (W' x)‖ := by
    intro x
    simpa only [mul_one] using
      exists_large_dyadic_block 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (W' x) S hJ (hwide x).le
  choose j hj hblock using hblocks
  let label : ι → Fin (Nat.clog 2 M) := fun x => ⟨j x,Finset.mem_range.mp (hj x)⟩
  have hpert : ∀ x, |W' x-W x| ≤ H := by
    intro x
    change |W x+v x-W x| ≤ H
    rw [add_sub_cancel_left]
    exact abs_le.mpr (hv x)
  refine ⟨W',label,hpert,?_,?_⟩
  · exact hblock
  · calc
      approximateAdditiveEnergyOf 1 W ≤
          approximateAdditiveEnergyOf (1+4*H) W' :=
        approximateAdditiveEnergyOf_perturbation_le hpert
      _ ≤ (4 * Nat.ceil (1+4*H)+6) * approximateAdditiveEnergyOf 1 W' :=
        approximateAdditiveEnergyOf_le_natCeil_mul_unit _ _

end TaoTrudgianYang2025
