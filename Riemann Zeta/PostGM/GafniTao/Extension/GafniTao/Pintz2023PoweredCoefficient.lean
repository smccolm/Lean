import GafniTao.Pintz2023PoweredBlock
import GafniTao.Pintz2023IntervalPower
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Pintz (2023), equation (4.19): powered-coefficient normalization

The exact zero-padded powered coefficient is identified with the convolution
on the true selected interval, times the common real-line factor `m^-beta`.
This makes the divisor and ordered-factorization losses from
`Pintz2023IntervalPower` available to the actual coefficient passed to the
large-values theorem.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The true support of a selected dyadic block after intersecting it with
the source interval `(X,Y]`. -/
def pintz2023SelectedInterval (X Y U : ℕ) : Finset ℕ :=
  (Finset.Ioc U (2 * U)).filter fun n => n ∈ Finset.Ioc X Y

theorem pintz2023SelectedInterval_subset
    (X Y U : ℕ) :
    pintz2023SelectedInterval X Y U ⊆ Finset.Ioc U (2 * U) :=
  Finset.filter_subset _ _

/-- Exact coefficient identity for the possibly truncated selected interval.
Tuples meeting a zero-padded coordinate vanish before the support is
restricted, and every remaining tuple has the common factor `m^-beta`. -/
theorem pintz2023SelectedPowerCoeff_eq_interval
    (X Y U h m : ℕ) (beta : ℝ) :
    pintz2023SelectedPowerCoeff X Y U h beta m =
      pintz2023IntervalPowerCoeff X
        (pintz2023SelectedInterval X Y U) h m *
          (m : ℂ) ^ (-(beta : ℂ)) := by
  classical
  let allTuples :=
    (Fintype.piFinset
      (fun (_ : Fin h) => Finset.Ioc U (2 * U))).filter
        (fun p => (∏ j : Fin h, p j) = m)
  let selectedTuples :=
    (Fintype.piFinset
      (fun (_ : Fin h) => pintz2023SelectedInterval X Y U)).filter
        (fun p => (∏ j : Fin h, p j) = m)
  have hsubset : selectedTuples ⊆ allTuples := by
    intro p hp
    dsimp only [selectedTuples, allTuples] at hp ⊢
    rw [Finset.mem_filter] at hp ⊢
    refine ⟨?_, hp.2⟩
    rw [Fintype.mem_piFinset] at hp ⊢
    intro j
    exact pintz2023SelectedInterval_subset X Y U (hp.1 j)
  have hvanish : ∀ p ∈ allTuples, p ∉ selectedTuples →
      ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j) = 0 := by
    intro p hpAll hpNotSelected
    dsimp only [allTuples] at hpAll
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hpAll
    have hpNotSupport : p ∉ Fintype.piFinset
        (fun (_ : Fin h) => pintz2023SelectedInterval X Y U) := by
      intro hpSupport
      apply hpNotSelected
      dsimp only [selectedTuples]
      exact Finset.mem_filter.mpr ⟨hpSupport, hpAll.2⟩
    rw [Fintype.mem_piFinset] at hpNotSupport
    push Not at hpNotSupport
    obtain ⟨j, hj⟩ := hpNotSupport
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    unfold pintz2023SelectedInterval at hj
    rw [Finset.mem_filter] at hj
    have hsource : p j ∉ Finset.Ioc X Y := by
      intro hpSource
      exact hj ⟨hpAll.1 j, hpSource⟩
    simp [pintz2023LocalizedLineCoeff, hsource]
  have hrestrict :
      (∑ p ∈ allTuples,
          ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j)) =
        ∑ p ∈ selectedTuples,
          ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j) := by
    symm
    apply Finset.sum_subset hsubset
    intro p hpAll hpNotSelected
    exact hvanish p hpAll hpNotSelected
  rw [pintz2023SelectedPowerCoeff, finitePowCoeff]
  change (∑ p ∈ allTuples,
      ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j)) = _
  calc
    (∑ p ∈ allTuples,
        ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j)) =
      ∑ p ∈ selectedTuples,
        ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j) := hrestrict
    _ = pintz2023IntervalPowerCoeff X
          (pintz2023SelectedInterval X Y U) h m *
            (m : ℂ) ^ (-(beta : ℂ)) := by
      rw [pintz2023IntervalPowerCoeff, Finset.sum_mul]
      change (∑ p ∈ selectedTuples,
          ∏ j : Fin h, pintz2023LocalizedLineCoeff X Y beta (p j)) =
        ∑ p ∈ selectedTuples,
          (∏ j : Fin h, pintz2023Coeff X (p j)) *
            (m : ℂ) ^ (-(beta : ℂ))
      apply Finset.sum_congr rfl
      intro p hp
      dsimp only [selectedTuples] at hp
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hp
      have hsource : ∀ j : Fin h, p j ∈ Finset.Ioc X Y := by
        intro j
        exact (Finset.mem_filter.mp (hp.1 j)).2
      simp only [pintz2023LocalizedLineCoeff, if_pos (hsource _)]
      rw [Finset.prod_mul_distrib, prod_natCast_cpow_eq, hp.2]

/-- The exact powered line coefficient inherits the interval-convolution
bound with its full real decay `m^-beta`. -/
theorem norm_pintz2023SelectedPoweredLineCoeff_le_rpow
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y U m : ℕ) (beta : ℝ),
        0 < U → 0 < m →
        ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤
          C * (m : ℝ) ^ (epsilon - beta) := by
  obtain ⟨C, hC, hCoeff⟩ :=
    pintz2023IntervalPowerCoeff_bound_native h epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro X Y U m beta hU hm
  rw [pintz2023SelectedPoweredLineCoeff_eq,
    pintz2023SelectedPowerCoeff_eq_interval X Y U h m beta,
    norm_mul]
  have hmReal : (0 : ℝ) < m := by exact_mod_cast hm
  have hCpow := hCoeff X U m (pintz2023SelectedInterval X Y U)
    (pintz2023SelectedInterval_subset X Y U) hU hm
  have hNormPower :
      ‖((m : ℂ) ^ (-(beta : ℂ)))‖ = (m : ℝ) ^ (-beta) := by
    change ‖(((m : ℝ) : ℂ) ^ (-(beta : ℂ)))‖ = _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hmReal]
    rfl
  rw [hNormPower]
  calc
    ‖pintz2023IntervalPowerCoeff X
        (pintz2023SelectedInterval X Y U) h m‖ * (m : ℝ) ^ (-beta) ≤
        (C * (m : ℝ) ^ epsilon) * (m : ℝ) ^ (-beta) := by
      gcongr
    _ = C * (m : ℝ) ^ (epsilon - beta) := by
      rw [mul_assoc, ← Real.rpow_add hmReal]
      congr 2
    _ = C * (m : ℝ) ^ (epsilon - beta) := rfl

/-- If the coefficient epsilon is at most the physical real part, the exact
powered coefficient is in particular bounded by a uniform constant. -/
theorem norm_pintz2023SelectedPoweredLineCoeff_le
    (h : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (X Y U m : ℕ) (beta : ℝ),
        0 < U → 0 < m → epsilon ≤ beta →
        ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤ C := by
  obtain ⟨C, hC, hCoeff⟩ :=
    norm_pintz2023SelectedPoweredLineCoeff_le_rpow h epsilon hepsilon
  refine ⟨C, hC, ?_⟩
  intro X Y U m beta hU hm hepsilonBeta
  calc
    ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤
        C * (m : ℝ) ^ (epsilon - beta) := hCoeff X Y U m beta hU hm
    _ ≤ C * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm.ne'))
        (sub_nonpos.mpr hepsilonBeta)
    _ = C := mul_one C

/-- Constant normalization gives literal unit coefficients on every ordinary
dyadic subblock of the powered support. -/
theorem norm_pintz2023_normalized_powered_coeff_le_one
    {X Y U h m : ℕ} {beta C : ℝ}
    (hC : 0 < C)
    (hBound : ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m‖ ≤ C) :
    ‖pintz2023SelectedPoweredLineCoeff X Y U h beta m / (C : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC,
    div_le_one hC]
  exact hBound

#print axioms pintz2023SelectedPowerCoeff_eq_interval
#print axioms norm_pintz2023SelectedPoweredLineCoeff_le_rpow
#print axioms norm_pintz2023SelectedPoweredLineCoeff_le
#print axioms norm_pintz2023_normalized_powered_coeff_le_one

end

end GafniTao
