import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.ZMod
import RiemannZeta.External.PNT.ResidueCalcOnRectangles
import RiemannZeta.GuthMaynard.QuadraticDivisor

open Complex Finset Filter Topology
open HurwitzZeta
open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# Periodic Estermann functions for divisor Voronoi summation

For a periodic coefficient `Φ : ZMod q → ℂ`, the divisor-twisted
Dirichlet series has coefficient

`n ↦ d(n) Φ(n)`.

The exact finite identity below expresses this coefficient as a sum of
Dirichlet convolutions of periodic functions.  Consequently its analytic
continuation is a finite sum of products of Mathlib's `ZMod.LFunction`s.
This is the analytic object underlying DFI Proposition 1; its functional
equation is assembled from `ZMod.LFunction_one_sub` rather than postulated as
a Bessel-transform axiom.
-/

/-- The periodic indicator of a residue class. -/
def residueIndicator (q : ℕ) (a : ZMod q) (n : ℕ) : ℂ :=
  if (n : ZMod q) = a then 1 else 0

/-- The divisor coefficient twisted by a periodic function. -/
noncomputable def periodicDivisorCoeff (q : ℕ) (Φ : ZMod q → ℂ) (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ) * Φ n

/-- Finite residue-pair convolution model for the periodic divisor
coefficient. -/
noncomputable def periodicDivisorConvolutionCoeff
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (n : ℕ) : ℂ :=
  ∑ a : ZMod q, ∑ b : ZMod q,
    Φ (a * b) *
      (LSeries.convolution (residueIndicator q a) (residueIndicator q b)) n

lemma residueIndicator_apply (q : ℕ) (a : ZMod q) (n : ℕ) :
    residueIndicator q a n = if (n : ZMod q) = a then 1 else 0 := rfl

/-- A residue pair selects exactly those divisor pairs with the specified
residues. -/
theorem periodicDivisorConvolutionCoeff_eq_sum_antidiagonal
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (n : ℕ) :
    periodicDivisorConvolutionCoeff q Φ n =
      ∑ p ∈ n.divisorsAntidiagonal, Φ ((p.1 * p.2 : ℕ) : ZMod q) := by
  unfold periodicDivisorConvolutionCoeff
  simp only [LSeries.convolution_def, Finset.mul_sum]
  calc
    (∑ a : ZMod q, ∑ b : ZMod q,
        ∑ p ∈ n.divisorsAntidiagonal,
          Φ (a * b) *
            (residueIndicator q a p.1 * residueIndicator q b p.2)) =
        ∑ p ∈ n.divisorsAntidiagonal,
          ∑ a : ZMod q, ∑ b : ZMod q,
            Φ (a * b) *
              (residueIndicator q a p.1 * residueIndicator q b p.2) := by
      rw [Finset.sum_comm]
      conv_lhs =>
        enter [2, a]
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.sum_comm]
    _ = ∑ p ∈ n.divisorsAntidiagonal, Φ ((p.1 * p.2 : ℕ) : ZMod q) := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp [residueIndicator, mul_comm]

/-- The convolution model is exactly `d(n)Φ(n)` for every positive index.
The `n = 0` convention of `Nat.divisorsAntidiagonal` is handled separately. -/
theorem periodicDivisorConvolutionCoeff_eq
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) {n : ℕ} (_hn : n ≠ 0) :
    periodicDivisorConvolutionCoeff q Φ n = periodicDivisorCoeff q Φ n := by
  rw [periodicDivisorConvolutionCoeff_eq_sum_antidiagonal, periodicDivisorCoeff]
  have hTerm : ∀ p ∈ n.divisorsAntidiagonal,
      Φ ((p.1 * p.2 : ℕ) : ZMod q) = Φ n := by
    intro p hp
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
  calc
    ∑ p ∈ n.divisorsAntidiagonal, Φ ((p.1 * p.2 : ℕ) : ZMod q) =
        ∑ _p ∈ n.divisorsAntidiagonal, Φ n :=
      Finset.sum_congr rfl hTerm
    _ = (n.divisorsAntidiagonal.card : ℂ) * Φ n := by simp
    _ = (n.divisors.card : ℂ) * Φ n := by
      congr 2
      have hInj : Set.InjOn Prod.fst (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
        intro p hp r hr hpr
        have hpProd := (Nat.mem_divisorsAntidiagonal.mp hp).1
        have hrProd := (Nat.mem_divisorsAntidiagonal.mp hr).1
        apply Prod.ext
        · exact hpr
        · have hpPos : 0 < p.1 :=
            Nat.pos_of_ne_zero (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp)
          apply Nat.eq_of_mul_eq_mul_left hpPos
          calc
            p.1 * p.2 = n := hpProd
            _ = r.1 * r.2 := hrProd.symm
            _ = p.1 * r.2 := by rw [hpr]
      calc
        n.divisorsAntidiagonal.card =
            (n.divisorsAntidiagonal.image Prod.fst).card :=
          (Finset.card_image_iff.mpr hInj).symm
        _ = n.divisors.card := by rw [Nat.image_fst_divisorsAntidiagonal]

/-- Meromorphic continuation of the divisor series with periodic
coefficient `Φ`, expressed entirely through Mathlib's periodic L-functions. -/
noncomputable def periodicEstermann (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  ∑ a : ZMod q, ∑ b : ZMod q,
    Φ (a * b) * ZMod.LFunction (fun x => if x = a then 1 else 0) s *
      ZMod.LFunction (fun x => if x = b then 1 else 0) s

/-- Exact Dirichlet-series agreement for the finite L-function continuation
of the periodic Estermann function in the half-plane of absolute
convergence. -/
theorem periodicEstermann_eq_LSeries (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {s : ℂ} (hs : 1 < s.re) :
    periodicEstermann q Φ s = LSeries (periodicDivisorCoeff q Φ) s := by
  unfold periodicEstermann
  have hIndicatorSummable (a : ZMod q) :
      LSeriesSummable (residueIndicator q a) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    by_cases hna : (n : ZMod q) = a <;> simp [residueIndicator, hna]
  calc
    (∑ a : ZMod q, ∑ b : ZMod q,
        Φ (a * b) * ZMod.LFunction (fun x => if x = a then 1 else 0) s *
          ZMod.LFunction (fun x => if x = b then 1 else 0) s) =
        ∑ a : ZMod q, ∑ b : ZMod q,
          Φ (a * b) *
            LSeries (LSeries.convolution
              (residueIndicator q a) (residueIndicator q b)) s := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [ZMod.LFunction_eq_LSeries _ hs, ZMod.LFunction_eq_LSeries _ hs]
      have ha : (fun n : ℕ => (fun x : ZMod q => if x = a then 1 else 0) n) =
          residueIndicator q a := by
        funext n
        simp [residueIndicator, eq_comm]
      have hb : (fun n : ℕ => (fun x : ZMod q => if x = b then 1 else 0) n) =
          residueIndicator q b := by
        funext n
        simp [residueIndicator, eq_comm]
      rw [ha, hb,
        LSeries_convolution' (hIndicatorSummable a) (hIndicatorSummable b)]
      ring
    _ = LSeries (periodicDivisorConvolutionCoeff q Φ) s := by
      let F : ZMod q → ZMod q → ℕ → ℂ := fun a b =>
        Φ (a * b) • LSeries.convolution
          (residueIndicator q a) (residueIndicator q b)
      have hF (a b : ZMod q) : LSeriesSummable (F a b) s :=
        ((hIndicatorSummable a).convolution (hIndicatorSummable b)).smul (Φ (a * b))
      have hOuter : LSeriesSummable (∑ a : ZMod q, ∑ b : ZMod q, F a b) s := by
        apply LSeriesSummable.sum
        intro a _ha
        apply LSeriesSummable.sum
        intro b _hb
        exact hF a b
      have hCoeff : (∑ a : ZMod q, ∑ b : ZMod q, F a b) =
          periodicDivisorConvolutionCoeff q Φ := by
        funext n
        simp [F, periodicDivisorConvolutionCoeff]
      rw [← hCoeff]
      symm
      calc
        LSeries (∑ a : ZMod q, ∑ b : ZMod q, F a b) s =
            ∑ a : ZMod q, LSeries (∑ b : ZMod q, F a b) s := by
          rw [LSeries_sum]
          intro a _ha
          exact LSeriesSummable.sum (fun b _hb => hF a b)
        _ = ∑ a : ZMod q, ∑ b : ZMod q, LSeries (F a b) s := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [LSeries_sum]
          intro b _hb
          exact hF a b
        _ = ∑ a : ZMod q, ∑ b : ZMod q,
            Φ (a * b) * LSeries (LSeries.convolution
              (residueIndicator q a) (residueIndicator q b)) s := by
          apply Finset.sum_congr rfl
          intro a _ha
          apply Finset.sum_congr rfl
          intro b _hb
          change LSeries (Φ (a * b) • LSeries.convolution
              (residueIndicator q a) (residueIndicator q b)) s = _
          rw [LSeries_smul]
    _ = LSeries (periodicDivisorCoeff q Φ) s := by
      apply LSeries_congr
      intro n hn
      rcases eq_or_ne n 0 with rfl | hn
      · simp [periodicDivisorConvolutionCoeff, periodicDivisorCoeff,
          LSeries.convolution_map_zero]
      · exact periodicDivisorConvolutionCoeff_eq q Φ hn

/-- Absolute convergence of the periodic divisor Dirichlet series in its
source half-plane.  This is the summability statement underlying the
right-line Fubini step in divisor Voronoi summation. -/
theorem periodicDivisorCoeff_LSeriesSummable (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (periodicDivisorCoeff q Φ) s := by
  have hIndicatorSummable (a : ZMod q) :
      LSeriesSummable (residueIndicator q a) s := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1) _ hs
    intro n hn
    by_cases hna : (n : ZMod q) = a <;> simp [residueIndicator, hna]
  let F : ZMod q → ZMod q → ℕ → ℂ := fun a b =>
    Φ (a * b) • LSeries.convolution
      (residueIndicator q a) (residueIndicator q b)
  have hF (a b : ZMod q) : LSeriesSummable (F a b) s :=
    ((hIndicatorSummable a).convolution (hIndicatorSummable b)).smul (Φ (a * b))
  have hOuter : LSeriesSummable (∑ a : ZMod q, ∑ b : ZMod q, F a b) s := by
    apply LSeriesSummable.sum
    intro a _ha
    apply LSeriesSummable.sum
    intro b _hb
    exact hF a b
  have hCoeff : (∑ a : ZMod q, ∑ b : ZMod q, F a b) =
      periodicDivisorConvolutionCoeff q Φ := by
    funext n
    simp [F, periodicDivisorConvolutionCoeff]
  rw [hCoeff] at hOuter
  exact (LSeriesSummable_congr s
    (fun hn => periodicDivisorConvolutionCoeff_eq q Φ hn)).mp hOuter

/-- The exact reflected expression occurring in the functional equation of a
periodic L-function. -/
noncomputable def periodicLFunctionDual (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s - 1) * (2 * Real.pi : ℂ) ^ (-s) * Gamma s *
    (cexp (Real.pi * I * s / 2) * ZMod.LFunction (ZMod.dft Ψ) s +
      cexp (-Real.pi * I * s / 2) *
        ZMod.LFunction (ZMod.dft fun x => Ψ (-x)) s)

/-- Mathlib's periodic L-function functional equation, packaged in the exact
form used by the Estermann continuation. -/
theorem periodicLFunction_one_sub (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {s : ℂ} (hsPole : s ≠ 1)
    (hsGamma : ∀ n : ℕ, s ≠ -n) :
    ZMod.LFunction Ψ (1 - s) = periodicLFunctionDual q Ψ s := by
  exact ZMod.LFunction_one_sub Ψ hsGamma (Or.inr hsPole)

/-- Reflected finite product representing the dual side of the periodic
Estermann functional equation. -/
noncomputable def periodicEstermannDual (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  ∑ a : ZMod q, ∑ b : ZMod q,
    Φ (a * b) *
      periodicLFunctionDual q (fun x => if x = a then 1 else 0) s *
      periodicLFunctionDual q (fun x => if x = b then 1 else 0) s

/-- Exact functional equation for the finite periodic Estermann
continuation.  Expanding the two discrete Fourier transforms gives the four
oscillatory Voronoi kernels; no transform formula is assumed. -/
theorem periodicEstermann_one_sub (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {s : ℂ} (hsPole : s ≠ 1)
    (hsGamma : ∀ n : ℕ, s ≠ -n) :
    periodicEstermann q Φ (1 - s) = periodicEstermannDual q Φ s := by
  unfold periodicEstermann periodicEstermannDual
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [periodicLFunction_one_sub q _ hsPole hsGamma,
    periodicLFunction_one_sub q _ hsPole hsGamma]

/-- The discrete Fourier transform of one residue-class indicator is the
corresponding additive character.  This is the exact finite Fourier step
which turns the reflected Estermann expression into the four Voronoi
oscillatory kernels. -/
theorem zmod_dft_residueIndicator (q : ℕ) [NeZero q]
    (a k : ZMod q) :
    ZMod.dft (fun x : ZMod q => if x = a then 1 else 0) k =
      ZMod.stdAddChar (-(a * k)) := by
  rw [ZMod.dft_apply]
  simp

/-- Source-oriented left-line form of the periodic Estermann functional
equation.  A point on `Re s = d < 0` is reflected to the absolutely
convergent half-plane `Re (1-s) > 1`. -/
theorem periodicEstermann_leftLine_reflection (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {d u : ℝ} (hd : d < 0) :
    periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) =
      periodicEstermannDual q Φ
        (((1 - d : ℝ) : ℂ) - (u : ℂ) * I) := by
  let s : ℂ := ((1 - d : ℝ) : ℂ) - (u : ℂ) * I
  have hsPole : s ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simp [s] at hr
    linarith
  have hsGamma : ∀ n : ℕ, s ≠ -n := by
    intro n h
    have hr := congrArg Complex.re h
    simp [s] at hr
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  have hfe := periodicEstermann_one_sub q Φ hsPole hsGamma
  change periodicEstermann q Φ (1 - s) = periodicEstermannDual q Φ s at hfe
  have hsEq : 1 - s = (d : ℂ) + (u : ℂ) * I := by
    dsimp [s]
    push_cast
    ring
  rw [hsEq] at hfe
  exact hfe

/-- The coefficient of the double pole at `s = 1` of the periodic
Estermann function.  Written as a finite residue-class average, this is the
leading coefficient of the logarithmic main term after Mellin inversion. -/
noncomputable def periodicEstermannLeadingCoeff (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) : ℂ :=
  ((q : ℂ) ⁻¹) ^ 2 * ∑ a : ZMod q, ∑ b : ZMod q, Φ (a * b)

private theorem residueIndicator_LFunction_residue_one
    (q : ℕ) [NeZero q] (a : ZMod q) :
    Tendsto
      (fun s : ℂ => (s - 1) *
        ZMod.LFunction (fun x : ZMod q => if x = a then 1 else 0) s)
      (nhdsWithin (1 : ℂ) {1}ᶜ) (nhds ((q : ℂ) ⁻¹)) := by
  convert
    (ZMod.LFunction_residue_one
      (fun x : ZMod q => if x = a then (1 : ℂ) else 0)) using 1
  rw [← Finset.sum_div]
  simp

/-- Exact leading Laurent coefficient at the unique possible pole.  This is
the pole calculation used in the divisor Voronoi formula; it follows from
Mathlib's residue theorem for periodic L-functions and finite summation. -/
theorem periodicEstermann_leading_term (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * periodicEstermann q Φ s)
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (periodicEstermannLeadingCoeff q Φ)) := by
  have hterm (a b : ZMod q) :
      Tendsto
        (fun s : ℂ => Φ (a * b) *
          ((s - 1) * ZMod.LFunction
            (fun x : ZMod q => if x = a then 1 else 0) s) *
          ((s - 1) * ZMod.LFunction
            (fun x : ZMod q => if x = b then 1 else 0) s))
        (nhdsWithin (1 : ℂ) {1}ᶜ)
        (nhds (Φ (a * b) * (q : ℂ) ⁻¹ * (q : ℂ) ⁻¹)) :=
    (tendsto_const_nhds.mul
      (residueIndicator_LFunction_residue_one q a)).mul
        (residueIndicator_LFunction_residue_one q b)
  have hsum : Tendsto
      (fun s : ℂ => ∑ a : ZMod q, ∑ b : ZMod q,
        Φ (a * b) *
          ((s - 1) * ZMod.LFunction
            (fun x : ZMod q => if x = a then 1 else 0) s) *
          ((s - 1) * ZMod.LFunction
            (fun x : ZMod q => if x = b then 1 else 0) s))
      (nhdsWithin (1 : ℂ) {1}ᶜ)
      (nhds (∑ a : ZMod q, ∑ b : ZMod q,
        Φ (a * b) * (q : ℂ) ⁻¹ * (q : ℂ) ⁻¹)) := by
    exact tendsto_finsetSum _ fun a _ =>
      tendsto_finsetSum _ fun b _ => hterm a b
  convert hsum using 1
  · funext s
    unfold periodicEstermann
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  · unfold periodicEstermannLeadingCoeff
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring

/-- Away from `s = 1`, the periodic Estermann continuation is holomorphic. -/
theorem differentiableAt_periodicEstermann (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ (periodicEstermann q Φ) s := by
  unfold periodicEstermann
  apply DifferentiableAt.fun_sum
  intro a _ha
  apply DifferentiableAt.fun_sum
  intro b _hb
  exact ((ZMod.differentiableAt_LFunction _ s (Or.inl hs)).const_mul _).mul
    (ZMod.differentiableAt_LFunction _ s (Or.inl hs))

/-- The entire part of a Hurwitz zeta function after removal of its canonical
simple pole.  Mathlib chooses the `Gammaℝ`-regularized principal part, which
is especially convenient for the functional equation. -/
noncomputable def hurwitzZetaRegularized (a : UnitAddCircle) (s : ℂ) : ℂ :=
  hurwitzZeta a s - 1 / (s - 1) / Gammaℝ s

theorem differentiable_hurwitzZetaRegularized (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaRegularized a) := by
  intro s
  by_cases hs : s = 1
  · subst s
    exact differentiableAt_hurwitzZeta_sub_one_div a
  · unfold hurwitzZetaRegularized
    have hpole : DifferentiableAt ℂ
        (fun z : ℂ => 1 / (z - 1) / Gammaℝ z) s := by
      have hsub : DifferentiableAt ℂ (fun z : ℂ => z - 1) s :=
        differentiableAt_id.sub_const 1
      simpa [div_eq_mul_inv] using
        ((hsub.inv (sub_ne_zero.mpr hs)).mul
          (differentiable_Gammaℝ_inv s))
    exact (differentiableAt_hurwitzZeta a hs).sub hpole

/-- Entire regular part of a periodic L-function. -/
noncomputable def periodicLFunctionRegularized (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (-s) * ∑ j : ZMod q, Ψ j *
    hurwitzZetaRegularized (ZMod.toAddCircle j) s

theorem differentiable_periodicLFunctionRegularized (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    Differentiable ℂ (periodicLFunctionRegularized q Ψ) := by
  intro s
  unfold periodicLFunctionRegularized
  apply DifferentiableAt.mul
  · fun_prop
  · apply DifferentiableAt.fun_sum
    intro j _hj
    exact (differentiable_hurwitzZetaRegularized
      (ZMod.toAddCircle j) s).const_mul (Ψ j)

/-- Canonical entire continuation of `(s-1)L(s,Ψ)`. -/
noncomputable def periodicLFunctionPoleCleared (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  (s - 1) * periodicLFunctionRegularized q Ψ s +
    (q : ℂ) ^ (-s) * (∑ j : ZMod q, Ψ j) * (Gammaℝ s) ⁻¹

theorem differentiable_periodicLFunctionPoleCleared (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) :
    Differentiable ℂ (periodicLFunctionPoleCleared q Ψ) := by
  intro s
  unfold periodicLFunctionPoleCleared
  exact ((differentiableAt_id.sub_const 1).mul
      (differentiable_periodicLFunctionRegularized q Ψ s)).add
    (((by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s).mul
      (differentiableAt_const _)).mul (differentiable_Gammaℝ_inv s))

/-- Off the pole, the entire pole-cleared continuation agrees exactly with
`(s-1)L(s,Ψ)`. -/
theorem periodicLFunctionPoleCleared_eq (q : ℕ) [NeZero q]
    (Ψ : ZMod q → ℂ) {s : ℂ} (hs : s ≠ 1) :
    periodicLFunctionPoleCleared q Ψ s =
      (s - 1) * ZMod.LFunction Ψ s := by
  unfold periodicLFunctionPoleCleared periodicLFunctionRegularized
    hurwitzZetaRegularized ZMod.LFunction
  have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hsum :
      (∑ j : ZMod q, Ψ j *
        (hurwitzZeta (ZMod.toAddCircle j) s -
          1 / (s - 1) / Gammaℝ s)) =
        (∑ j : ZMod q, Ψ j * hurwitzZeta (ZMod.toAddCircle j) s) -
          (∑ j : ZMod q, Ψ j) * (1 / (s - 1) / Gammaℝ s) := by
    rw [Finset.sum_mul]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  field_simp [hsSub]
  ring

/-- Entire numerator obtained after clearing the double Estermann pole. -/
noncomputable def periodicEstermannPoleCleared (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  ∑ a : ZMod q, ∑ b : ZMod q, Φ (a * b) *
    periodicLFunctionPoleCleared q (fun x => if x = a then 1 else 0) s *
    periodicLFunctionPoleCleared q (fun x => if x = b then 1 else 0) s

theorem differentiable_periodicEstermannPoleCleared (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) :
    Differentiable ℂ (periodicEstermannPoleCleared q Φ) := by
  intro s
  unfold periodicEstermannPoleCleared
  apply DifferentiableAt.fun_sum
  intro a _ha
  apply DifferentiableAt.fun_sum
  intro b _hb
  exact ((differentiable_periodicLFunctionPoleCleared q _ s).const_mul _).mul
    (differentiable_periodicLFunctionPoleCleared q _ s)

/-- Exact agreement between the pole-cleared entire numerator and the
periodic Estermann function away from `s=1`. -/
theorem periodicEstermannPoleCleared_eq (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) {s : ℂ} (hs : s ≠ 1) :
    periodicEstermannPoleCleared q Φ s =
      (s - 1) ^ 2 * periodicEstermann q Φ s := by
  unfold periodicEstermannPoleCleared periodicEstermann
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [periodicLFunctionPoleCleared_eq q _ hs,
    periodicLFunctionPoleCleared_eq q _ hs]
  ring

/-- The residue coefficient of the periodic Estermann function at its
possible double pole.  It is the derivative of the entire pole-cleared
numerator, represented by Mathlib's differentiable slope. -/
noncomputable def periodicEstermannResidueCoeff (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) : ℂ :=
  dslope (periodicEstermannPoleCleared q Φ) 1 1

/-- Entire remainder after removing both Laurent principal-part terms. -/
noncomputable def periodicEstermannRegularPart (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) (s : ℂ) : ℂ :=
  dslope (dslope (periodicEstermannPoleCleared q Φ) 1) 1 s

private theorem differentiable_dslope_entire {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (a : ℂ) :
    Differentiable ℂ (dslope F a) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope
    (s := Set.univ) (c := a) univ_mem).2 hF.differentiableOn

theorem differentiable_periodicEstermannRegularPart (q : ℕ) [NeZero q]
    (Φ : ZMod q → ℂ) :
    Differentiable ℂ (periodicEstermannRegularPart q Φ) := by
  unfold periodicEstermannRegularPart
  exact differentiable_dslope_entire
    (differentiable_dslope_entire
      (differentiable_periodicEstermannPoleCleared q Φ) 1) 1

/-- Exact Laurent decomposition of the periodic Estermann continuation.
The first term has integral zero around a rectangle, the second contributes
the residue, and the last term is entire.  This is the contour-shift form of
the divisor Voronoi main-term calculation. -/
theorem periodicEstermann_eq_principalParts_add_regular
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) {s : ℂ} (hs : s ≠ 1) :
    periodicEstermann q Φ s =
      periodicEstermannPoleCleared q Φ 1 / (s - 1) ^ 2 +
        periodicEstermannResidueCoeff q Φ / (s - 1) +
        periodicEstermannRegularPart q Φ s := by
  let H : ℂ → ℂ := periodicEstermannPoleCleared q Φ
  let D : ℂ → ℂ := dslope H 1
  let R : ℂ → ℂ := dslope D 1
  have hHD := sub_smul_dslope H 1 s
  have hDR := sub_smul_dslope D 1 s
  have hNumerator : H s = H 1 + (s - 1) * D 1 + (s - 1) ^ 2 * R s := by
    change (s - 1) * D s = H s - H 1 at hHD
    change (s - 1) * R s = D s - D 1 at hDR
    have hFirst : H s = H 1 + (s - 1) * D s := by
      calc
        H s = H 1 + (H s - H 1) := by ring
        _ = H 1 + (s - 1) * D s := by rw [hHD]
    have hSecond : D s = D 1 + (s - 1) * R s := by
      calc
        D s = D 1 + (D s - D 1) := by ring
        _ = D 1 + (s - 1) * R s := by rw [hDR]
    rw [hFirst, hSecond]
    ring
  have hCleared := periodicEstermannPoleCleared_eq q Φ hs
  change H s = (s - 1) ^ 2 * periodicEstermann q Φ s at hCleared
  change periodicEstermann q Φ s =
      H 1 / (s - 1) ^ 2 + D 1 / (s - 1) + R s
  have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hE : periodicEstermann q Φ s = H s / (s - 1) ^ 2 := by
    field_simp [hsSub]
    simpa [mul_comm] using hCleared.symm
  rw [hE, hNumerator]
  field_simp [hsSub]

/-- Exact product decomposition against an entire Mellin multiplier.  The
pure double-pole term has zero residue.  The displayed simple-pole numerator
takes the value `A * G' 1 + B * G 1` at the pole, which is precisely the DFI
logarithmic main-term coefficient. -/
theorem periodicEstermann_mul_eq_double_add_simple_add_regular
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    {s : ℂ} (hs : s ≠ 1) :
    periodicEstermann q Φ s * G s =
      periodicEstermannPoleCleared q Φ 1 * G 1 / (s - 1) ^ 2 +
        (periodicEstermannPoleCleared q Φ 1 * dslope G 1 s +
          periodicEstermannResidueCoeff q Φ * G s) / (s - 1) +
        periodicEstermannRegularPart q Φ s * G s := by
  rw [periodicEstermann_eq_principalParts_add_regular q Φ hs,
    dslope_of_ne G hs]
  unfold slope
  simp only [vsub_eq_sub, smul_eq_mul]
  have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp [hsSub]
  ring

/-- The simple-pole numerator in the product decomposition is entire. -/
theorem differentiable_periodicEstermann_simpleNumerator
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) :
    Differentiable ℂ (fun s =>
      periodicEstermannPoleCleared q Φ 1 * dslope G 1 s +
        periodicEstermannResidueCoeff q Φ * G s) := by
  exact (differentiable_dslope_entire hG 1).const_mul _ |>.add (hG.const_mul _)

/-- Value of the simple-pole numerator: the derivative term from the double
pole plus the original simple-pole coefficient. -/
theorem periodicEstermann_simpleNumerator_one
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ) :
    periodicEstermannPoleCleared q Φ 1 * dslope G 1 1 +
        periodicEstermannResidueCoeff q Φ * G 1 =
      periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
        periodicEstermannResidueCoeff q Φ * G 1 := by
  rw [dslope_same]

end RiemannZeta.GuthMaynard
