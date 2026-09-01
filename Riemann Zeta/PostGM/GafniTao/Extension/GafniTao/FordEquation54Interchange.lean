import GafniTao.FordEquation54Fourier

/-!
# Ford Lemma 5.1: justified lattice/tuple interchange for equation (5.4)

The all-lattice weighted moment is expanded over the two finite `B^s` tuple
families, and the absolutely convergent lattice series for each tuple pair is
evaluated by the product tent identity.  This supplies the exact equality
immediately before Ford discards the unit complex coefficients and restricts
to the resonant displacement sets.
-/

open Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

/-- One tuple-pair summand of the all-lattice series in (5.4). -/
def fordLemma51TuplePairLatticeTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) (c : Fin k → ℤ) : ℂ :=
  fordLemma51TupleCoefficient k M r s B t z x y *
    ((fordLemma51WeightProduct k r M c : ℂ) *
      fordAdditiveCharacter
        (fordLemma51DifferencePhase k t z
          (fordLemma51DifferenceVector k s B x y) c))

/-- The evaluated tent product attached to one tuple pair. -/
def fordLemma51TuplePairTentTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) : ℂ :=
  fordLemma51TupleCoefficient k M r s B t z x y *
    ∏ j : Fin k, fordLemma51CoordinateTentValue k r M j
      (fordLemma51DifferenceCoordinate k t z
        (fordLemma51DifferenceVector k s B x y))

theorem hasSum_fordLemma51TuplePairLatticeTerm
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) (x y : FordLemma51BTuple s B) :
    HasSum (fordLemma51TuplePairLatticeTerm k M r s B t z x y)
      (fordLemma51TuplePairTentTerm k M r s B t z x y) := by
  unfold fordLemma51TuplePairLatticeTerm fordLemma51TuplePairTentTerm
  exact (hasSum_fordLemma51DifferenceLattice hr hM t z
    (fordLemma51DifferenceVector k s B x y)).mul_left
      (fordLemma51TupleCoefficient k M r s B t z x y)

theorem hasSum_fordLemma51AllTuplePairLatticeTerms
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    HasSum
      (fun c : Fin k → ℤ =>
        ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairLatticeTerm k M r s B t z x y c)
      (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentTerm k M r s B t z x y) := by
  have hy (x : FordLemma51BTuple s B) :
      HasSum
        (fun c : Fin k → ℤ =>
          ∑ y : FordLemma51BTuple s B,
            fordLemma51TuplePairLatticeTerm k M r s B t z x y c)
        (∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentTerm k M r s B t z x y) := by
    simpa using hasSum_sum (s := Finset.univ)
      (fun y _hy => hasSum_fordLemma51TuplePairLatticeTerm hr hM B t z x y)
  simpa using hasSum_sum (s := Finset.univ) (fun x _hx => hy x)

theorem fordLemma51WeightedLatticeTerm_eq_tuplePairSum
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    (((fordLemma51WeightProduct k r M c *
        ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) : ℝ≥0) : ℝ) : ℂ) =
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairLatticeTerm k M r s B t z x y c := by
  have hexpand := fordLemma51_nnnorm_pow_eq_differenceTupleSum
    k M r s B t z c
  rw [show
    (((fordLemma51WeightProduct k r M c *
        ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) : ℝ≥0) : ℝ) : ℂ) =
      (fordLemma51WeightProduct k r M c : ℂ) *
        ((‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
          (2 * s) : ℝ≥0) : ℂ) by push_cast; rfl]
  rw [hexpand]
  unfold fordLemma51TuplePairLatticeTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  ring

/-- The exact, absolutely convergent equality preceding Ford's inequality
(5.4).  The left side is the literal weighted all-lattice moment; the right
side exposes every tuple pair and its product of source tents. -/
theorem hasSum_fordLemma51WeightedLatticeMoment_complex
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    HasSum
      (fun c : Fin k → ℤ =>
        (((fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
            (2 * s) : ℝ≥0) : ℝ) : ℂ))
      (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentTerm k M r s B t z x y) := by
  exact HasSum.congr_fun
    (hasSum_fordLemma51AllTuplePairLatticeTerms hr hM B t z)
    (fun c => fordLemma51WeightedLatticeTerm_eq_tuplePairSum
      k M r s B t z c)

theorem fordLemma51WeightedLatticeTsum_eq_tupleTentSum
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    ((((∑' c : Fin k → ℤ,
        fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
            (2 * s) : ℝ≥0) : ℝ)) : ℂ) =
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentTerm k M r s B t z x y := by
  let f : (Fin k → ℤ) → ℝ≥0 := fun c =>
    fordLemma51WeightProduct k r M c *
      ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s)
  have hnn : HasSum f (∑' c, f c) :=
    (summable_fordLemma51WeightedLatticeMoment hr hM B t z).hasSum
  have hre : HasSum (fun c => (f c : ℝ)) (((∑' c, f c) : ℝ≥0) : ℝ) :=
    NNReal.hasSum_coe.mpr hnn
  have hc : HasSum (fun c => ((f c : ℝ) : ℂ))
      (((((∑' c, f c) : ℝ≥0) : ℝ)) : ℂ) :=
    Complex.hasSum_ofReal.mpr hre
  exact hc.unique (hasSum_fordLemma51WeightedLatticeMoment_complex hr hM B t z)

theorem norm_fordLemma51TupleCoefficient
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    ‖fordLemma51TupleCoefficient k M r s B t z x y‖ = 1 := by
  unfold fordLemma51TupleCoefficient
  rw [norm_mul, Complex.norm_conj]
  simp only [norm_prod, norm_fordLemma51Epsilon,
    prod_const_one, one_mul]

#print axioms hasSum_fordLemma51TuplePairLatticeTerm
#print axioms hasSum_fordLemma51AllTuplePairLatticeTerms
#print axioms fordLemma51WeightedLatticeTerm_eq_tuplePairSum
#print axioms hasSum_fordLemma51WeightedLatticeMoment_complex
#print axioms fordLemma51WeightedLatticeTsum_eq_tupleTentSum
#print axioms norm_fordLemma51TupleCoefficient

end

end GafniTao
