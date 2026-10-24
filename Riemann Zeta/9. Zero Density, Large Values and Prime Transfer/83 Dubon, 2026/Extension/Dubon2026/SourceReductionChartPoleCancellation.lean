import Dubon2026.SourceReductionOffFiberVanishing
import Dubon2026.SourceCurveChartIntegralCriterion

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> principal-divisor pushforward.
Cancelling poles away from one exact chart-reduction fiber transfers the
required vanishing bound to the residue field. The existing characteristic-
zero chart-integrality criterion replaces the external valuation-intersection
construction; residue integrality removes the chart-surjectivity premise.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin.
The finite-product order calculation reuses the local proof in
SourceCurveGaloisPrincipalDegree. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Place
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem ord_prod {K E ι : Type*} [Field K] [Field E] [Algebra K E]
    (v : Place K E) (s : Finset ι) (g : ι → E) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.sum_cons,
      v.ord_mul (hg i (Finset.mem_cons_self i s))
        (Finset.prod_ne_zero_iff.mpr fun j hj => hg j (Finset.mem_cons_of_mem hj)),
      ih fun j hj => hg j (Finset.mem_cons_of_mem hj)]

private theorem ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E]
    (v : Place K E) (f : E) (n : ℕ) : v.ord (f ^ n) = (n : ℤ) * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

theorem chart_pole_cancellation [IsAlgClosed L] [CharZero L]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (f : R.integers) (hfi : IsIntegral (Algebra.adjoin L {(x : F)}) (f : F))
    (hf : R.residue f ≠ 0)
    (Q : Place (ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord (f : F))
    (T : Finset (Place L F))
    (hT : ∀ P, P ∈ T ↔ (D P ≠ 0 ∧
      (∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits))
    (h : R.integers) (hh : IsIntegral (Algebra.adjoin L {(x : F)}) (h : F))
    (hvan : ∀ P ∈ T, (h : F) = 0 ∨ D P ≤ P.ord (h : F)) :
    R.residue h = 0 ∨ Q.ord (R.residue f) ≤ Q.ord (R.residue h) := by
  classical
  by_cases hh0 : (h : F) = 0
  · left; rw [show h = 0 from Subtype.ext hh0, map_zero]
  by_cases hresh : R.residue h = 0
  · exact Or.inl hresh
  right
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  have hf0 : (f : F) ≠ 0 := fun h0 => hf (by rw [show f = 0 from Subtype.ext h0, map_zero])

  let B : Finset (Place L F) :=
    D.support.filter fun P => (x : F) ∈ P.toValuationSubring ∧ P ∉ T
  have hy : ∀ P : Place L F, ∃ y : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (y : F) ∧
      (y : F) ≠ 0 ∧ (P ∈ B → 0 < P.ord (y : F)) ∧ R.residue y ≠ 0 ∧
      Q.ord (R.residue y) = 0 := by
    intro P
    by_cases hPB : P ∈ B
    · obtain ⟨hPD, hxP, hPT⟩ := Finset.mem_filter.mp hPB
      obtain ⟨y, h1, h2, h3, h4, h5⟩ := exists_off_fiber_vanishing R x hx hfin hdeg Q hQ P hxP
        (fun hc => hPT ((hT P).mpr ⟨Finsupp.mem_support_iff.mp hPD, hc⟩))
      exact ⟨y, h1, h2, fun _ => h3, h4, h5⟩
    · refine ⟨1, ?_, by simp, fun h => absurd h hPB, by simp, by rw [map_one, Q.ord_one]⟩
      have : IsIntegral (Algebra.adjoin L {(x : F)}) (1 : F) := isIntegral_one
      simpa using this
  choose y hyint hy0 hyord hyres hyQ using hy
  let U : R.integers := ∏ P ∈ B, y P ^ (D P).toNat
  have hUF : (U : F) = ∏ P ∈ B, (y P : F) ^ (D P).toNat := by
    simp only [U]; push_cast; rfl
  have hUint : IsIntegral (Algebra.adjoin L {(x : F)}) (U : F) := by
    rw [hUF]; exact IsIntegral.prod _ fun P _ => (hyint P).pow _
  have hU0 : (U : F) ≠ 0 := by
    rw [hUF]; exact Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (hy0 P)
  have hresU : R.residue U = ∏ P ∈ B, R.residue (y P) ^ (D P).toNat := by
    simp only [U, map_prod, map_pow]
  have hresU0 : R.residue U ≠ 0 := by
    rw [hresU]; exact Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (hyres P)
  have hordU : Q.ord (R.residue U) = 0 := by
    rw [hresU, ord_prod Q B _ fun P _ => pow_ne_zero _ (hyres P)]
    exact Finset.sum_eq_zero fun P _ => by rw [ord_pow, hyQ, mul_zero]
  obtain ⟨uf, huf⟩ := R.isUnit_of_residue_ne_zero hf
  have hufinv : (((uf⁻¹ : R.integersˣ) : R.integers) : F) = (f : F)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← huf]
    exact_mod_cast congrArg (fun z : R.integers => (z : F)) uf.inv_mul
  let g : R.integers := U * h * ↑(uf⁻¹)
  have hgF : (g : F) = (U : F) * h * (f : F)⁻¹ := by
    simp only [g]; push_cast; rw [hufinv]
  have hg0 : (g : F) ≠ 0 := by
    rw [hgF]; exact mul_ne_zero (mul_ne_zero hU0 hh0) (inv_ne_zero hf0)

  have hgmem : ∀ P : Place L F, (x : F) ∈ P.toValuationSubring →
      (g : F) ∈ P.toValuationSubring := by
    intro P hxP
    rw [P.mem_iff_ord_nonneg, hgF, P.ord_mul (mul_ne_zero hU0 hh0) (inv_ne_zero hf0),
      P.ord_mul hU0 hh0, P.ord_inv, ← hD]
    have hUnn : 0 ≤ P.ord (U : F) :=
      ord_nonneg_of_mem P (P.mem_of_integral_adjoin hxP hUint)
    have hhnn : 0 ≤ P.ord (h : F) :=
      ord_nonneg_of_mem P (P.mem_of_integral_adjoin hxP hh)
    have hDnn : 0 ≤ D P :=
      (hD P).symm ▸ ord_nonneg_of_mem P (P.mem_of_integral_adjoin hxP hfi)
    by_cases hPT : P ∈ T
    · rcases hvan P hPT with h0 | h0
      · exact absurd h0 hh0
      · omega
    by_cases hDP : D P = 0
    · omega
    have hPB : P ∈ B := Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hDP, hxP, hPT⟩
    have hDU : D P ≤ P.ord (U : F) := by
      rw [hUF, ord_prod P B _ fun P' _ => pow_ne_zero _ (hy0 P')]
      have h1 : D P ≤ P.ord ((y P : F) ^ (D P).toNat) := by
        rw [ord_pow]
        have := hyord P hPB
        calc D P = ((D P).toNat : ℤ) * 1 := by rw [mul_one, Int.toNat_of_nonneg hDnn]
          _ ≤ ((D P).toNat : ℤ) * P.ord (y P : F) :=
            mul_le_mul_of_nonneg_left (by omega) (Int.natCast_nonneg _)
      refine h1.trans ?_
      exact Finset.single_le_sum (f := fun P' => P.ord ((y P' : F) ^ (D P').toNat))
        (fun P' _ => by
          show 0 ≤ P.ord ((y P' : F) ^ (D P').toNat)
          rw [ord_pow]
          exact mul_nonneg (Int.natCast_nonneg _) (ord_nonneg_of_mem P
            (P.mem_of_integral_adjoin hxP (hyint P'))))
        hPB
    omega
  have hgint : IsIntegral (Algebra.adjoin L {(x : F)}) (g : F) :=
    isIntegral_adjoin_of_nonnegative_orders (x : F)
      (transcendental_of_residue_transcendental R x hx) (g : F)
      (fun P hP => P.ord_nonneg_of_mem (hgmem P (P.mem_of_ord_nonneg hP)))
  have hresg : R.residue g ∈ Q.toValuationSubring :=
    Q.mem_of_integral_adjoin hQ
      (isIntegral_residue_of_integral_chart R x hx hfin hdeg g hgint)
  have hgf : g * f = U * h := by
    simp only [g]; rw [← huf, mul_assoc, Units.inv_mul, mul_one]
  have hres : R.residue g * R.residue f = R.residue U * R.residue h := by
    rw [← map_mul, hgf, map_mul]
  have hresg0 : R.residue g ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hres
    exact mul_ne_zero hresU0 hresh hres.symm
  have h1 := congrArg Q.ord hres
  rw [Q.ord_mul hresg0 hf, Q.ord_mul hresU0 hresh, hordU, zero_add] at h1
  have h2 := ord_nonneg_of_mem Q hresg
  omega

end
end Dubon2026.SourceCurve.RegularProlongation
