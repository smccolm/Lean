import GafniTao.FordCubicSum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrability of Ford's cubic majorant

Ford's Lemma 7.3 extends a finite interval integral to the positive half-line.
Here we prove that this is legitimate for the literal cubic exponent, using
an explicit exponential majorant on the tail.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

def fordCubicTailStart (D sigma t : ℝ) : ℝ :=
  max 1 ((fordCubicA sigma + 1) / fordCubicB D t)

theorem fordCubicExponent_le_neg_of_tail
    {D sigma t x : ℝ} (hD : 0 < D) (ht : 1 < t)
    (hx : fordCubicTailStart D sigma t ≤ x) :
    fordCubicExponent D sigma t x ≤ -x := by
  have hB : 0 < fordCubicB D t := fordCubicB_pos hD ht
  have hx1 : 1 ≤ x :=
    (le_max_left 1 ((fordCubicA sigma + 1) /
      fordCubicB D t)).trans hx
  have hx0 : 0 ≤ x := by linarith
  have hratio :
      (fordCubicA sigma + 1) / fordCubicB D t ≤ x :=
    (le_max_right 1 ((fordCubicA sigma + 1) /
      fordCubicB D t)).trans hx
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hratioSq :
      (fordCubicA sigma + 1) / fordCubicB D t ≤ x ^ 2 :=
    hratio.trans hxx
  have hmul := mul_le_mul_of_nonneg_left hratioSq hB.le
  have hAB : fordCubicA sigma + 1 ≤ fordCubicB D t * x ^ 2 := by
    calc
      fordCubicA sigma + 1 = fordCubicB D t *
          ((fordCubicA sigma + 1) / fordCubicB D t) := by
            field_simp [hB.ne']
      _ ≤ fordCubicB D t * x ^ 2 := hmul
  have hxmul := mul_le_mul_of_nonneg_right hAB hx0
  unfold fordCubicExponent
  nlinarith

theorem integrableOn_fordCubicExp_Ioi
    {D sigma t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    IntegrableOn (fun x => Real.exp (fordCubicExponent D sigma t x))
      (Set.Ioi 0) := by
  let M := fordCubicTailStart D sigma t
  have hM : 0 ≤ M := by
    dsimp [M, fordCubicTailStart]
    exact le_trans (by norm_num) (le_max_left _ _)
  have hcont : Continuous
      (fun x => Real.exp (fordCubicExponent D sigma t x)) := by
    unfold fordCubicExponent fordCubicA fordCubicB
    fun_prop
  have hcompact : IntegrableOn
      (fun x => Real.exp (fordCubicExponent D sigma t x))
      (Set.Ioc 0 M) := by
    exact hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htail : IntegrableOn
      (fun x => Real.exp (fordCubicExponent D sigma t x))
      (Set.Ioi M) := by
    apply (integrableOn_exp_neg_Ioi M).mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (fordCubicExponent_le_neg_of_tail hD ht hx.le)
  have hunion := hcompact.union htail
  have hsets : Set.Ioc (0 : ℝ) M ∪ Set.Ioi M = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact lt_of_le_of_lt hM hx
    · intro hx
      by_cases hxm : x ≤ M
      · exact Or.inl ⟨hx, hxm⟩
      · exact Or.inr (lt_of_not_ge hxm)
  rwa [hsets] at hunion

theorem intervalIntegral_fordCubicExp_le_Ioi
    {D sigma t : ℝ} (hD : 0 < D) (ht : 1 < t) (r : ℕ) :
    (∫ x in (0 : ℝ)..r,
        Real.exp (fordCubicExponent D sigma t x)) ≤
      ∫ x in Set.Ioi (0 : ℝ),
        Real.exp (fordCubicExponent D sigma t x) := by
  have hint := integrableOn_fordCubicExp_Ioi (sigma := sigma) hD ht
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg r)]
  apply setIntegral_mono_set hint _ Set.Ioc_subset_Ioi_self.eventuallyLE
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (Real.exp_pos _).le

#print axioms fordCubicExponent_le_neg_of_tail
#print axioms integrableOn_fordCubicExp_Ioi
#print axioms intervalIntegral_fordCubicExp_le_Ioi

end

end GafniTao
