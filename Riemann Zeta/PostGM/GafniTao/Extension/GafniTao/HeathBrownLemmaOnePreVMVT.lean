import GafniTao.HeathBrownCellAveraging

/-!
# Heath-Brown Lemma 1 before inserting VMVT

This is the exact coefficient-cell/Hölder conclusion.  Its majorant retains
the literal Vinogradov solution count, derivative pair count, interior-index
count, and coefficient-cell volume.
-/

open Finset MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownIntegratedMajorant
    (N k H s : ℕ) (f : ℝ → ℝ) : ENNReal :=
  (fordVinogradovMomentNat s (k - 1) H : ENNReal) ^
      (1 / (2 * (s : ℝ))) *
    ENNReal.ofReal
      (((heathBrownPairCount N k H f).card : ℝ) *
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
      (1 / (2 * (s : ℝ))) *
    ENNReal.ofReal
      (((N - H : ℕ) : ℝ) *
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹))) ^
      (1 - 1 / (s : ℝ))

theorem heathBrownIntegratedWeyl_le_majorant
    {N k H s Q : ℕ} (hH : 2 ≤ H) (hQH : Q ≤ H) (hs : 1 ≤ s)
    (f : ℝ → ℝ) :
    heathBrownIntegratedWeyl N k H Q f ≤
      heathBrownIntegratedMajorant N k H s f := by
  exact heathBrown_integratedWeyl_le_source_moments N k H hH f hQH hs

theorem card_Ico_one_le (Q : ℕ) :
    (Finset.Ico 1 Q).card ≤ Q := by
  simp

/-- The literal averaged Weyl-sum estimate at all source cell centres. -/
theorem heathBrown_centerWeyl_sum_preVMVT
    {N k H Q s : ℕ} (hH : 2 ≤ H) (hQ : 1 ≤ Q) (hQH : Q ≤ H)
    (hs : 1 ≤ s) (f : ℝ → ℝ) :
    ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) *
        ∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k Q
            (heathBrownCoefficientCenter k f n)‖ ≤
      (1 + ENNReal.ofReal (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * Q) *
        heathBrownIntegratedMajorant N k H s f := by
  have hcell := heathBrown_cellwise_center_lintegral_le
    (N := N) (k := k) (H := H) (Q := Q) hH hQ hQH f
  have hQmajor := heathBrownIntegratedWeyl_le_majorant
    (N := N) (k := k) (H := H) (s := s) hH hQH hs f
  have hjmajor (j : ℕ) (hj : j ∈ Finset.Ico 1 Q) :
      heathBrownIntegratedWeyl N k H j f ≤
        heathBrownIntegratedMajorant N k H s f :=
    heathBrownIntegratedWeyl_le_majorant hH
      ((Finset.mem_Ico.mp hj).2.le.trans hQH) hs f
  have hsum :
      (∑ j ∈ Finset.Ico 1 Q,
          heathBrownIntegratedWeyl N k H j f) ≤
        Q * heathBrownIntegratedMajorant N k H s f := by
    calc
      (∑ j ∈ Finset.Ico 1 Q,
          heathBrownIntegratedWeyl N k H j f) ≤
          ∑ _j ∈ Finset.Ico 1 Q,
            heathBrownIntegratedMajorant N k H s f := by
        exact Finset.sum_le_sum fun j hj => hjmajor j hj
      _ = (Finset.Ico 1 Q).card *
          heathBrownIntegratedMajorant N k H s f := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Q * heathBrownIntegratedMajorant N k H s f := by
        gcongr
        exact_mod_cast card_Ico_one_le Q
  calc
    _ ≤ heathBrownIntegratedWeyl N k H Q f +
        ENNReal.ofReal (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
          ∑ j ∈ Finset.Ico 1 Q,
            heathBrownIntegratedWeyl N k H j f := hcell
    _ ≤ heathBrownIntegratedMajorant N k H s f +
        ENNReal.ofReal (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
          (Q * heathBrownIntegratedMajorant N k H s f) := by
      gcongr
    _ = (1 + ENNReal.ofReal (2 * Real.pi * ((k : ℝ) ^ 2 / H)) * Q) *
        heathBrownIntegratedMajorant N k H s f := by ring

#print axioms heathBrownIntegratedWeyl_le_majorant
#print axioms card_Ico_one_le
#print axioms heathBrown_centerWeyl_sum_preVMVT

end

end GafniTao
