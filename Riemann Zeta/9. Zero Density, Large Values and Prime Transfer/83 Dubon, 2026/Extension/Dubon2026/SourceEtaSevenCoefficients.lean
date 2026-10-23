import Dubon2026.SourceJFiniteCoefficientLists

/-! Exact first seven coefficients of the actual integral j numerator.
These supply the finite coefficient comparison identifying the actual integral
prime-two modular polynomial, then its cyclic-quotient roots and finite inertia
census on the DUB-17 / DUB-18 good-reduction chain. Adapted from the selected
coeff_jNum_le_six proof, anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the existing proved eta-product
truncation; do not repeat its topological infinite-product argument. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries
open JCoeff

theorem lowCoeffs_etaProd : LowCoeffs etaProd [1, -1, -1, 0, 0, 1, 0] := by

  have hP : LowCoeffs (∏ n ∈ Finset.range 7, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) [1, -1, -1, 0, 0, 1, 0] := by
    have f := fun m (hm : 0 < m) => LowCoeffs.one_sub_X_pow (R := ℤ) m 7 hm
    have h1 : LowCoeffs (∏ n ∈ Finset.range 1, (1 - (X : ℤ⟦X⟧) ^ (n + 1))) [1, -1, 0, 0, 0, 0, 0] := by
      rw [Finset.prod_range_one]; exact (f 1 (by norm_num)).congr (by decide)
    have h2 := (h1.mul (f 2 (by norm_num))).congr (M := [1, -1, -1, 1, 0, 0, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h2
    have h3 := (h2.mul (f 3 (by norm_num))).congr (M := [1, -1, -1, 0, 1, 1, -1]) (by decide)
    rw [← Finset.prod_range_succ] at h3
    have h4 := (h3.mul (f 4 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 2, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h4
    have h5 := (h4.mul (f 5 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 1]) (by decide)
    rw [← Finset.prod_range_succ] at h5
    have h6 := (h5.mul (f 6 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h6
    have h7 := (h6.mul (f 7 (by norm_num))).congr (M := [1, -1, -1, 0, 0, 1, 0]) (by decide)
    rw [← Finset.prod_range_succ] at h7
    exact h7
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  rw [PrimeDegreeAux.coeff_etaProd_eq_coeff_partialEta (n := 6) (by omega)]
  exact hP i (by simpa using hi)


end
end Dubon2026.SourceFunctionField
