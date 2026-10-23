import Dubon2026.SourceEtaSevenCoefficients

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

theorem lowCoeffs_dedekindEtaUnit : LowCoeffs dedekindEtaUnit [1, -24, 252, -1472, 4830, -6048, -16744] := by
  have e1 := lowCoeffs_etaProd
  have e2 := (e1.mul e1).congr (M := [1, -2, -1, 2, 1, 2, -2]) (by decide)
  have e4 := (e2.mul e2).congr (M := [1, -4, 2, 8, -5, -4, -10]) (by decide)
  have e8 := (e4.mul e4).congr (M := [1, -8, 20, 0, -70, 64, 56]) (by decide)
  have e16 := (e8.mul e8).congr (M := [1, -16, 104, -320, 260, 1248, -3712]) (by decide)
  have e24 := (e16.mul e8).congr (M := [1, -24, 252, -1472, 4830, -6048, -16744]) (by decide)
  have h24 : dedekindEtaUnit = ((((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd)))) *
      (((etaProd * etaProd) * (etaProd * etaProd)) * ((etaProd * etaProd) * (etaProd * etaProd))) := by
    rw [dedekindEtaUnit]; ring
  rw [h24]
  exact e24

theorem lowCoeffs_dedekindEtaUnitInv : LowCoeffs dedekindEtaUnitInv [1, 24, 324, 3200, 25650, 176256, 1073720] := by
  refine lowCoeffs_dedekindEtaUnit.invOfUnit (by rfl) constantCoeff_dedekindEtaUnit (by decide) (by decide)

theorem lowCoeffs_eisenstein4 : LowCoeffs eisenstein4 [1, 240, 2160, 6720, 17520, 30240, 60480] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  simp only [eisenstein4, coeff_mk]
  interval_cases i <;> decide

theorem lowCoeffs_jNum : LowCoeffs jNum [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600] := by
  have h4 := lowCoeffs_eisenstein4
  have h42 := (h4.mul h4).congr (M := [1, 480, 61920, 1050240, 7926240, 37500480, 135480960]) (by decide)
  have h43 := (h42.mul h4).congr (M := [1, 720, 179280, 16954560, 396974160, 4632858720, 34413301440]) (by decide)
  have hj := (h43.mul lowCoeffs_dedekindEtaUnitInv).congr
    (M := [1, 744, 196884, 21493760, 864299970, 20245856256, 333202640600]) (by decide)
  have : jNum = eisenstein4 * eisenstein4 * eisenstein4 * dedekindEtaUnitInv := by rw [jNum]; ring
  rw [this]; exact hj

theorem coeff_jNum_le_six :
    coeff 0 jNum = 1 ∧ coeff 1 jNum = 744 ∧ coeff 2 jNum = 196884 ∧ coeff 3 jNum = 21493760 ∧
      coeff 4 jNum = 864299970 ∧ coeff 5 jNum = 20245856256 ∧ coeff 6 jNum = 333202640600 := by
  have h := lowCoeffs_jNum
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide)⟩

end
end Dubon2026.SourceFunctionField
