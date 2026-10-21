import Dubon2026.SourceCurveExactDifferentialResidue

/-! DUB-17/18 -> regular differential dimension -> Riemann--Roch
-> global residue identity -> characteristic-zero rational-function atoms.
The residue of df/f is the actual normalized order of f. The unit part
has integral derivative, and the uniformizer power contributes its exponent.
This local identity does not assert the global residue theorem.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open KaehlerDifferential
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
variable [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]

theorem coordinateDerivation_log_unit_mul_zpow
    (u : v.toValuationSubringˣ) (n : ℤ) :
    v.coordinateDerivation (((u : v.toValuationSubring) : F) * v.uniformizer ^ n) /
        (((u : v.toValuationSubring) : F) * v.uniformizer ^ n) =
      v.coordinateDerivation ((u : v.toValuationSubring) : F) /
        ((u : v.toValuationSubring) : F) + (n : F) * v.uniformizer⁻¹ := by
  have hu : ((u : v.toValuationSubring) : F) ≠ 0 := by exact_mod_cast u.ne_zero
  rw [Derivation.leibniz, v.coordinateDerivation_zpow]
  simp only [smul_eq_mul, zpow_sub₀ v.uniformizer_ne_zero, zpow_one]
  field_simp [hu, zpow_ne_zero n v.uniformizer_ne_zero]
  ring

variable [Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄K]]
variable [Algebra.IsSeparable K v.ResidueField]

theorem localResidueScalar_logarithmic {f : F} (hf : f ≠ 0) :
    v.localResidueScalar (v.coordinateDerivation f / f) = (v.ord f : K) := by
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf v.irreducible_uniformizerSubring
  change f = ((u : v.toValuationSubring) : F) * v.uniformizer ^ v.ord f at hu
  have hunit : ((u : v.toValuationSubring) : F)⁻¹ ∈ v.toValuationSubring := by
    apply v.mem_of_ord_nonneg
    rw [v.ord_inv, v.ord_coe_unit, neg_zero]
  have hreg : v.coordinateDerivation ((u : v.toValuationSubring) : F) /
      ((u : v.toValuationSubring) : F) ∈ v.toValuationSubring := by
    rw [div_eq_mul_inv]
    exact mul_mem
      (v.differentialCoeff_D_mem_of_mem (u : v.toValuationSubring).2) hunit
  have he := v.coordinateDerivation_log_unit_mul_zpow u (v.ord f)
  rw [← hu] at he
  rw [he, map_add, v.localResidueScalar_of_mem hreg, zero_add,
    ← map_intCast (algebraMap K F) (v.ord f), ← Algebra.smul_def, map_smul,
    v.localResidueScalar_uniformizer_inv, smul_eq_mul, mul_one]

theorem canonicalLocalResidueData_logarithmic
    (hres : Function.Bijective (algebraMap K v.ResidueField))
    (d : v.CanonicalLocalResidueDataK) {f : F} (hf : f ≠ 0) :
    d.res (v.differentialCoeff (D K F f) / f) = (v.ord f : v.ResidueField) := by
  rw [v.canonicalLocalResidueData_res_unique hres d]
  change algebraMap K v.ResidueField
    (v.localResidueScalar (v.coordinateDerivation f / f)) = _
  rw [v.localResidueScalar_logarithmic hf, map_intCast]

theorem localResidueScalar_power_differential [CharZero K]
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    {f : F} (hf : f ≠ 0) (n : ℤ) :
    v.localResidueScalar (f ^ n * v.coordinateDerivation f) =
      if n = -1 then (v.ord f : K) else 0 := by
  split_ifs with hn
  · rw [hn, zpow_neg_one, mul_comm, ← div_eq_mul_inv]
    exact v.localResidueScalar_logarithmic hf
  · have he := v.localResidueScalar_coordinateDerivation_eq_zero hres (f ^ (n + 1))
    simp only [Derivation.leibniz_zpow, smul_eq_mul, zsmul_eq_mul,
      show n + 1 - 1 = n by omega] at he
    rw [← map_intCast (algebraMap K F) (n + 1), ← Algebra.smul_def, map_smul,
      smul_eq_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (Int.cast_ne_zero.mpr (by omega))

theorem canonicalLocalResidueData_power_differential [CharZero K]
    (hres : Function.Bijective (algebraMap K v.ResidueField))
    (d : v.CanonicalLocalResidueDataK) {f : F} (hf : f ≠ 0) (n : ℤ) :
    d.res (f ^ n * v.differentialCoeff (D K F f)) =
      if n = -1 then (v.ord f : v.ResidueField) else 0 := by
  rw [v.canonicalLocalResidueData_res_unique hres d]
  change algebraMap K v.ResidueField
    (v.localResidueScalar (f ^ n * v.coordinateDerivation f)) = _
  rw [v.localResidueScalar_power_differential hres.surjective hf n]
  split_ifs <;> simp only [map_intCast, map_zero]

end
end Dubon2026.SourceCurve.Place
