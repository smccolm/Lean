import Dubon2026.SourceGammaOneGaussResidueKernel

/-! DUB-17/18 -> original Gamma1 Tate Frobenius/inertia -> original
good reduction -> literal coefficient reduction. Reuse the original
integral-fraction residue proof on the actual Gamma1 scalar-extended field.
The residue formula is independent of its integral fraction witness.
These maps and kernel/constant identities do not assert genus preservation
or good reduction; those remain subsequent mathematical obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open Polynomial IntermediateField GaussReduction

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "FF" => functionFieldOver Γ L
local notation "kk" => IsLocalRing.ResidueField A

theorem coe_algebraMap (c : L) :
    ((algebraMap L FF c : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c := rfl

theorem algebraMap_mem_gaussRing_iff (c : L) : algebraMap L FF c ∈ coefficientGaussRing Γ A ↔ c ∈ A := by
  constructor
  · rintro ⟨x, y, hy, h⟩
    rw [coe_algebraMap] at h
    by_contra hc
    have hc0 : c ≠ 0 := by rintro rfl; exact hc A.zero_mem
    have hci : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hc
    have hcm : (⟨c⁻¹, hci⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      apply hc
      have h1 : ((↑(u⁻¹ : Aˣ) : A) : L) * c⁻¹ = 1 := by
        have := congrArg (fun a : A => (a : L)) u.inv_val
        simpa [hu] using this
      rw [mul_inv_eq_one₀ hc0] at h1
      rw [← h1]; exact SetLike.coe_mem _
    have hyx : y = HahnSeries.C ⟨c⁻¹, hci⟩ * x := by
      apply ι_injective A
      rw [map_mul, ι_C, ← h, ← mul_assoc, ← map_mul]
      simp [inv_mul_cancel₀ hc0]
    apply hy
    rw [ϖ_eq_zero_iff]
    intro n
    rw [hyx, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hcm
  · intro hc
    refine ⟨HahnSeries.C ⟨c, hc⟩, 1, by simp, ?_⟩
    rw [coe_algebraMap, ι_C, map_one, mul_one]

theorem resHom_algebraMap (a : A) (h : algebraMap L FF a ∈ coefficientGaussRing Γ A) :
    resHom A Γ ⟨algebraMap L FF a, h⟩ = algebraMap kk (LaurentSeries kk) (IsLocalRing.residue A a) := by
  rw [resHom_eq A Γ (x := HahnSeries.C a) (y := 1) (by simp)
    (by rw [map_one, mul_one]; change algebraMap L (LaurentSeries L) (a : L) = _; rw [ι_C]),
    ϖ_C, map_one, div_one]

theorem coe_smul' (c : L) (f : FF) :
    ((c • f : FF) : LaurentSeries L) = algebraMap L (LaurentSeries L) c * (f : LaurentSeries L) := by
  rw [IntermediateField.coe_smul, Algebra.smul_def]

theorem exists_smul_mem_gaussRing (f : FF) (hf : f ≠ 0) :
    ∃ c : L, ∃ h : c • f ∈ coefficientGaussRing Γ A, resHom A Γ ⟨c • f, h⟩ ≠ 0 := by
  have hx : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := by
    rw [← functionFieldOver_eq_qExpFunctionFieldC Γ L]
    exact f.property
  have hx0 : (f : LaurentSeries L) ≠ 0 := fun h => hf (Subtype.ext h)
  obtain ⟨c, hc0, x₀, y₀, hx₀, hy₀, h⟩ :=
    qExpFunctionField_exists_primitive_fraction A Γ hx hx0
  have key : ((c⁻¹ • f : FF) : LaurentSeries L) * ι A y₀ = ι A x₀ := by
    rw [coe_smul', mul_assoc, h, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
  have hmem : c⁻¹ • f ∈ coefficientGaussRing Γ A := (mem_coefficientGaussRing_iff Γ A _).mpr ⟨x₀, y₀, hy₀, key⟩
  refine ⟨c⁻¹, hmem, ?_⟩
  rw [Ne, resHom_eq A Γ (f := ⟨_, hmem⟩) hy₀ key]
  exact div_ne_zero hx₀ hy₀

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
