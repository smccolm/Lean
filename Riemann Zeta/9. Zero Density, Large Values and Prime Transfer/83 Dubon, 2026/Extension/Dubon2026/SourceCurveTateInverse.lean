import Dubon2026.SourceCurveTateVanishing
import Dubon2026.SourceCurveParameterTateTrace

/-! The exact inverse-parameter and unit cases for rational power
residues. Together with the proved order-one normalization, these cover
every place of a rational generator without a characteristic restriction.
They feed the DUB-17/18 rational global residue sum. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The differential inverse rule for the actual Tate pairing. -/
theorem tateResidue_inv
    (hres : Function.Surjective (algebraMap K v.ResidueField)) {x : F} (hx : x ≠ 0) (f : F) :
    v.tateResidue f x⁻¹ = -v.tateResidue (f * x ^ (-2 : ℤ)) x := by
  have h := v.tateResidue_leibniz hres (f * x⁻¹) x x⁻¹
  rw [mul_inv_cancel₀ hx, v.tateResidue_one hres] at h
  have hfirst : (f * x⁻¹) * x = f := by rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]
  have hsecond : (f * x⁻¹) * x⁻¹ = f * x ^ (-2 : ℤ) := by
    rw [mul_assoc, ← zpow_neg_one, ← zpow_add₀ hx]
    rfl
  rw [hfirst, hsecond] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Powers of a local unit have zero residue against that unit. -/
theorem tateResidue_unit_zpow
    (hres : Function.Surjective (algebraMap K v.ResidueField)) {x : F}
    (hx : v.ord x = 0) (n : ℤ) : v.tateResidue (x ^ n) x = 0 := by
  apply v.tateResidue_of_mem hres
  · apply v.mem_of_ord_nonneg
    rw [v.ord_zpow, hx, mul_zero]
  · exact v.mem_of_ord_nonneg hx.ge

/-- A simple pole gives the negative of the order-one parameter normalization. -/
theorem tateResidue_pole_parameter_zpow
    (hres : Function.Surjective (algebraMap K v.ResidueField)) {x : F}
    (hx : v.ord x = -1) (n : ℤ) :
    v.tateResidue (x ^ n) x = if n = -1 then -1 else 0 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, v.ord_zero] at hx
    norm_num at hx
  have hxi : v.ord x⁻¹ = 1 := by rw [v.ord_inv, hx]; norm_num
  have h := v.tateResidue_inv hres (inv_ne_zero hx0) (x ^ n)
  rw [inv_inv] at h
  have hp : x ^ n * (x⁻¹) ^ (-2 : ℤ) = (x⁻¹) ^ (-n - 2) := by
    simp only [inv_zpow, ← zpow_neg]
    rw [← zpow_add₀ hx0]
    congr 1
    omega
  rw [hp, v.tateResidue_parameter_zpow hxi hres] at h
  rw [h]
  by_cases hn : n = -1
  · subst n
    norm_num
  · rw [if_neg (by omega), if_neg hn, neg_zero]

end Dubon2026.SourceCurve.Place
