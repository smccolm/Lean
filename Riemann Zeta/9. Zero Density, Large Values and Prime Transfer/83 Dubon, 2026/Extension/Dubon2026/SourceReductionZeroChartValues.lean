import Dubon2026.SourceReductionIntegralChartValues

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> place comparison.
Integral chart functions have integral values at an original place centered
over an integral coordinate value; zero Gauss residue forces that value into
the coefficient maximal ideal. These are the properness inputs for the
actual reduction-place construction, not a supplied place-map certificate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.
The existing local minimal-polynomial integrality theorem replaces the
external valuation-extension and monic-equation development. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem valuation_algebraMap_eq_one (P : Place L F) {c : L} (hc : c ≠ 0) :
    P.toValuationSubring.valuation (algebraMap L F c) = 1 := by
  let u : (P.toValuationSubring)ˣ :=
    ⟨algebraMap L P.toValuationSubring c, algebraMap L P.toValuationSubring c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩
  exact P.toValuationSubring.valuation_unit u

theorem mem_nonunits_of_residue_eq_zero (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits)
    {h : F} (hhO : h ∈ R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h)
    (hres : R.residue ⟨h, hhO⟩ = 0)
    {b : L} (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : b ∈ A.nonunits := by
  rcases eq_or_ne h 0 with rfl | hh0
  · have hb0 : b = 0 := by
      by_contra hb0
      have := (ValuationSubring.mem_nonunits_iff _).mp hb
      rw [zero_sub, Valuation.map_neg, valuation_algebraMap_eq_one P hb0] at this
      exact lt_irrefl _ this
    rw [hb0]
    exact zero_mem _
  · obtain ⟨c, hcO, hcres⟩ := R.exists_smul_mem h hh0
    have hc0 : c ≠ 0 := by
      intro hc
      subst c
      apply hcres
      have heq : (⟨(0 : L) • h, hcO⟩ : R.integers) = 0 := Subtype.ext (zero_smul L h)
      rw [heq, map_zero]
    have hcu : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (c • h) := by
      rw [Algebra.smul_def]
      have hcint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (algebraMap L F c) :=
        (isIntegral_algebraMap (R := L) (A := F) (x := c)).tower_top
      exact hcint.mul hh
    have hsub : c • h - algebraMap L F (c * b) ∈ P.toValuationSubring.nonunits := by
      rw [Algebra.smul_def, map_mul, ← mul_sub, ValuationSubring.mem_nonunits_iff, map_mul,
        valuation_algebraMap_eq_one P hc0, one_mul]
      exact (ValuationSubring.mem_nonunits_iff _).mp hb
    have hcbA : c * b ∈ A := mem_of_sub_mem_nonunits R x hx hfin hdeg P ha₀ hcO hcu hsub
    have hcinvA : c⁻¹ ∈ A := by
      refine (A.mem_or_inv_mem c).resolve_left fun hcA => hcres ?_
      have heq : (⟨c • h, hcO⟩ : R.integers) = constHom R ⟨c, hcA⟩ * ⟨h, hhO⟩ :=
        Subtype.ext (Algebra.smul_def c h)
      rw [heq, map_mul, hres, mul_zero]
    have key : R.residue (constHom R ⟨c⁻¹, hcinvA⟩) = 0 := by
      have heq : (⟨h, hhO⟩ : R.integers) = constHom R ⟨c⁻¹, hcinvA⟩ * ⟨c • h, hcO⟩ := by
        apply Subtype.ext
        show h = algebraMap L F c⁻¹ * (c • h)
        rw [Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      have := hres
      rw [heq, map_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hcres
    have hbA : b ∈ A := by
      have : b = c⁻¹ * (c * b) := by rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
      rw [this]
      exact mul_mem hcinvA hcbA
    refine ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr ⟨hbA, ?_⟩
    have hcm : (⟨c⁻¹, hcinvA⟩ : A) ∈ maximalIdeal A := by
      rw [← IsLocalRing.residue_eq_zero_iff]
      apply (algebraMap (ResidueField A) Fbar).injective
      rw [map_zero, ← residue_constHom R]
      exact key
    have heq : (⟨b, hbA⟩ : A) = ⟨c⁻¹, hcinvA⟩ * ⟨c * b, hcbA⟩ := by
      apply Subtype.ext
      show b = c⁻¹ * (c * b)
      rw [← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
    rw [heq]
    exact Ideal.mul_mem_right _ _ hcm


end
end Dubon2026.SourceCurve.RegularProlongation
