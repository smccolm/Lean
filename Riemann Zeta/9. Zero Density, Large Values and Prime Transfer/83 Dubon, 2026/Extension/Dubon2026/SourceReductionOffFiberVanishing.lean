import Dubon2026.SourceReductionIntegralChartImage
import Dubon2026.SourceReductionChartGluing
import Dubon2026.SourceIntegralChartPoleBound
import Dubon2026.SourceConstantFieldOrderResidues

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> weight-two Frobenius
and inertia -> modular good reduction -> principal-divisor pushforward.
An original chart place outside the chosen reduction fiber admits an integral
function vanishing there whose reduction is a unit at the target place.
This supplies the multiplier for the required pole-cancellation argument.
The proved residue-integrality lemma removes the external chart-surjectivity
premise from this step. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_ord_residue_le_sum_ord_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem exists_off_fiber_vanishing [IsAlgClosed L]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (Q : Place (ResidueField A) Fbar) (hQ : R.residue x ∈ Q.toValuationSubring)
    (P : Place L F) (hxP : (x : F) ∈ P.toValuationSubring)
    (hPT : ¬ ((∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits) ∧
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits)) :
    ∃ y : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (y : F) ∧ (y : F) ≠ 0 ∧
      0 < P.ord (y : F) ∧ R.residue y ≠ 0 ∧ Q.ord (R.residue y) = 0 := by
  haveI : FiniteDimensional (IntermediateField.adjoin L ({(x : F)} : Set F)) F :=
    Module.finite_of_finrank_pos (hdeg ▸ hfin)
  obtain ⟨c, hc⟩ := P.exists_sub_algebraMap_mem_nonunits
    (place_residue_bijective_of_finite_coordinate (x : F) P).surjective hxP
  by_cases hcA : c ∈ A
  ·
    have h2 : ∃ a : A, (x : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits :=
      ⟨⟨c, hcA⟩, hc⟩
    have h3 : ∃ h₁ : R.integers, IsIntegral (Algebra.adjoin L {(x : F)}) (h₁ : F) ∧ ∃ a : A,
        (h₁ : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits ∧
          R.residue h₁ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∉
            Q.toValuationSubring.nonunits := by
      by_contra hne
      push Not at hne
      exact hPT ⟨h2, hne⟩
    obtain ⟨h₁, hh₁, a, ha, hres⟩ := h3
    have hcoe : ((h₁ - constHom R a : R.integers) : F) = (h₁ : F) - algebraMap L F a := by
      push_cast; rw [coe_constHom]
    have hres' : R.residue (h₁ - constHom R a) = R.residue h₁ -
        algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
      rw [map_sub, residue_constHom]
    have hyint : IsIntegral (Algebra.adjoin L {(x : F)}) ((h₁ - constHom R a : R.integers) : F) := by
      rw [hcoe]; exact hh₁.sub ((isIntegral_algebraMap (R := L) (A := F) (x := (a : L))).tower_top)
    have hyO : R.residue (h₁ - constHom R a) ∈ Q.toValuationSubring :=
      Q.mem_of_integral_adjoin hQ
        (isIntegral_residue_of_integral_chart R x hx hfin hdeg _ hyint)
    have hord0 : Q.ord (R.residue (h₁ - constHom R a)) = 0 := by
      refine ConstantField.ord_coe_isUnit Q (X := ⟨_, hyO⟩) ?_
      by_contra hnu
      apply hres
      rw [← hres']
      exact (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, hyO⟩)).mpr
        ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
    have hresne : R.residue (h₁ - constHom R a) ≠ 0 := by
      intro h0
      apply hres
      rw [← hres', h0]
      rw [ValuationSubring.mem_nonunits_iff, map_zero]
      exact zero_lt_one
    have hy0 : ((h₁ - constHom R a : R.integers) : F) ≠ 0 := by
      intro h0
      apply hresne
      rw [show h₁ - constHom R a = 0 from Subtype.ext h0, map_zero]
    refine ⟨h₁ - constHom R a, hyint, hy0, ?_, hresne, hord0⟩
    have hyP : ((h₁ - constHom R a : R.integers) : F) ∈ P.toValuationSubring.nonunits := by
      rwa [hcoe]
    apply (P.mem_maximalIdeal_iff_ord_pos hy0 (ValuationSubring.nonunits_subset hyP)).mp
    exact ValuationSubring.coe_mem_nonunits_iff.mp hyP
  ·
    have hc0 : c ≠ 0 := fun h => hcA (h ▸ zero_mem A)
    have hc' : algebraMap L F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
    have hcinv : c⁻¹ ∈ A := (A.mem_or_inv_mem c).resolve_left hcA
    have hres0 : IsLocalRing.residue A ⟨c⁻¹, hcinv⟩ = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      show A.valuation c⁻¹ < 1
      rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))]
      exact lt_of_not_ge fun h => hcA ((A.valuation_le_one_iff c).mp h)
    let y : R.integers := 1 - constHom R ⟨c⁻¹, hcinv⟩ * x
    have hxc : (x : F) - algebraMap L F c ≠ 0 := by
      intro h
      exact transcendental_of_residue_transcendental R x hx (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap c)
    have hyF : (y : F) = -(algebraMap L F c)⁻¹ * ((x : F) - algebraMap L F c) := by
      simp only [y]
      push_cast
      rw [coe_constHom]
      show 1 - algebraMap L F c⁻¹ * (x : F) = _
      rw [map_inv₀]
      field_simp
      ring
    have hy0 : (y : F) ≠ 0 := by
      rw [hyF]; exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hc')) hxc
    have hordy : 0 < P.ord (y : F) := by
      rw [hyF, P.ord_mul (neg_ne_zero.mpr (inv_ne_zero hc')) hxc, P.ord_neg, ← map_inv₀,
        P.ord_algebraMap, zero_add]
      exact (P.mem_maximalIdeal_iff_ord_pos hxc (ValuationSubring.nonunits_subset hc)).mp
        (ValuationSubring.coe_mem_nonunits_iff.mp hc)
    have hresy : R.residue y = 1 := by
      simp only [y, map_sub, map_one, map_mul, residue_constHom, hres0, map_zero, zero_mul, sub_zero]
    refine ⟨y, ?_, hy0, hordy, ?_, ?_⟩
    · have : IsIntegral (Algebra.adjoin L {(x : F)}) ((1 : F) - (constHom R ⟨c⁻¹, hcinv⟩ : F) * x) :=
        isIntegral_one.sub (((isIntegral_algebraMap (R := L) (A := F) (x := c⁻¹)).tower_top).mul (isIntegral_algebraMap (x := (⟨(x : F), Algebra.self_mem_adjoin_singleton L (x : F)⟩ : Algebra.adjoin L {(x : F)}))))
      exact this
    · rw [hresy]; exact one_ne_zero
    · rw [hresy]; exact Q.ord_one

end
end Dubon2026.SourceCurve.RegularProlongation
