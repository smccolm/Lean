import Dubon2026.SourceEllipticResidueInverseSlope

/-! Integral addition slopes commute with reduction away from inverse pairs.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, ReduceHom, lines 65-270.
This is the remaining finite-coordinate calculation for the prime-to-residue
torsion reduction map and integral odd quotient compatibility. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

section Coercion

variable {W}

/-- Residue compatibility for the actual integral addition slope: coe_negY. -/
lemma coe_negY {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
  (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm

/-- Residue compatibility for the actual integral addition slope: negY_mem. -/
lemma negY_mem {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    (W.map A.subtype).toAffine.negY x y ∈ A := by
  rw [← coe_negY hx hy]
  exact SetLike.coe_mem _

/-- Residue compatibility for the actual integral addition slope: residue_negY. -/
lemma residue_negY {x y : L} (hx : x ∈ A) (hy : y ∈ A) :
    residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) =
      (W.map (residue A)).toAffine.negY (residue A ⟨x, hx⟩) (residue A ⟨y, hy⟩) :=
  (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm

/-- Residue compatibility for the actual integral addition slope: residue_sub_negY. -/
lemma residue_sub_negY {x₂ y₁ y₂ : L} (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A) (hy₂ : y₂ ∈ A)
    (hmem : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A) :
    residue A ⟨y₁ - (W.map A.subtype).toAffine.negY x₂ y₂, hmem⟩ =
      residue A ⟨y₁, hy₁⟩ -
        (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
  rw [residue_eq_of_coe_eq A hmem (v := ⟨y₁, hy₁⟩ - W.toAffine.negY ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩)
    (by push_cast; rw [coe_negY hx₂ hy₂]), map_sub, residue_negY hx₂ hy₂]

/-- Residue compatibility for the actual integral addition slope: residue_inverse_iff. -/
lemma residue_inverse_iff {x₁ y₁ x₂ y₂ : L} (hx₁ : x₁ ∈ A) (hy₁ : y₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hy₂ : y₂ ∈ A) :
    (residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) ↔
      (x₁ - x₂ ∈ A.nonunits ∧
        y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) := by
  have hnegA : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := negY_mem hx₂ hy₂
  have h1 := residue_eq_residue_iff_sub_mem_nonunits A hx₁ hx₂
  have h2 := residue_eq_residue_iff_sub_mem_nonunits A hy₁ hnegA
  have h3 : residue A ⟨(W.map A.subtype).toAffine.negY x₂ y₂, hnegA⟩ =
      (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
    rw [residue_eq_of_coe_eq A hnegA (v := W.toAffine.negY ⟨x₂, hx₂⟩ ⟨y₂, hy₂⟩)
      (coe_negY hx₂ hy₂).symm]
    exact residue_negY hx₂ hy₂
  rw [← h3]
  exact and_congr h1 h2

end Coercion

section Slope

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W}

/-- Residue compatibility for the actual integral addition slope: slope_mem_residue_of_not_inverse. -/
theorem slope_mem_residue_of_not_inverse
    {x₁ y₁ x₂ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hred : ¬(x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits)) :
    ∃ hs : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A,
      residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hs⟩ =
        (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
          (residue A ⟨y₁, SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₁ hx₁⟩)
          (residue A ⟨y₂, SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₂ hx₂⟩) := by
  have hy₁ : y₁ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₁ hx₁
  have hy₂ : y₂ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₂ hx₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄

  have hk₁ : (W.map (residue A)).toAffine.Equation (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩) :=
    equation_residue W (x := ⟨x₁, hx₁⟩) (y := ⟨y₁, hy₁⟩) h₁
  have hk₂ : (W.map (residue A)).toAffine.Equation (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) :=
    equation_residue W (x := ⟨x₂, hx₂⟩) (y := ⟨y₂, hy₂⟩) h₂

  have ha₁k : (W.map (residue A)).toAffine.a₁ = residue A W.a₁ := rfl
  have ha₂k : (W.map (residue A)).toAffine.a₂ = residue A W.a₂ := rfl
  have ha₄k : (W.map (residue A)).toAffine.a₄ = residue A W.a₄ := rfl
  by_cases hxx : x₁ - x₂ ∈ A.nonunits
  ·

    have hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∉ A.nonunits := fun h => hred ⟨hxx, h⟩
    have hyyA : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A :=
      A.toSubring.sub_mem hy₁ (negY_mem hx₂ hy₂)
    have hyy0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 :=
      ne_zero_of_notMem_nonunits A hyy

    have hxk : residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ :=
      (residue_eq_residue_iff_sub_mem_nonunits A hx₁ hx₂).mpr hxx
    have hyk : residue A ⟨y₁, hy₁⟩ ≠
        (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩) := by
      intro h
      exact hyy (((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp ⟨hxk, h⟩).2)

    have hyk' : residue A ⟨y₁, hy₁⟩ = residue A ⟨y₂, hy₂⟩ :=
      Affine.Y_eq_of_Y_ne hk₁ hk₂ hxk hyk
    have hslope_k : (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩)
        (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) =
        (3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
            residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
            (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩) /
          (residue A ⟨y₁, hy₁⟩ -
            (W.map (residue A)).toAffine.negY (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩)) :=
      Affine.slope_of_Y_ne hxk hyk

    have hden_res : residue A ⟨y₁ - (W.map A.subtype).toAffine.negY x₂ y₂, hyyA⟩ =
        residue A ⟨y₁, hy₁⟩ -
          (W.map (residue A)).toAffine.negY (residue A ⟨x₁, hx₁⟩) (residue A ⟨y₁, hy₁⟩) := by
      rw [residue_sub_negY hy₁ hx₂ hy₂ hyyA, hxk, hyk']

    have hnum_mem : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ ∈ A := by
      refine A.toSubring.sub_mem (A.toSubring.add_mem (A.toSubring.add_mem ?_ ?_) ha₄)
        (A.toSubring.mul_mem ha₁ hy₁)
      · exact A.toSubring.mul_mem (by norm_num : (3 : L) ∈ A) (pow_mem hx₁ 2)
      · exact A.toSubring.mul_mem (A.toSubring.mul_mem (by norm_num : (2 : L) ∈ A) ha₂) hx₁
    have hnum_res : residue A ⟨3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁, hnum_mem⟩ =
        3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
          residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
          (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩ := by
      rw [residue_eq_of_coe_eq A hnum_mem
        (v := 3 * ⟨x₁, hx₁⟩ ^ 2 + 2 * W.a₂ * ⟨x₁, hx₁⟩ + W.a₄ - W.a₁ * ⟨y₁, hy₁⟩)
        (by push_cast; rfl)]
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat]
      rw [ha₁k, ha₂k, ha₄k]
    by_cases hx : x₁ = x₂
    ·
      have hyL : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hyy0 (by rw [h, sub_self])
      have hyL' : y₁ = y₂ := Affine.Y_eq_of_Y_ne h₁ h₂ hx hyL
      have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₁ y₁) :=
        Affine.slope_of_Y_ne hx hyL
      have hden_eq : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
          y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ := by
        rw [hx, hyL']
      have hslope_L' : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [hslope_L, hden_eq]
      have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
        rw [hslope_L']
        exact div_mem_of_mem_of_notMem_nonunits A hnum_mem hyy
      refine ⟨hsmem, ?_⟩
      rw [residue_eq_div_of_eq_div A hsmem hnum_mem hyyA hyy hslope_L', hslope_k, hnum_res,
        hden_res]
    ·

      have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
        Affine.slope_of_X_ne hx
      have hN_mem : x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
          (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ ∈ A := by
        refine A.toSubring.sub_mem (A.toSubring.add_mem (A.toSubring.add_mem (A.toSubring.add_mem
          (A.toSubring.add_mem (pow_mem hx₁ 2) (A.toSubring.mul_mem hx₁ hx₂)) (pow_mem hx₂ 2))
          (A.toSubring.mul_mem ha₂ (A.toSubring.add_mem hx₁ hx₂))) ha₄)
          (A.toSubring.mul_mem ha₁ hy₁)

      have hslope_N : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ =
          (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
              (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁) /
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [hslope_L, div_eq_div_iff (sub_ne_zero.mpr hx) hyy0]
        linear_combination sub_mul_sub_negY h₁ h₂
      have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
        rw [hslope_N]
        exact div_mem_of_mem_of_notMem_nonunits A hN_mem hyy
      refine ⟨hsmem, ?_⟩

      have hN_res : residue A ⟨x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 +
          (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) + (W.map A.subtype).toAffine.a₄ -
          (W.map A.subtype).toAffine.a₁ * y₁, hN_mem⟩ =
          3 * residue A ⟨x₁, hx₁⟩ ^ 2 + 2 * (W.map (residue A)).toAffine.a₂ *
            residue A ⟨x₁, hx₁⟩ + (W.map (residue A)).toAffine.a₄ -
            (W.map (residue A)).toAffine.a₁ * residue A ⟨y₁, hy₁⟩ := by
        rw [residue_eq_of_coe_eq A hN_mem
          (v := ⟨x₁, hx₁⟩ ^ 2 + ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ + ⟨x₂, hx₂⟩ ^ 2 +
            W.a₂ * (⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩) + W.a₄ - W.a₁ * ⟨y₁, hy₁⟩)
          (by push_cast; rfl)]
        simp only [map_sub, map_add, map_mul, map_pow]
        rw [ha₁k, ha₂k, ha₄k, ← hxk]
        ring
      rw [residue_eq_div_of_eq_div A hsmem hN_mem hyyA hyy hslope_N, hslope_k, hN_res, hden_res]
  ·
    have hxL : x₁ ≠ x₂ := fun h => hxx (by rw [h, sub_self]; exact A.nonunits.zero_mem)
    have hxxA : x₁ - x₂ ∈ A := A.toSubring.sub_mem hx₁ hx₂
    have hslope_L : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) :=
      Affine.slope_of_X_ne hxL
    have hyyA : y₁ - y₂ ∈ A := A.toSubring.sub_mem hy₁ hy₂
    have hsmem : (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∈ A := by
      rw [hslope_L]
      exact div_mem_of_mem_of_notMem_nonunits A hyyA hxx
    refine ⟨hsmem, ?_⟩

    have hxk : residue A ⟨x₁, hx₁⟩ ≠ residue A ⟨x₂, hx₂⟩ := fun h =>
      hxx ((residue_eq_residue_iff_sub_mem_nonunits A hx₁ hx₂).mp h)
    have hslope_k : (W.map (residue A)).toAffine.slope (residue A ⟨x₁, hx₁⟩)
        (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₁, hy₁⟩) (residue A ⟨y₂, hy₂⟩) =
        (residue A ⟨y₁, hy₁⟩ - residue A ⟨y₂, hy₂⟩) /
          (residue A ⟨x₁, hx₁⟩ - residue A ⟨x₂, hx₂⟩) := Affine.slope_of_X_ne hxk
    have hnum_eq : residue A ⟨y₁ - y₂, hyyA⟩ = residue A ⟨y₁, hy₁⟩ - residue A ⟨y₂, hy₂⟩ := by
      rw [residue_eq_of_coe_eq A hyyA (v := ⟨y₁, hy₁⟩ - ⟨y₂, hy₂⟩) (by push_cast; ring), map_sub]
    have hden_eq : residue A ⟨x₁ - x₂, hxxA⟩ = residue A ⟨x₁, hx₁⟩ - residue A ⟨x₂, hx₂⟩ := by
      rw [residue_eq_of_coe_eq A hxxA (v := ⟨x₁, hx₁⟩ - ⟨x₂, hx₂⟩) (by push_cast; ring), map_sub]
    rw [residue_eq_div_of_eq_div A hsmem hyyA hxxA hxx hslope_L, hslope_k, hnum_eq, hden_eq]

end Slope

end Dubon2026.SourceEllipticReduction
