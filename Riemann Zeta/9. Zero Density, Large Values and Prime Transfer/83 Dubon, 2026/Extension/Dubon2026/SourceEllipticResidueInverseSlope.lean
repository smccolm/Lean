import Dubon2026.SourceEllipticResiduePoint

/-! When two integral points reduce to inverses, their finite sum has a pole.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, TorsionIntegral, lines 36-203.
Only this slope argument is retained; no formal-parameter estimates are used.
It proves additivity of reduction on the required torsion subgroup. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

/-- Integral-point slope control used by the reduction homomorphism: sub_mul_sub_negY. -/
theorem sub_mul_sub_negY {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (h₁ : V.Equation x₁ y₁) (h₂ : V.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ - V.negY x₂ y₂) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₁) := by
  rw [Affine.equation_iff] at h₁ h₂
  rw [Affine.negY]
  linear_combination h₁ - h₂

/-- Integral-point slope control used by the reduction homomorphism: notMem_nonunits_of_sub_negY_mem_nonunits. -/
theorem notMem_nonunits_of_sub_negY_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x y : L} (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A)
    (hY : y - (W.map A.subtype).toAffine.negY x y ∈ A.nonunits) :
    3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x + (W.map A.subtype).toAffine.a₄ -
      (W.map A.subtype).toAffine.a₁ * y ∉ A.nonunits := by
  have hy : y ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h hx

  set eX : A := 3 * ⟨x, hx⟩ ^ 2 + 2 * W.a₂ * ⟨x, hx⟩ + W.a₄ - W.a₁ * ⟨y, hy⟩ with heX
  set eY : A := ⟨y, hy⟩ - W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ with heY

  have hcoeX : (eX : L) = 3 * x ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x +
      (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y := by
    push_cast [heX]
    rfl
  have hcoeY : (eY : L) = y - (W.map A.subtype).toAffine.negY x y := by
    have h1 : ((W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩ : A) : L) = (W.map A.subtype).toAffine.negY x y :=
      (Affine.map_negY A.subtype (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    rw [heY]
    push_cast
    rw [h1]

  have hns := nonsingular_residue W hΔ (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) h
  rw [Affine.nonsingular_iff] at hns

  have hY0 : residue A eY = 0 := by
    rw [← coe_mem_nonunits_iff_residue_eq_zero A, hcoeY]
    exact hY

  have hX0 : residue A eX ≠ 0 := by
    rcases hns.2 with hX | hY'
    · intro h0
      apply hX
      rw [heX] at h0
      simp only [map_sub, map_add, map_mul, map_pow, map_ofNat] at h0
      show residue A W.a₁ * residue A ⟨y, hy⟩ = 3 * residue A ⟨x, hx⟩ ^ 2 +
        2 * residue A W.a₂ * residue A ⟨x, hx⟩ + residue A W.a₄
      linear_combination -h0
    · exact absurd (by
        show residue A ⟨y, hy⟩ = -residue A ⟨y, hy⟩ - residue A W.a₁ * residue A ⟨x, hx⟩ -
          residue A W.a₃
        rw [heY] at hY0
        simp only [Affine.negY, map_sub, map_neg, map_mul] at hY0
        linear_combination hY0) hY'

  rw [← hcoeX, coe_mem_nonunits_iff_residue_eq_zero A]
  exact hX0

section Slope

variable [DecidableEq L]

/-- Integral-point slope control used by the reduction homomorphism: slope_notMem_of_sub_mem_nonunits. -/
theorem slope_notMem_of_sub_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂ ∉ A := by
  have hy₁ : y₁ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₁ hx₁
  have hy₂ : y₂ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₂ hx₂

  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄

  have hnegY : (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A := by
    rw [Affine.negY]
    exact A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem hy₂)
      (A.toSubring.mul_mem ha₁ hx₂)) ha₃
  by_cases hx : x₁ = x₂
  ·

    have hy : y₁ ≠ (W.map A.subtype).toAffine.negY x₂ y₂ := fun h => hPQ ⟨hx, h⟩
    have hy12 : y₁ = y₂ := (Affine.Y_eq_of_X_eq h₁ h₂ hx).resolve_right hy
    rw [Affine.slope_of_Y_ne hx hy]

    have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
      rwa [← hx, ← hy12] at hyy
    have hden0 : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hy (by rw [← hx, ← hy12]; exact hcon)

    have hnum := notMem_nonunits_of_sub_negY_mem_nonunits W hΔ h₁ hx₁ hden
    exact div_notMem A hnum hden hden0
  ·
    by_cases hyy' : y₁ - y₂ ∈ A.nonunits
    ·

      rw [Affine.slope_of_X_ne hx]

      have hden : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ ∈ A.nonunits := by
        have key : y₁ - (W.map A.subtype).toAffine.negY x₁ y₁ =
            (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) + (y₁ - y₂) +
              (W.map A.subtype).toAffine.a₁ * (x₁ - x₂) := by
          simp only [Affine.negY]
          ring
        rw [key]
        exact add_mem (add_mem hyy hyy') (mul_mem_nonunits A ha₁ hxx)

      have hnum := notMem_nonunits_of_sub_negY_mem_nonunits W hΔ h₁ hx₁ hden

      set N : L := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + (W.map A.subtype).toAffine.a₂ * (x₁ + x₂) +
        (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ with hN
      have hNunit : N ∉ A.nonunits := by
        intro hmem
        apply hnum
        have key : 3 * x₁ ^ 2 + 2 * (W.map A.subtype).toAffine.a₂ * x₁ +
            (W.map A.subtype).toAffine.a₄ - (W.map A.subtype).toAffine.a₁ * y₁ =
            N - (x₁ + x₁ + x₂ + (W.map A.subtype).toAffine.a₂) * -(x₁ - x₂) := by
          rw [hN]; ring
        rw [key]
        exact sub_mem hmem (mul_mem_nonunits A
          (add_mem (add_mem (add_mem hx₁ hx₁) hx₂) ha₂) (neg_mem hxx))

      have hd0 : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ≠ 0 := by
        intro hd
        apply hNunit
        rw [hN]
        have hid := sub_mul_sub_negY h₁ h₂
        rw [hd, mul_zero] at hid
        rcases mul_eq_zero.mp hid.symm with h | h
        · exact absurd (sub_eq_zero.mp h) hx
        · rw [h]
          exact zero_mem _

      have hslope : (y₁ - y₂) / (x₁ - x₂) = N / (y₁ - (W.map A.subtype).toAffine.negY x₂ y₂) := by
        rw [div_eq_div_iff (sub_ne_zero.mpr hx) hd0, hN]
        linear_combination sub_mul_sub_negY h₁ h₂
      rw [hslope]
      exact div_notMem A hNunit hyy hd0
    ·

      rw [Affine.slope_of_X_ne hx]
      exact div_notMem A hyy' hxx (sub_ne_zero.mpr hx)

/-- Integral-point slope control used by the reduction homomorphism: addX_notMem_of_sub_mem_nonunits. -/
theorem addX_notMem_of_sub_mem_nonunits (hΔ : (W.map (residue A)).Δ ≠ 0)
    {x₁ x₂ y₁ y₂ : L} (h₁ : (W.map A.subtype).toAffine.Equation x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Equation x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A)
    (hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂))
    (hxx : x₁ - x₂ ∈ A.nonunits)
    (hyy : y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits) :
    (W.map A.subtype).toAffine.addX x₁ x₂ ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∉ A := by
  have hℓ := slope_notMem_of_sub_mem_nonunits W hΔ h₁ h₂ hx₁ hx₂ hPQ hxx hyy
  set ℓ : L := (W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂

  rw [show (W.map A.subtype).toAffine.addX x₁ x₂ ℓ =
    ℓ * (ℓ + (W.map A.subtype).toAffine.a₁) +
      (-(W.map A.subtype).toAffine.a₂ - x₁ - x₂) from by rw [Affine.addX]; ring]
  exact add_notMem A (mul_notMem A hℓ (by simpa [add_comm] using add_notMem A hℓ ha₁))
    (A.toSubring.sub_mem (A.toSubring.sub_mem (A.toSubring.neg_mem ha₂) hx₁) hx₂)

end Slope

end Dubon2026.SourceEllipticReduction
