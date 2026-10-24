import Dubon2026.SourceEllipticResidueAdditionSlope

/-! Addition of actual integral points commutes with reduction. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, ReduceHom, integral-point case.
The residue inverse and noninverse cases use the proved slope lemmas.
This suffices for the required prime-to-residue torsion subgroup. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
variable {L : Type*} [Field L] {A : ValuationSubring L} (W : WeierstrassCurve A)

private lemma some_congr' {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

section IntegralCase

variable [DecidableEq L] [DecidableEq (ResidueField A)]
variable {W} (hΔ : (W.map (residue A)).Δ ≠ 0)


/-- Reduction commutes with addition of two actual integral points. -/
theorem reducePoint_add_of_mem {x₁ y₁ x₂ y₂ : L}
    (h₁ : (W.map A.subtype).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.map A.subtype).toAffine.Nonsingular x₂ y₂) (hx₁ : x₁ ∈ A) (hx₂ : x₂ ∈ A) :
    reducePoint hΔ (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      reducePoint hΔ (.some x₁ y₁ h₁) + reducePoint hΔ (.some x₂ y₂ h₂) := by
  have hy₁ : y₁ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₁.1 hx₁
  have hy₂ : y₂ ∈ A := SourceEllipticFunctionField.equation_y_mem_valuationSubring A W h₂.1 hx₂

  rw [reducePoint_some_of_mem _ _ hx₁, reducePoint_some_of_mem _ _ hx₂]
  by_cases hred : x₁ - x₂ ∈ A.nonunits ∧
      y₁ - (W.map A.subtype).toAffine.negY x₂ y₂ ∈ A.nonunits
  ·
    obtain ⟨hredx, hredy⟩ := (residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mpr hred
    rw [Affine.Point.add_of_Y_eq hredx hredy]
    by_cases hPQ : x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂
    ·
      rw [Affine.Point.add_of_Y_eq hPQ.1 hPQ.2, reducePoint_zero]
    ·

      rw [Affine.Point.add_some hPQ]
      exact reducePoint_some_of_notMem _ _
        (addX_notMem_of_sub_mem_nonunits W hΔ h₁.1 h₂.1 hx₁ hx₂ hPQ hred.1 hred.2)
  ·

    obtain ⟨hsmem, hsres⟩ := slope_mem_residue_of_not_inverse h₁.1 h₂.1 hx₁ hx₂ hred

    have hPQ : ¬(x₁ = x₂ ∧ y₁ = (W.map A.subtype).toAffine.negY x₂ y₂) := by
      rintro ⟨hxe, hye⟩
      exact hred ⟨by rw [hxe, sub_self]; exact A.nonunits.zero_mem,
        by rw [hye, sub_self]; exact A.nonunits.zero_mem⟩

    have hredk : ¬(residue A ⟨x₁, hx₁⟩ = residue A ⟨x₂, hx₂⟩ ∧
        residue A ⟨y₁, hy₁⟩ =
          (W.map (residue A)).toAffine.negY (residue A ⟨x₂, hx₂⟩) (residue A ⟨y₂, hy₂⟩)) :=
      fun h => hred ((residue_inverse_iff hx₁ hy₁ hx₂ hy₂).mp h)
    rw [Affine.Point.add_some hPQ, Affine.Point.add_some hredk]

    have hX_coe : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
        ((W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
      Affine.map_addX (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
    have hY_coe : (W.map A.subtype).toAffine.addY x₁ x₂ y₁
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) =
        ((W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
          ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩ : A) : L) :=
      Affine.map_addY (W' := W) A.subtype (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A) (⟨x₂, hx₂⟩ : A)
        ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩
    have hX_mem : (W.map A.subtype).toAffine.addX x₁ x₂
        ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂) ∈ A := by
      rw [hX_coe]; exact SetLike.coe_mem _
    rw [reducePoint_some_of_mem _ _ hX_mem]
    refine some_congr' ?_ ?_ _ _
    ·
      calc residue A ⟨(W.map A.subtype).toAffine.addX x₁ x₂
              ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂), hX_mem⟩
          = residue A (W.toAffine.addX ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            residue_eq_of_coe_eq A hX_mem hX_coe
        _ = (W.map (residue A)).toAffine.addX (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
              (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            (Affine.map_addX (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨x₂, hx₂⟩ : A)
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
        _ = _ := by rw [hsres]
    ·
      calc residue A ⟨(W.map A.subtype).toAffine.addY x₁ x₂ y₁
              ((W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂),
              SourceEllipticFunctionField.equation_y_mem_valuationSubring A W (Affine.nonsingular_add h₁ h₂ hPQ).1 hX_mem⟩
          = residue A (W.toAffine.addY ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ ⟨y₁, hy₁⟩
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            residue_eq_of_coe_eq A _ hY_coe
        _ = (W.map (residue A)).toAffine.addY (residue A ⟨x₁, hx₁⟩) (residue A ⟨x₂, hx₂⟩)
              (residue A ⟨y₁, hy₁⟩)
              (residue A ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩) :=
            (Affine.map_addY (W' := W) (residue A) (⟨x₁, hx₁⟩ : A) (⟨y₁, hy₁⟩ : A)
              (⟨x₂, hx₂⟩ : A)
              ⟨(W.map A.subtype).toAffine.slope x₁ x₂ y₁ y₂, hsmem⟩).symm
        _ = _ := by rw [hsres]

end IntegralCase

end Dubon2026.SourceEllipticReduction
