import Dubon2026.SourceEllipticVeluTwoTangentYCompatibility

/-! Remaining coordinate and case analysis for the actual degree-two Velu
group homomorphism. The dependency is DUB-17 / DUB-18 -> continuation -> good
reduction -> reverse genus -> elliptic inertia census -> cyclic-quotient root
interpretation -> quotient homomorphisms with their actual cyclic kernels.
Compatibility predicates in intermediate lemmas describe explicit secant and
tangent coordinate obligations; the final consumer must derive them all.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2. All source option
changes and irrelevant logical anchors are omitted. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial
noncomputable section
section Held

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

variable (W x₀ y₀) in

/-- Explicit coordinate compatibility condition, discharged by the final additivity proof. -/
abbrev KwVeluOrderTwoAddCompatAt (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) : Prop :=
  ∀ P Q : W.toAffine.Point,
    veluPointMap2 hQ hgy hΔ (P + Q) = veluPointMap2 hQ hgy hΔ P + veluPointMap2 hQ hgy hΔ Q

end Held


section Field

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} {x₀ y₀ : F}

omit [DecidableEq F] in

theorem velu2_kernel_nonsingular (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : veluGy W x₀ y₀ = 0) (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0) :
    W.toAffine.Nonsingular x₀ y₀ := by
  have ht : veluGx W x₀ y₀ ≠ 0 := veluGx_ne_zero_of_quotΔ hQ hgy hΔ
  simp only [veluGx] at ht
  refine (WeierstrassCurve.Affine.nonsingular_iff ..).mpr ⟨hQ, Or.inl fun hcon => ht ?_⟩
  linear_combination -hcon

variable (hQ : W.toAffine.Equation x₀ y₀) (hgy : veluGy W x₀ y₀ = 0)
  (hΔ : (veluQuotient2 W x₀ y₀).Δ ≠ 0)

include hQ hgy hΔ in

theorem veluPointMap2_add_of_right_ker {K : W.toAffine.Point}
    (hK : veluPointMap2 hQ hgy hΔ K = 0) (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ (P + K) = veluPointMap2 hQ hgy hΔ P := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases K with
  | zero => rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hx : x = x₀
    ·
      rw [some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hx]
      exact veluPointMap2_add_kernel_gen hQ hgy hΔ hQns P
    ·
      rw [veluPointMap2_some_of_ne hQ hgy hΔ h hx] at hK
      exact absurd hK (WeierstrassCurve.Affine.Point.some_ne_zero _)

include hQ hgy hΔ in

theorem veluPointMap2_add_self (htan : KwVeluOrderTwoTangentCompatAt W x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ (P + P)
      = veluPointMap2 hQ hgy hΔ P + veluPointMap2 hQ hgy hΔ P := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases P with
  | zero =>
    rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero,
      ← WeierstrassCurve.Affine.Point.zero_def, add_zero]
  | some x y h =>
    by_cases hy : y = W.toAffine.negY x y
    ·
      have hPnP : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = -WeierstrassCurve.Affine.Point.some x y h := by
        rw [WeierstrassCurve.Affine.Point.neg_some]; simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro (Eq.refl x) hy
      have h2P0 : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + .some x y h = 0 := by
        nth_rw 1 [hPnP]; exact neg_add_cancel _
      have h2φP : veluPointMap2 hQ hgy hΔ (.some x y h)
          + veluPointMap2 hQ hgy hΔ (.some x y h) = 0 := by
        nth_rw 1 [hPnP, veluPointMap2_neg hQ hgy hΔ]; exact neg_add_cancel _
      rw [h2P0, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero]
      exact h2φP.symm
    ·
      have hx : x ≠ x₀ := by
        intro hcon
        have hPP₀ : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
            = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns :=
          some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns h hcon
        rw [WeierstrassCurve.Affine.Point.some.injEq] at hPP₀
        exact hy (hcon ▸ hPP₀.2 ▸ (negY_eq_of_veluGy_eq_zero hgy).symm)
      by_cases hx2 : W.toAffine.addX x x (W.toAffine.slope x x y y) = x₀
      ·
        have hnsA : W.toAffine.Nonsingular
            (W.toAffine.addX x x (W.toAffine.slope x x y y))
            (W.toAffine.addY x x y (W.toAffine.slope x x y y)) :=
          WeierstrassCurve.Affine.nonsingular_add h h fun hxy => hy hxy.2
        have h2P : (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x y h
            = WeierstrassCurve.Affine.Point.some x₀ y₀ hQns := by
          rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy]
          exact some_eq_of_X_eq_of_veluGy_eq_zero hQ hgy hQns hnsA hx2

        have hφ2P : veluPointMap2 hQ hgy hΔ
            ((WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) + WeierstrassCurve.Affine.Point.some x y h) = 0 := by
          rw [h2P]; exact veluPointMap2_some_of_eq hQ hgy hΔ hQns rfl

        have hnegP₀ : -(WeierstrassCurve.Affine.Point.some x₀ y₀ hQns : W.toAffine.Point) = .some x₀ y₀ hQns := by
          rw [WeierstrassCurve.Affine.Point.neg_some]
          simpa only [WeierstrassCurve.Affine.Point.some.injEq] using And.intro (Eq.refl x₀) (negY_eq_of_veluGy_eq_zero hgy)
        have hnegP : -(WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point)
            = WeierstrassCurve.Affine.Point.some x y h + WeierstrassCurve.Affine.Point.some x₀ y₀ hQns := by
          rw [← hnegP₀, ← sub_eq_add_neg, ← h2P]; abel
        have h2φP : veluPointMap2 hQ hgy hΔ (.some x y h)
            + veluPointMap2 hQ hgy hΔ (.some x y h) = 0 :=
          add_eq_zero_iff_eq_neg.mpr <| by
            rw [← veluPointMap2_neg hQ hgy hΔ, hnegP,
              veluPointMap2_add_kernel_gen hQ hgy hΔ hQns]
        rw [hφ2P, h2φP]
      ·
        exact veluPointMap2_add_self_of_tangent hQ hgy hΔ htan h hy hx hx2

include hQ hgy hΔ in

theorem veluPointMap2_add' (hsec : KwVeluOrderTwoSecantCompatDiffAvoidAt W x₀ y₀)
    (htan : KwVeluOrderTwoTangentCompatAt W x₀ y₀) (P₁ P₂ : W.toAffine.Point) :
    veluPointMap2 hQ hgy hΔ (P₁ + P₂)
      = veluPointMap2 hQ hgy hΔ P₁ + veluPointMap2 hQ hgy hΔ P₂ := by
  have hQns : W.toAffine.Nonsingular x₀ y₀ := velu2_kernel_nonsingular hQ hgy hΔ
  cases P₁ with
  | zero =>
    rw [← WeierstrassCurve.Affine.Point.zero_def, zero_add, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero,
      ← WeierstrassCurve.Affine.Point.zero_def, zero_add]
  | some x₁ y₁ h₁ =>
    cases P₂ with
    | zero =>
      rw [← WeierstrassCurve.Affine.Point.zero_def, add_zero, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero,
        ← WeierstrassCurve.Affine.Point.zero_def, add_zero]
    | some x₂ y₂ h₂ =>

      by_cases hx₂k : x₂ = x₀
      · have hK : veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂) = 0 :=
          veluPointMap2_some_of_eq hQ hgy hΔ h₂ hx₂k
        rw [veluPointMap2_add_of_right_ker hQ hgy hΔ hK, hK, add_zero]
      by_cases hx₁k : x₁ = x₀
      · have hK : veluPointMap2 hQ hgy hΔ (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁) = 0 :=
          veluPointMap2_some_of_eq hQ hgy hΔ h₁ hx₁k
        rw [add_comm, veluPointMap2_add_of_right_ker hQ hgy hΔ hK, hK, zero_add]

      by_cases hx12 : x₁ = x₂
      · rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := h₂) (h₂ := h₁)).mp hx12.symm with hPeq | hPeq
        · rw [hPeq]; exact veluPointMap2_add_self hQ hgy hΔ htan _
        · rw [hPeq, add_neg_cancel, WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_zero,
            ← WeierstrassCurve.Affine.Point.zero_def, veluPointMap2_neg hQ hgy hΔ, add_neg_cancel]

      by_cases hsp : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂) = x₀
      · have hAns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ y₂)) :=
          WeierstrassCurve.Affine.nonsingular_add h₁ h₂ fun hxy => hx12 hxy.1
        have hK0 : veluPointMap2 hQ hgy hΔ
            ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) = 0 := by
          rw [WeierstrassCurve.Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hQ hgy hΔ hAns hsp
        have hφ1 : veluPointMap2 hQ hgy hΔ (.some x₁ y₁ h₁)
            = -(veluPointMap2 hQ hgy hΔ (.some x₂ y₂ h₂)) := by
          have heq : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = -(.some x₂ y₂ h₂)
                + ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂) := by abel
          rw [heq, veluPointMap2_add_of_right_ker hQ hgy hΔ hK0,
            veluPointMap2_neg hQ hgy hΔ]
        rw [hK0, hφ1, neg_add_cancel]

      by_cases hsm : W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))
          = x₀
      · have h₂' : W.toAffine.Nonsingular x₂ (W.toAffine.negY x₂ y₂) :=
          (WeierstrassCurve.Affine.nonsingular_neg ..).mpr h₂
        have hDns : W.toAffine.Nonsingular
            (W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂)))
            (W.toAffine.addY x₁ x₂ y₁ (W.toAffine.slope x₁ x₂ y₁ (W.toAffine.negY x₂ y₂))) :=
          WeierstrassCurve.Affine.nonsingular_add h₁ h₂' fun hxy => hx12 hxy.1
        have hKD : veluPointMap2 hQ hgy hΔ
            ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) = 0 := by
          rw [sub_eq_add_neg, WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.add_of_X_ne hx12]
          exact veluPointMap2_some_of_eq hQ hgy hΔ hDns hsm

        have hφeq : veluPointMap2 hQ hgy hΔ (.some x₁ y₁ h₁)
            = veluPointMap2 hQ hgy hΔ (.some x₂ y₂ h₂) := by
          have heq : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point)
              = (WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point)
                + ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
          rw [heq, veluPointMap2_add_of_right_ker hQ hgy hΔ hKD]

        have heq2 : (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) + .some x₂ y₂ h₂
            = ((WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ : W.toAffine.Point) + .some x₂ y₂ h₂)
              + ((WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ : W.toAffine.Point) - .some x₂ y₂ h₂) := by abel
        rw [heq2, veluPointMap2_add_of_right_ker hQ hgy hΔ hKD,
          veluPointMap2_add_self hQ hgy hΔ htan, hφeq]

      exact veluPointMap2_add_of_secant_diffAvoid hQ hgy hΔ hsec h₁ h₂ hx12 hx₁k
        hx₂k hsp hsm

include hQ hgy hΔ in

theorem veluOrderTwoAddCompatAt_of_carriers
    (hsec : KwVeluOrderTwoSecantCompatDiffAvoidAt W x₀ y₀)
    (htan : KwVeluOrderTwoTangentCompatAt W x₀ y₀) :
    KwVeluOrderTwoAddCompatAt W x₀ y₀ hQ hgy hΔ :=
  veluPointMap2_add' hQ hgy hΔ hsec htan

end Field


end
end Dubon2026.SourceEllipticVelu
