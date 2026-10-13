import Dubon2026.ContinuousCohomologyCoefficientMap
import Dubon2026.ContinuousH2RestrictionComposition

/-! # Original H2 restriction along a commuting finite-stage square

The comparison keeps the original coefficient map and both cochain arguments.
It transfers actual local inflation vanishing to arithmetic restriction in the
DUB-17 finite-support chain; the field square is proved separately.
-/

namespace Dubon2026
noncomputable section

variable {R G Q H L : Type} [CommRing R]
  [Group G] [Group Q] [Group H] [Group L]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace Q]
  [TopologicalSpace H] [TopologicalSpace L]
  [IsTopologicalGroup G] [IsTopologicalGroup Q]
  [IsTopologicalGroup H] [IsTopologicalGroup L]
  (A : Rep R G) (B : Rep R Q)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : Q × B => B.ρ z.1 z.2))
  (π : G →* Q) (hπ : Continuous π) (j : H →* G) (hj : Continuous j)
  (k : L →* Q) (hk : Continuous k) (r : H →* L) (hr : Continuous r)
  (hsq : π.comp j = k.comp r)
  (φ : B →ₗ[R] A) (hφ : Continuous φ)
  (hφρ : ∀ g b, φ (B.ρ (π g) b) = A.ρ g (φ b))

include hsq hφρ in
omit [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace Q]
  [TopologicalSpace H] [TopologicalSpace L] [IsTopologicalGroup G]
  [IsTopologicalGroup Q] [IsTopologicalGroup H] [IsTopologicalGroup L]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B] in
/-- The genuine coefficient map is equivariant for the two paths around the
proved restriction square. -/
theorem continuousH2RestrictionSquare_coefficient (g : H) (b : B) :
    φ ((restrictedCoefficientRep (restrictedCoefficientRep B k) r).ρ g b) =
      (restrictedCoefficientRep A j).ρ g (φ b) := by
  change φ (B.ρ (k (r g)) b) = A.ρ (j g) (φ b)
  have he : π (j g) = k (r g) := DFunLike.congr_fun hsq g
  rw [← he]
  exact hφρ (j g) b

include hsq in
/-- Vanishing after actual local finite-stage inflation implies vanishing of
the corresponding original arithmetic restriction, with no coefficient or
restriction comparison left implicit. -/
theorem continuousH2RestrictionSquare_eq_zero
    (x : ContinuousRepresentationH2 B hB)
    (hx : continuousRepresentationH2Restriction (restrictedCoefficientRep B k)
      (restrictedCoefficientAction_continuous B k hk hB) r hr
      (continuousRepresentationH2Restriction B hB k hk x) = 0) :
    continuousRepresentationH2Restriction A hA j hj
      (continuousCoefficientH2Map (restrictedCoefficientRep B π) A φ hφ hφρ
        (restrictedCoefficientAction_continuous B π hπ hB) hA
        (continuousRepresentationH2Restriction B hB π hπ x)) = 0 := by
  let C := restrictedCoefficientRep (restrictedCoefficientRep B k) r
  let D := restrictedCoefficientRep A j
  have hC := restrictedCoefficientAction_continuous (restrictedCoefficientRep B k) r hr
    (restrictedCoefficientAction_continuous B k hk hB)
  have hD := restrictedCoefficientAction_continuous A j hj hA
  let ψ := continuousCoefficientH2Map C D φ hφ
    (continuousH2RestrictionSquare_coefficient A B π j k r hsq φ hφρ) hC hD
  have he : continuousRepresentationH2Restriction A hA j hj
      (continuousCoefficientH2Map (restrictedCoefficientRep B π) A φ hφ hφρ
        (restrictedCoefficientAction_continuous B π hπ hB) hA
        (continuousRepresentationH2Restriction B hB π hπ x)) =
      ψ (continuousRepresentationH2Restriction (restrictedCoefficientRep B k)
        (restrictedCoefficientAction_continuous B k hk hB) r hr
        (continuousRepresentationH2Restriction B hB k hk x)) := by
    induction x using Submodule.Quotient.induction_on with
    | _ c =>
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      apply Subtype.ext
      apply Subtype.ext
      funext z
      change φ (c.val (π (j z.1), π (j z.2))) = φ (c.val (k (r z.1), k (r z.2)))
      exact congrArg (fun v : Q × Q => φ (c.val v))
        (Prod.ext (DFunLike.congr_fun hsq z.1) (DFunLike.congr_fun hsq z.2))
  rw [he, hx, map_zero]

end
end Dubon2026
