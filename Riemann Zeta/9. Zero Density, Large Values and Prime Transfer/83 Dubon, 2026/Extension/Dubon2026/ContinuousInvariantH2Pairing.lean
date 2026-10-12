import Dubon2026.ContinuousCohomologyCoefficientMap

/-! # Evaluation of original continuous H2 against an invariant coefficient

This uses the existing H2 coefficient map, rather than a replacement cohomology
group, for the degree-zero/degree-two term in DUB-17's local duality sequence.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  (A W D : Rep.{0} R G) (α : A →ₗ[R] W →ₗ[R] D)
  (hα : ∀ g a w, α (A.ρ g a) (W.ρ g w) = D.ρ g (α a w))

include hα in
/-- Pairing with an actual invariant is an original equivariant coefficient map. -/
theorem invariantRightPairing_equivariant (w : W.ρ.invariants) (g : G) (a : A) :
    α (A.ρ g a) w.val = D.ρ g (α a w.val) := by
  simpa only [w.property g] using hα g a w.val

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace W]
  [TopologicalSpace D] [IsTopologicalAddGroup D] [ContinuousSMul R D]
  (hcα : Continuous (fun z : A × W => α z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hD : Continuous (fun z : G × D => D.ρ z.1 z.2))

/-- Pair an original continuous H2 class with an actual invariant, using the
same coefficient map and the same continuous coboundary quotient. -/
def continuousInvariantRightH2Map (w : W.ρ.invariants) :
    ContinuousRepresentationH2 A hA →ₗ[R] ContinuousRepresentationH2 D hD :=
  continuousCoefficientH2Map A D (α.flip w.val)
    (hcα.comp (continuous_id.prodMk continuous_const))
    (invariantRightPairing_equivariant A W D α hα w) hA hD

/-- On the original cocycle representative, invariant evaluation is pointwise. -/
theorem continuousInvariantRightH2Map_mk (w : W.ρ.invariants)
    (c : continuousRepresentationCocyclesTwo A) :
    continuousInvariantRightH2Map A W D α hα hcα hA hD w (Submodule.Quotient.mk c) =
      (Submodule.Quotient.mk
        (continuousCoefficientCocycleTwoMap A D (α.flip w.val)
          (hcα.comp (continuous_id.prodMk continuous_const))
          (invariantRightPairing_equivariant A W D α hα w) c) :
        ContinuousRepresentationH2 D hD) := rfl

end
end Dubon2026
