import Dubon2026.ContinuousCoefficientConnectingLift

/-! # The actual continuous two-cocycle of the original coefficient connecting construction -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul R B]
  [TopologicalSpace C] [DiscreteTopology C] [ContinuousSMul R C]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- The original lift boundary lies in the actual inclusion range. Its genuine
preimage is a continuous original two-cocycle, by injectivity, equivariance and
the original boundary-squared-zero identity. -/
def coefficientConnectingTwoCocycle (c : continuousRepresentationCocyclesOne C) :
    continuousRepresentationCocyclesTwo A := by
  let d := continuousRepresentationCoboundaryTwo B hB
    (coefficientConnectingOneLift B C ψ hψ c)
  let f : G × G → A := fun z => exactCoefficientPreimage φ hφ (d.val z)
  have hi : ∀ z, φ (f z) = d.val z := by
    intro z
    exact exactCoefficientPreimage_map φ hφ (d.val z)
      (coefficientConnectingBoundary_mem_range A B C φ ψ hψ hψρ hExact hB c z)
  refine ⟨⟨f, ?_⟩, (exactCoefficientPreimage_continuous φ hφ).comp d.property⟩
  apply (groupCohomology.mem_cocycles₂_iff _).mpr
  intro g h t
  apply hφ
  change φ (f (g * h, t) + f (g, h)) = φ (A.ρ g (f (h, t)) + f (g, h * t))
  rw [map_add, map_add, hφρ, hi, hi, hi, hi]
  exact (groupCohomology.mem_cocycles₂_iff _).mp d.val.property g h t

/-- The connecting cocycle is the literal original coefficient preimage of
the original degree-one differential of the chosen continuous lift. -/
theorem coefficientConnectingTwoCocycle_apply
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val z =
      exactCoefficientPreimage φ hφ
        ((continuousRepresentationCoboundaryTwo B hB
          (coefficientConnectingOneLift B C ψ hψ c)).val z) := by
  rfl

/-- The original inclusion carries the connecting cocycle back to exactly
the original continuous coboundary of the actual lifted one-cochain. -/
theorem coefficientConnectingTwoCocycle_map
    (c : continuousRepresentationCocyclesOne C) (z : G × G) :
    φ ((coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val z) =
      (continuousRepresentationCoboundaryTwo B hB
        (coefficientConnectingOneLift B C ψ hψ c)).val z := by
  rw [coefficientConnectingTwoCocycle_apply]
  exact exactCoefficientPreimage_map φ hφ _
    (coefficientConnectingBoundary_mem_range A B C φ ψ hψ hψρ hExact hB c z)

/-- The constructed original cocycle class maps to zero under the genuine
coefficient-induced H2 map, with the original lifted continuous cochain as witness.
Descent of this construction to the source H1 is still a separate obligation. -/
theorem coefficientConnectingTwoCocycle_image_class_zero
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (hcφ : Continuous φ)
    (c : continuousRepresentationCocyclesOne C) :
    continuousCoefficientH2Map A B φ hcφ hφρ hA hB
      (Submodule.Quotient.mk
        (coefficientConnectingTwoCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)) = 0 := by
  rw [continuousCoefficientH2Map_mk]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨coefficientConnectingOneLift B C ψ hψ c, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext z
  exact (coefficientConnectingTwoCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c z).symm

end
end Dubon2026
