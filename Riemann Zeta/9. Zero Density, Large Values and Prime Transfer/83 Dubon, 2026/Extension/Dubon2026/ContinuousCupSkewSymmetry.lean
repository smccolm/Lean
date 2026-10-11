import Dubon2026.ContinuousCohomologyCup

/-! # The explicit continuous homotopy for swapping two degree-one cup factors -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A B C : Rep R G)
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))

/-- The sum of the original two cup orders is the original differential of the
negative diagonal pairing cochain. This retains the inhomogeneous sign exactly. -/
theorem equivariantOneCocycleCup_swap_coboundary
    (f : groupCohomology.cocycles₁ A) (u : groupCohomology.cocycles₁ B) :
    groupCohomology.d₁₂ C (fun g => -β (f g) (u g)) =
      (equivariantOneCocycleCup A B C β hβ f u : G × G → C) +
      (equivariantOneCocycleCup B A C β.flip (fun g x y => hβ g y x) u f : G × G → C) := by
  funext z
  rcases z with ⟨g, h⟩
  have hf : f (g * h) = A.ρ g (f h) + f g :=
    (groupCohomology.mem_cocycles₁_iff _).mp f.property g h
  have hu : u (g * h) = B.ρ g (u h) + u g :=
    (groupCohomology.mem_cocycles₁_iff _).mp u.property g h
  change C.ρ g (-β (f h) (u h)) - (-β (f (g * h)) (u (g * h))) +
      (-β (f g) (u g)) = β (f g) (B.ρ g (u h)) + β (A.ρ g (f h)) (u g)
  rw [map_neg, ← hβ g (f h) (u h), hf, hu]
  simp only [map_add, LinearMap.add_apply]
  abel

variable [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
  (hC : Continuous (fun z : G × C => C.ρ z.1 z.2))

/-- The same negative diagonal cochain is continuous, so the original two cup
orders sum to zero in genuine continuous H2, not merely algebraic cohomology. -/
theorem continuousCocycleCupClass_swap_add
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousCocycleCupClass A B C β hβ hcβ hB hC f u +
      continuousCocycleCupClass B A C β.flip (fun g x y => hβ g y x)
        (hcβ.comp continuous_swap) hA hC u f = 0 := by
  change (continuousRepresentationCoboundariesTwo C hC).mkQ
      (continuousOneCocycleCup A B C β hβ hcβ hB f u) +
    (continuousRepresentationCoboundariesTwo C hC).mkQ
      (continuousOneCocycleCup B A C β.flip (fun g x y => hβ g y x)
        (hcβ.comp continuous_swap) hA u f) = 0
  rw [← map_add]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let w : C(G, C) := ⟨fun g => -β (f.val g) (u.val g),
    (hcβ.comp (f.property.prodMk u.property)).neg⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact equivariantOneCocycleCup_swap_coboundary A B C β hβ f.val u.val

/-- Swapping the two original continuous H1 factors and flipping their actual
coefficient pairing negates the resulting continuous H2 class. -/
theorem continuousH1Cup_skew
    (x : ContinuousRepresentationH1 A hA) (y : ContinuousRepresentationH1 B hB) :
    continuousH1Cup A B C β hβ hcβ hA hB hC x y =
      -continuousH1Cup B A C β.flip (fun g v w => hβ g w v)
        (hcβ.comp continuous_swap) hB hA hC y x := by
  induction x using Quotient.inductionOn' with
  | h f =>
    induction y using Quotient.inductionOn' with
    | h u =>
      apply eq_neg_iff_add_eq_zero.mpr
      exact continuousCocycleCupClass_swap_add A B C β hβ hcβ hA hB hC f u

end
end Dubon2026
