import Dubon2026.CocycleAffinePermutation
import Dubon2026.ContinuousCohomologyRestriction

/-! The affine non-fixed-point test implies that the same original continuous
H1 class has nonzero restriction. This is the local detection consumer needed
after prescribed Frobenius selection in DUB-17 arithmetic patching. -/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (j : H →* G) (hj : Continuous j)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- A non-coboundary value at one original local group element prevents the
restriction of the original continuous H1 class from vanishing. -/
theorem continuousH1Restriction_ne_zero_of_value
    (c : continuousRepresentationCocyclesOne A) (g : H)
    (hc : c.val (j g) ∉ LinearMap.range (A.ρ (j g) - 1)) :
    continuousRepresentationH1Restriction A hA j hj
      (Submodule.Quotient.mk c) ≠ 0 := by
  intro hz
  rw [continuousRepresentationH1Restriction_mk] at hz
  have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
  obtain ⟨x, hx⟩ := hm
  apply hc
  refine ⟨x, ?_⟩
  have he := congrArg
    (fun d : continuousRepresentationCocyclesOne (restrictedCoefficientRep A j) => d.val g) hx
  exact he

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- If the actual affine cocycle action has no fixed point at the image of a
local element, the original continuous H1 restriction is nonzero. -/
theorem continuousH1Restriction_ne_zero_of_affine_no_fixed
    (c : continuousRepresentationCocyclesOne A) (g : H)
    (hc : ¬ ∃ x : A, cocycleAffinePermutation A c.val (j g) x = x) :
    continuousRepresentationH1Restriction A hA j hj
      (Submodule.Quotient.mk c) ≠ 0 :=
  continuousH1Restriction_ne_zero_of_value A hA j hj c g
    (fun h => hc ((cocycleAffinePermutation_exists_fixed_iff A c.val (j g)).mpr h))

end
end Dubon2026
