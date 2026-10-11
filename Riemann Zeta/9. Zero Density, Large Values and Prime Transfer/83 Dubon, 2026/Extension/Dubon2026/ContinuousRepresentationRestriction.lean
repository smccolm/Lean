import Dubon2026.ContinuousRepresentationCohomology

/-! # Genuine restriction of original continuous cochains and cocycles -/

namespace Dubon2026
noncomputable section

variable {R G H : Type} [CommRing R] [Group G] [Group H]
  [TopologicalSpace R] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (j : H →* G) (hj : Continuous j)

/-- Restrict the same original coefficient action along the given actual group homomorphism. -/
abbrev restrictedCoefficientRep : Rep R H := Rep.of (A.ρ.comp j)

include hj in
omit [TopologicalSpace R] [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalAddGroup A] [ContinuousSMul R A] in
/-- The same restricted action is jointly continuous along an actual continuous
group homomorphism, with the original coefficient topology unchanged. -/
theorem restrictedCoefficientAction_continuous
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) :
    Continuous (fun z : H × A => (restrictedCoefficientRep A j).ρ z.1 z.2) := by
  exact hA.comp ((hj.comp continuous_fst).prodMk continuous_snd)

/-- Restrict the original continuous one-cocycle as the same function precomposed
with the actual group homomorphism. -/
def continuousRepresentationCocycleOneRestriction :
    continuousRepresentationCocyclesOne A →ₗ[R]
      continuousRepresentationCocyclesOne (restrictedCoefficientRep A j) where
  toFun c := ⟨⟨fun h => c.val (j h), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro h k
    change c.val (j (h * k)) = A.ρ (j h) (c.val (j k)) + c.val (j h)
    rw [j.map_mul]
    exact (groupCohomology.mem_cocycles₁_iff _).mp c.val.property (j h) (j k)⟩,
      c.property.comp hj⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restrict the original continuous two-cocycle on the genuine product topology. -/
def continuousRepresentationCocycleTwoRestriction :
    continuousRepresentationCocyclesTwo A →ₗ[R]
      continuousRepresentationCocyclesTwo (restrictedCoefficientRep A j) where
  toFun c := ⟨⟨fun z => c.val (j z.1, j z.2), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro h k l
    change c.val (j (h * k), j l) + c.val (j h, j k) =
      A.ρ (j h) (c.val (j k, j l)) + c.val (j h, j (k * l))
    simp only [j.map_mul]
    exact (groupCohomology.mem_cocycles₂_iff _).mp c.val.property (j h) (j k) (j l)⟩,
      c.property.comp ((hj.comp continuous_fst).prodMk (hj.comp continuous_snd))⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The original degree-zero continuous coboundary restricts to the coboundary
of the same original coefficient vector. -/
theorem continuousRepresentationCocycleOneRestriction_coboundary
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (a : A) :
    continuousRepresentationCocycleOneRestriction A j hj
        (continuousRepresentationCoboundaryOne A hA a) =
      continuousRepresentationCoboundaryOne (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) a := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- An original continuous one-cochain witness restricts continuously and gives
the exact restricted two-coboundary, with the same inhomogeneous differential. -/
theorem continuousRepresentationCocycleTwoRestriction_coboundary
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2)) (f : C(G, A)) :
    continuousRepresentationCocycleTwoRestriction A j hj
        (continuousRepresentationCoboundaryTwo A hA f) =
      continuousRepresentationCoboundaryTwo (restrictedCoefficientRep A j)
        (restrictedCoefficientAction_continuous A j hj hA) (f.comp ⟨j, hj⟩) := by
  apply Subtype.ext
  apply Subtype.ext
  funext z
  rcases z with ⟨h, k⟩
  change A.ρ (j h) (f (j k)) - f (j h * j k) + f (j h) =
    A.ρ (j h) (f (j k)) - f (j (h * k)) + f (j h)
  rw [j.map_mul]

end
end Dubon2026
