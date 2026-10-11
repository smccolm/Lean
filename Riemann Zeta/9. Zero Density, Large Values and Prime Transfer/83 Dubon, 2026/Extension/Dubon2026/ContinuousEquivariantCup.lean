import Dubon2026.ContinuousRepresentationCohomology
import Dubon2026.EquivariantCupCoboundaries
import Mathlib.LinearAlgebra.BilinearMap

/-! # The actual continuous degree-one cup product before passing to quotients -/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A B C : Rep R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [IsTopologicalAddGroup B] [ContinuousSMul R B]
  [TopologicalSpace C] [IsTopologicalAddGroup C] [ContinuousSMul R C]
  (β : A →ₗ[R] B →ₗ[R] C)
  (hβ : ∀ g x y, β (A.ρ g x) (B.ρ g y) = C.ρ g (β x y))
  (hcβ : Continuous (fun z : A × B => β z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

include hcβ hB in
omit [IsTopologicalGroup G] [IsTopologicalAddGroup C] [ContinuousSMul R C] in
/-- The actual inhomogeneous cup cochain is jointly continuous in its two group
arguments. This uses the genuine coefficient pairing and original continuous action. -/
theorem equivariantOneCocycleCup_continuous
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    Continuous (fun z => equivariantOneCocycleCup A B C β hβ f.val u.val z) := by
  exact hcβ.comp ((f.property.comp continuous_fst).prodMk
    (hB.comp (continuous_fst.prodMk (u.property.comp continuous_snd))))

/-- The genuine cup of the original continuous one-cocycles, as an actual
continuous two-cocycle with its algebraic differential and topology both proved. -/
def continuousOneCocycleCup
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B) :
    continuousRepresentationCocyclesTwo C :=
  ⟨equivariantOneCocycleCup A B C β hβ f.val u.val,
    equivariantOneCocycleCup_continuous A B C β hβ hcβ hB f u⟩

/-- The actual continuous cocycle cup is bilinear in the original coefficient
modules, with no quotient or cohomological perfectness assumption. -/
def continuousOneCocycleCupBilinear :
    continuousRepresentationCocyclesOne A →ₗ[R]
      continuousRepresentationCocyclesOne B →ₗ[R] continuousRepresentationCocyclesTwo C :=
  LinearMap.mk₂ R (continuousOneCocycleCup A B C β hβ hcβ hB)
    (by
      intro f₁ f₂ u
      apply Subtype.ext
      apply groupCohomology.cocycles₂_ext
      intro g h
      change β (f₁.val g + f₂.val g) (B.ρ g (u.val h)) = _
      rw [map_add, LinearMap.add_apply]
      rfl)
    (by
      intro r f u
      apply Subtype.ext
      apply groupCohomology.cocycles₂_ext
      intro g h
      change β (r • f.val g) (B.ρ g (u.val h)) = _
      rw [map_smul, LinearMap.smul_apply]
      rfl)
    (by
      intro f u₁ u₂
      apply Subtype.ext
      apply groupCohomology.cocycles₂_ext
      intro g h
      change β (f.val g) (B.ρ g (u₁.val h + u₂.val h)) = _
      rw [map_add, map_add]
      rfl)
    (by
      intro r f u
      apply Subtype.ext
      apply groupCohomology.cocycles₂_ext
      intro g h
      change β (f.val g) (B.ρ g (r • u.val h)) = _
      rw [map_smul, map_smul]
      rfl)

omit [IsTopologicalGroup G] in
/-- The actual continuous bilinear map retains the original cup formula at every
pair of original group elements. -/
theorem continuousOneCocycleCupBilinear_apply
    (f : continuousRepresentationCocyclesOne A) (u : continuousRepresentationCocyclesOne B)
    (g h : G) :
    (continuousOneCocycleCupBilinear A B C β hβ hcβ hB f u).val (g, h) =
      β (f.val g) (B.ρ g (u.val h)) := by
  rfl

end
end Dubon2026
