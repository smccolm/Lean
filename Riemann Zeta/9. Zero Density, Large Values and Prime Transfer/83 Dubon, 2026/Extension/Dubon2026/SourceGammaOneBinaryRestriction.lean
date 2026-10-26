import Dubon2026.SourceGammaOneConstantHecke
import Dubon2026.SourceGammaOneCoverHeckeRepresentatives
import Dubon2026.SourceBinaryHeckeCohomology
import Dubon2026.SourceCorrespondenceOne

/-! DUB-17/18 -> all-weight adic association -> geometric Gamma1 Hecke
comparison. Use the actual diagonal cover and proved coefficient triviality
to define its literal cohomology pullback. This is the restriction leg
of the correspondence comparison, not a replacement for the surjective
transfer or its still-required Hecke compatibility. -/
namespace Dubon2026
noncomputable section
open CategoryTheory CongruenceSubgroup
variable (Q N w : ℕ) [NeZero N]

/-- Identity on the original binary vectors intertwines the actual pulled
back action with the proved constant action on the exact Gamma1 cover. -/
def sourceGammaOneBinaryRestrictionCoefficient :
    Rep.res (sourceGammaOneDiagonalHom Q N) (sourceBinaryCoefficientRep (ZMod N) Q w) ⟶
      Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
        (sourceBinaryCoefficientRep (ZMod N) Q w) :=
  Rep.ofHom {
    toLinearMap := LinearMap.id
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      change (sourceBinaryCoefficientRep (ZMod N) Q w).ρ
        (sourceGammaOneDiagonalHom Q N g) x = x
      rw [sourceGammaOneDiagonalHom_binary_trivial]
      rfl }

/-- Literal restriction of original binary cocycles to the true cover. -/
def sourceGammaOneBinaryRestrictionCocycles :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w) →ₗ[ZMod N]
      groupCohomology.cocycles₁
        (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
          (sourceBinaryCoefficientRep (ZMod N) Q w)) :=
  (groupCohomology.mapCocycles₁ (sourceGammaOneDiagonalHom Q N)
    (sourceGammaOneBinaryRestrictionCoefficient Q N w)).hom

/-- The corresponding native H1 pullback keeps the same original group
map and the same coefficient morphism. -/
def sourceGammaOneBinaryRestrictionH1 :
    groupCohomology.H1 (sourceBinaryCoefficientRep (ZMod N) Q w) →ₗ[ZMod N]
      groupCohomology.H1
        (Rep.trivial (ZMod N) (Gamma1 (Q * N ^ 2))
          (sourceBinaryCoefficientRep (ZMod N) Q w)) :=
  (groupCohomology.map (sourceGammaOneDiagonalHom Q N)
    (sourceGammaOneBinaryRestrictionCoefficient Q N w) 1).hom

/-- On every actual cocycle the restriction is literal pullback. -/
theorem sourceGammaOneBinaryRestrictionCocycles_apply
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w))
    (g : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneBinaryRestrictionCocycles Q N w c g =
      c (sourceGammaOneDiagonalHom Q N g) := rfl

/-- The native H1 pullback is induced by exactly this literal cocycle map. -/
theorem sourceGammaOneBinaryRestrictionH1_cocycle
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep (ZMod N) Q w)) :
    sourceGammaOneBinaryRestrictionH1 Q N w (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (sourceGammaOneBinaryRestrictionCocycles Q N w c) :=
  groupCohomology.H1π_comp_map_apply (sourceGammaOneDiagonalHom Q N)
    (sourceGammaOneBinaryRestrictionCoefficient Q N w) c

end
end Dubon2026
