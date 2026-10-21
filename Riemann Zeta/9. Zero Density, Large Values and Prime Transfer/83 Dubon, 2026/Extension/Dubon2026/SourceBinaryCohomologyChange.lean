import Dubon2026.SourceIntegralCohomologyFinite
import Dubon2026.SourceSemilinearCohomology
import Dubon2026.HomogeneousCoefficientChange

/-! Literal coefficient change on the original binary H1.
DUB-17/18 -> residual modular Galois association -> integral-to-residual
H1 eigenclass. Reuse the proved homogeneous coefficient map and its matrix
intertwining theorem, then the native cocycle quotient construction.
No comparison of coefficient conventions is assumed.
-/

namespace Dubon2026
noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (Q w : ℕ)

/-- Actual entrywise coefficient change intertwines the original Gamma0 binary actions. -/
theorem sourceBinaryCoefficientMap_equivariant (g : Gamma0 Q)
    (v : sourceBinaryCoefficientRep R Q w) :
    homogeneousCoefficientMap w φ ((sourceBinaryCoefficientRep R Q w).ρ g v) =
      (sourceBinaryCoefficientRep S Q w).ρ g (homogeneousCoefficientMap w φ v) := by
  change homogeneousCoefficientMap w φ
    (homogeneousMatrixAction w (g.val.val.map (Int.castRingHom R)) v) =
      homogeneousMatrixAction w (g.val.val.map (Int.castRingHom S))
        (homogeneousCoefficientMap w φ v)
  rw [homogeneousCoefficientMap_intertwines]
  have hm : (g.val.val.map (Int.castRingHom R)).map φ =
      g.val.val.map (Int.castRingHom S) := by
    ext i j
    exact map_intCast φ _
  rw [hm]

/-- The actual source binary cocycles with their coefficients changed by the given ring homomorphism. -/
def sourceBinaryCocyclesChange :
    groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w) →ₛₗ[φ]
      groupCohomology.cocycles₁ (sourceBinaryCoefficientRep S Q w) :=
  sourceSemilinearCocycles _ _ φ (homogeneousCoefficientMap w φ)
    (sourceBinaryCoefficientMap_equivariant φ Q w)

/-- The source binary cocycle map has the literal original polynomial coefficient formula. -/
theorem sourceBinaryCocyclesChange_apply
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w)) (g : Gamma0 Q) :
    (sourceBinaryCocyclesChange φ Q w c g).val =
      MvPolynomial.map φ (c g).val := rfl

/-- Change coefficients on the full actual native binary H1. -/
def sourceBinaryH1Change :
    groupCohomology.H1 (sourceBinaryCoefficientRep R Q w) →ₛₗ[φ]
      groupCohomology.H1 (sourceBinaryCoefficientRep S Q w) :=
  sourceSemilinearH1 _ _ φ (homogeneousCoefficientMap w φ)
    (sourceBinaryCoefficientMap_equivariant φ Q w)

/-- The native H1 coefficient map is represented by the actual transformed source cocycle. -/
theorem sourceBinaryH1Change_cocycle
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w)) :
    sourceBinaryH1Change φ Q w (groupCohomology.H1π _ c) =
      groupCohomology.H1π _ (sourceBinaryCocyclesChange φ Q w c) := by
  simpa only [sourceBinaryH1Change, sourceBinaryCocyclesChange] using
    sourceSemilinearH1_cocycle (sourceBinaryCoefficientRep R Q w)
      (sourceBinaryCoefficientRep S Q w) φ (homogeneousCoefficientMap w φ)
      (sourceBinaryCoefficientMap_equivariant φ Q w) c

end
end Dubon2026
