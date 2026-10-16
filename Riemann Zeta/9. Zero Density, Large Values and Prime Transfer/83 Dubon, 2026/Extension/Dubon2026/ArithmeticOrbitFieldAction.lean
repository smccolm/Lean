import Dubon2026.ArithmeticOrbitFieldEmbedding

/-! # The actual orbit embedding intertwines the stabilizer action

The literal conjugation map used in the proved Mackey formula is
intertwined by the actual coset-twisted field embedding. This is the
coefficient-action identity needed to compare an orbit cocycle with
genuine local Galois base change on DUB-17's reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra

/-- The original coset-twisted field embedding intertwines the literal
stabilizer conjugation with the actual local Galois action. -/
theorem rationalArithmeticOrbitEmbedding_equivariant
    (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
    (F : IntermediateField ℚ (rationalUnramifiedExtension a))
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F)
    (d : cosetOrbitStabilizer (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c)
    (x : rationalUnramifiedExtension a) :
    rationalArithmeticOrbitEmbedding a p hp F c
        ((show Gal(rationalUnramifiedExtension a / ℚ) from
          (cosetOrbitSubgroupMap (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
            (rationalArithmeticOrbitFixingSubgroup a F) c d).val) x) =
      d.val (rationalArithmeticOrbitEmbedding a p hp F c x) := by
  let σ := rationalArithmeticOrbitRepresentative a F c
  let τ : Gal(rationalUnramifiedExtension a / ℚ) := rationalPrimeArithmeticRestriction a p hp d.val
  let s : Gal(rationalUnramifiedExtension a / ℚ) :=
    (cosetOrbitSubgroupMap (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) c d).val
  have hf := cosetOrbitSubgroupMap_factor (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalArithmeticOrbitFixingSubgroup a F) c d
  change σ * s = τ * σ at hf
  have he := congrArg (fun g : Gal(rationalUnramifiedExtension a / ℚ) => g x) hf
  change σ (s x) = τ (σ x) at he
  change rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a (σ (s x)) =
    d.val (rationalArithmeticLocalEmbedding (K := rationalPrimeLocalClosure p hp) a (σ x))
  rw [he]
  exact rationalPrimeArithmeticRestriction_commutes a p hp d.val (σ x)

end
end Dubon2026
