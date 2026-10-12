import Dubon2026.FiniteScalarTraceCohomology

/-! # Field trace preserves the actual continuous character-dual cup

The original finite extension-field cup maps to the prime-field cup under
genuine scalar trace and the proved coefficient H1 identifications. This
comparison transfers the already proved local prime-field annihilators to
the original extension-field action for DUB-17's trace-zero local pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] finiteScalarPrimeModule characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Finite k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep.{0} k G) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))

variable (χ : G →* ZMod q) (hχ : Continuous χ)

variable
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]
  [DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ)]

/-- Trace of the original extension-field cup equals the original
prime-field cup, on the same cocycles under the actual coefficient identifications. -/
theorem finiteScalarTraceCharacterH2Map_cup
    (x : ContinuousRepresentationH1 A hA)
    (y : ContinuousRepresentationH1
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ))) :
    finiteScalarTraceCharacterH2Map q χ hχ
      (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        (finiteScalarCharacter_continuous q χ hχ) hA x y) =
      continuousCharacterDualH1Cup (finiteScalarPrimeRep q A) χ hχ hA
        (finiteScalarPrimeH1Equiv q A hA x) (finiteScalarTraceDualH1Equiv q A hA χ hχ y) := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    induction y using Submodule.Quotient.induction_on with
    | _ u =>
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      apply Subtype.ext
      funext z
      exact DFunLike.congr_fun (finiteScalarTraceDualMap_equivariant q A χ z.1 (u.val z.2)) (c.val z.1)

end
end Dubon2026
