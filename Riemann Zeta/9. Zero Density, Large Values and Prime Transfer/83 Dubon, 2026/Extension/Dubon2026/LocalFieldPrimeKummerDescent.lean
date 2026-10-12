import Dubon2026.LocalFieldKummerCoprimeDescent
import Dubon2026.OriginalCyclotomicPrimeStage
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Original prime Kummer nondegeneracy without base primitive roots

The actual cyclotomic field is constructed inside the original algebraic
closure. Its local structure, compatible valuation and coprime degree are derived.
-/

namespace Dubon2026
noncomputable section

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The actual prime Kummer root annihilator vanishes without a primitive root
in the base field. The needed cyclotomic extension and all descent premises are
constructed from q being nonzero in the original local field. -/
theorem localFieldPrimeKummer_root_eq_zero_of_cup_zero (hq : (q : K) ≠ 0)
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) q)
    (hx : ∀ χ : Gal(Ω/K) →ₜ* Multiplicative (ZMod q),
      continuousGaloisRootCharacterH1Cup q χ x = 0) : x = 0 := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : NontriviallyNormedField K := localFieldOriginalNorm K
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  haveI : NeZero (q : Ω) := ⟨by
    intro hz
    apply hq
    apply (algebraMap K Ω).injective
    simpa only [map_natCast, map_zero] using hz⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  let F := originalPrimitiveRootStage K Ω hμ
  letI : NontriviallyNormedField F := spectralNorm.nontriviallyNormedField K F
  letI : NormedAlgebra K F := spectralNorm.normedAlgebra K F
  haveI : IsUltrametricDist F := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel F := ValuativeRel.ofValuation (NormedField.valuation (K := F))
  haveI : IsNonarchimedeanLocalField F := spectralFiniteExtension_isNonarchimedeanLocalField K F
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation F) :=
    spectralValuation_hasExtension K F
  exact localFieldKummer_root_annihilator_coprime_descent K Ω F.toIntermediateField q
    (originalPrimitiveRootStage_finrank_coprime K Ω hμ)
    (originalPrimitiveRootStageRoot_isPrimitive K Ω hμ) x hx

end
end Dubon2026
