import Dubon2026.FiniteScalarTraceH2Pairing
import Dubon2026.LocalCharacterDualH2Perfect
import Dubon2026.FiniteScalarCharacterH2Normalization

/-! # Original finite extension-field local H0/H2 duality

Actual trace-dual H2 and invariant equivalences transfer both annihilators
from the proved prime-field endpoint. The constructed scalar H2 invariant
and finite invariant space then give perfectness, without an H2 finiteness
or local duality hypothesis. This endpoint serves DUB-17 global duality.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The original finite-field H2/invariant pairing, normalized by the
constructed scalar extension of the genuine prime-field local invariant. -/
def localFiniteScalarCharacterDualH2InvariantPairing :
    ContinuousRepresentationH2
      (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
        hA (finiteScalarCharacter_continuous q χ hχ)) →ₗ[k] A.ρ.invariants →ₗ[k] k :=
  (continuousCharacterDualH2InvariantPairing A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
    (finiteScalarCharacter_continuous q χ hχ) hA).compr₂
      (finiteScalarCharacterH2ScalarEquiv q χ hχ
        (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)).toLinearMap

/-- The original extension-field endpoint detects its actual dual H2 class,
by genuine trace comparison with the proved prime-field endpoint. -/
theorem localFiniteScalarCharacterDualH2InvariantPairing_left_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA) := by
  letI : TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⟨rfl⟩
  let e₂ := localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
  intro x y h
  apply (finiteScalarTraceDualH2Equiv q A hA χ hχ).injective
  apply localCharacterDualH2InvariantScalarPairing_left_injective K Ω q χ hχ e heρ
    (finiteScalarPrimeRep q A) hA hq
  apply LinearMap.ext
  intro w
  obtain ⟨w, rfl⟩ := (finiteScalarPrimeInvariantEquiv q A).surjective w
  have heq := (finiteScalarCharacterH2ScalarEquiv q χ hχ e₂ (k := k)).injective (DFunLike.congr_fun h w)
  exact (congrArg e₂ (finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ x w).symm).trans
    ((congrArg (fun z => e₂ (finiteScalarTraceCharacterH2Map q χ hχ z)) heq).trans
      (congrArg e₂ (finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ y w)))

/-- The same original endpoint detects every actual invariant coefficient,
using surjectivity of the trace-dual H2 equivalence and prime-field duality. -/
theorem localFiniteScalarCharacterDualH2InvariantPairing_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA).flip := by
  letI : TopologicalSpace (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⊥
  letI : DiscreteTopology (characterDualCoefficientRep (finiteScalarPrimeRep q A) χ) := ⟨rfl⟩
  let e₂ := localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ
  haveI := localCharacterDualH2InvariantScalarPairing_isPerfPair K Ω q χ hχ e heρ
    (finiteScalarPrimeRep q A) hA hq
  intro x y h
  apply (finiteScalarPrimeInvariantEquiv q A).injective
  apply (LinearMap.IsPerfPair.bijective_right
    (localCharacterDualH2InvariantScalarPairing K Ω q χ hχ e heρ (finiteScalarPrimeRep q A) hA)).injective
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := (finiteScalarTraceDualH2Equiv q A hA χ hχ).surjective z
  have heq := (finiteScalarCharacterH2ScalarEquiv q χ hχ e₂ (k := k)).injective (DFunLike.congr_fun h z)
  exact (congrArg e₂ (finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ z x).symm).trans
    ((congrArg (fun v => e₂ (finiteScalarTraceCharacterH2Map q χ hχ v)) heq).trans
      (congrArg e₂ (finiteScalarTraceCharacterH2Map_invariantPairing q A hA χ hχ z y)))

/-- The actual local H0/H2 endpoint is perfect for arbitrary finite
extension-field coefficient actions, with both annihilators proved. -/
theorem localFiniteScalarCharacterDualH2InvariantPairing_isPerfPair (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI : Module.Finite k A.ρ.invariants := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective'
    (p := localFiniteScalarCharacterDualH2InvariantPairing K Ω q χ hχ e heρ A hA)
    (localFiniteScalarCharacterDualH2InvariantPairing_left_injective K Ω q χ hχ e heρ A hA hq)
    (localFiniteScalarCharacterDualH2InvariantPairing_right_injective K Ω q χ hχ e heρ A hA hq)

end
end Dubon2026
