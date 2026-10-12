import Dubon2026.LocalFiniteScalarCharacterDualAnnihilators
import Dubon2026.FiniteScalarCharacterH2Normalization

/-! # Original finite extension-field local H1 perfectness

Normalize the original extension-field cup by the constructed original H2
invariant, and apply both proved actual annihilators and original H1
finiteness. This closes the finite extension-field character-dual perfectness
input needed before DUB-17's actual trace-zero matrix specialization.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul finiteScalarPrimeModule

variable {k : Type} [Field k] [Finite k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k] (χ : Gal(Ω/K) →* ZMod q) (hχ : Continuous χ)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

variable (A : Rep.{0} k Gal(Ω/K)) [Finite A] [TopologicalSpace A] [DiscreteTopology A]
  [TopologicalSpace (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  [DiscreteTopology (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))]
  (hA : Continuous (fun z : Gal(Ω/K) × A => A.ρ z.1 z.2))

/-- The actual extension-field character-dual H1 cup normalized by the
original local prime-field invariant extended over the original coefficient field. -/
def localFiniteScalarCharacterDualH1ScalarCup :
    ContinuousRepresentationH1 A hA →ₗ[k]
      ContinuousRepresentationH1
        (characterDualCoefficientRep A ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
        (finiteCharacterDualAction_continuous A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
          hA (finiteScalarCharacter_continuous q χ hχ)) →ₗ[k] k :=
  (continuousCharacterDualH1Cup A ((algebraMap (ZMod q) k).toMonoidHom.comp χ)
    (finiteScalarCharacter_continuous q χ hχ) hA).compr₂
    (finiteScalarCharacterH2ScalarEquiv q χ hχ
      (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ)).toLinearMap

/-- The genuine normalized extension-field cup detects its left
original H1 argument through the proved original H2 scalar equivalence. -/
theorem localFiniteScalarCharacterDualH1ScalarCup_left_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA) := by
  intro x y h
  apply localFiniteScalarCharacterDualH1Cup_left_injective K Ω q χ hχ e heρ A hA hq
  apply LinearMap.ext
  intro z
  apply (finiteScalarCharacterH2ScalarEquiv q χ hχ
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ) (k := k)).injective
  exact DFunLike.congr_fun h z

/-- The genuine normalized extension-field cup detects its right
original H1 argument through the proved original H2 scalar equivalence. -/
theorem localFiniteScalarCharacterDualH1ScalarCup_right_injective (hq : (q : K) ≠ 0) :
    Function.Injective (localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).flip := by
  intro x y h
  apply localFiniteScalarCharacterDualH1Cup_right_injective K Ω q χ hχ e heρ A hA hq
  apply LinearMap.ext
  intro z
  apply (finiteScalarCharacterH2ScalarEquiv q χ hχ
    (localCharacterLineH2ScalarEquiv K Ω q χ hχ e heρ) (k := k)).injective
  exact DFunLike.congr_fun h z

/-- The original scalar-valued local H1 pairing is perfect for arbitrary
finite continuous extension-field coefficient actions. Actual field trace,
both annihilators, scalar H2 normalization and original H1 finiteness are
proved; no local cohomological duality premise is retained. -/
theorem localFiniteScalarCharacterDualH1ScalarCup_isPerfPair (hq : (q : K) ≠ 0) :
    (localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA).IsPerfPair := by
  haveI := localField_finiteScalarCoefficientH1 q K Ω A hA hq
  haveI : Module.Finite k (ContinuousRepresentationH1 A hA) := Module.Finite.of_finite
  exact LinearMap.IsPerfPair.of_injective (p := localFiniteScalarCharacterDualH1ScalarCup K Ω q χ hχ e heρ A hA)
    (localFiniteScalarCharacterDualH1ScalarCup_left_injective K Ω q χ hχ e heρ A hA hq)
    (localFiniteScalarCharacterDualH1ScalarCup_right_injective K Ω q χ hχ e heρ A hA hq)

end
end Dubon2026
