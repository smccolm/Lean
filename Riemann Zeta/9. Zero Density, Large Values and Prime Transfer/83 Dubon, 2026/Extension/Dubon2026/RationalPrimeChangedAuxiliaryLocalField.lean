import Dubon2026.RationalPrimeChangedRootAuxiliaryMap
import Dubon2026.LocalFieldMonicRootIntegerEquiv
import Dubon2026.LocalFieldOriginalNorm
import Dubon2026.SpectralValuationExtension

/-! # The actual changed auxiliary field as a local field

The proved fraction-field identification puts the spectral finite-extension
topology on the actual auxiliary field.  The integral-closure equivalence then
transports the literal changed root to an irreducible element of the actual
integer ring, with its exact field value and norm.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

attribute [local instance] rationalPrimeChangedIntegralRootDomain
  rationalPrimeChangedIntegralRootDVR rationalPrimeWittPrime
  wittCyclotomicRootDomain wittCyclotomicRootFaithful wittCyclotomicFieldAlgebra
  wittCyclotomicFieldTower rationalPrimeWittOriginalAlgebra
  rationalPrimeWittCyclotomicAlgebra rationalPrimeWittCyclotomicTower
  rationalPrimeWittCyclotomicModule rationalPrimeWittCyclotomicMulAction

/-- The actual auxiliary field carries the spectral finite-extension
local-field structure extending the original completion. -/
theorem rationalPrimeChangedAuxiliary_exists_local_structure
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a) :
    let K := rationalPrimeLocalField p hp
    let E := rationalPrimeChangedAuxiliaryField p hp n u
    ∃ (_ : FiniteDimensional K E) (_ : ValuativeRel E)
      (_ : TopologicalSpace E) (_ : IsNonarchimedeanLocalField E)
      (_ : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)),
      True := by
  let K := rationalPrimeLocalField p hp
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  letI : FiniteDimensional K E :=
    (rationalPrimeChangedAuxiliaryField_finrank_and_finite p hp n a u hu ha).2
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let normK := localFieldOriginalNorm K
  letI : NontriviallyNormedField K := normK
  letI : NormedField K := normK.toNormedField
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible :=
    localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField E := spectralNorm.nontriviallyNormedField K E
  letI : NormedAlgebra K E := spectralNorm.normedAlgebra K E
  haveI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  haveI : IsNonarchimedeanLocalField E :=
    spectralFiniteExtension_isNonarchimedeanLocalField K E
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) :=
    spectralValuation_hasExtension K E
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, trivial⟩

/-- For any realized local structure supplied by the preceding theorem, the
literal changed root is an irreducible element of the actual auxiliary integer
ring.  Its field value and exact norm are preserved. -/
theorem rationalPrimeChangedAuxiliary_exists_integer_uniformizer
    (p : ℕ) (hp : p.Prime) (n a : ℕ)
    (u : 𝒪[rationalPrimeLocalField p hp]ˣ) (hu : u.val = a) (ha : ¬p ∣ a)
    [FiniteDimensional (rationalPrimeLocalField p hp)
      (rationalPrimeChangedAuxiliaryField p hp n u)]
    [ValuativeRel (rationalPrimeChangedAuxiliaryField p hp n u)]
    [TopologicalSpace (rationalPrimeChangedAuxiliaryField p hp n u)]
    [IsNonarchimedeanLocalField (rationalPrimeChangedAuxiliaryField p hp n u)]
    [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension
      (ValuativeRel.valuation (rationalPrimeChangedAuxiliaryField p hp n u))] :
    ∃ θE : 𝒪[rationalPrimeChangedAuxiliaryField p hp n u],
      Irreducible θE ∧
      algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
          (rationalPrimeChangedAuxiliaryField p hp n u) θE =
        rationalPrimeChangedAuxiliaryPoint p hp n u ∧
      Algebra.norm (rationalPrimeLocalField p hp)
          (-algebraMap 𝒪[rationalPrimeChangedAuxiliaryField p hp n u]
            (rationalPrimeChangedAuxiliaryField p hp n u) θE) =
        (a : rationalPrimeLocalField p hp) * p := by
  let K := rationalPrimeLocalField p hp
  let O := 𝒪[K]
  let f := rationalPrimeChangedIntegralPolynomial p hp n u
  let B := AdjoinRoot f
  let E := rationalPrimeChangedAuxiliaryField p hp n u
  let θ := rationalPrimeChangedAuxiliaryPoint p hp n u
  let φ := rationalPrimeChangedIntegralRootAlgHom p hp n a u hu ha
  letI : Algebra B E := φ.toAlgebra
  haveI : IsScalarTower O B E := IsScalarTower.of_algebraMap_eq fun x =>
    φ.commutes x |>.symm
  haveI : IsFractionRing B E :=
    rationalPrimeChangedAuxiliaryField_isFractionRing p hp n a u hu ha
  let e := localFieldMonicRootIntegerEquiv K E f
    (rationalPrimeChangedIntegralPolynomial_monic p hp n u)
  let θE : 𝒪[E] := e (AdjoinRoot.root f)
  have hθE : Irreducible θE :=
    (MulEquiv.irreducible_iff (f := e.toMulEquiv)).mpr
      (rationalPrimeChangedIntegralRoot_irreducible p hp n u)
  have hvalue : algebraMap 𝒪[E] E θE = θ := by
    exact (localFieldMonicRootIntegerEquiv_coefficient K E f
      (rationalPrimeChangedIntegralPolynomial_monic p hp n u)
      (AdjoinRoot.root f)).trans
        (rationalPrimeChangedIntegralRootAlgHom_root p hp n a u hu ha)
  refine ⟨θE, hθE, hvalue, ?_⟩
  rw [hvalue]
  exact rationalPrimeChangedAuxiliaryPoint_norm_neg p hp n a u hu ha

end
end Dubon2026
