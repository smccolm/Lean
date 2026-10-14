import Dubon2026.ArithmeticCyclotomicUnramifiedReciprocity
import Dubon2026.ArithmeticFiniteLocalCyclicity
import Dubon2026.SpectralFiniteExtensionLocalField
import Dubon2026.LocalFieldOriginalNorm

/-! # Actual cyclic arithmetic reciprocity away from the cyclotomic conductor

The local valuation, topology, local-field structure and extending valuation
are constructed on the literal finite local compositum. The established
unramified cyclotomic formula therefore has no local structure or
unramifiedness premise. Global cyclicity is the property already supplied by
the actual arithmetic Kummer cyclic-carry theorem on DUB-17's route to
arithmetic invariant sum-zero, global duality and automorphy.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra

variable (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
  [IsCyclic Gal(F/ℚ)] (p : ℕ) (hp : p.Prime)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]

/-- Transport the proved cyclicity across the unique rational algebra on the original global field. -/
local instance arithmeticCyclotomicLocalCyclic :
    IsCyclic Gal(rationalArithmeticFiniteLocalStage a F p hp / rationalPrimeLocalField p hp) := by
  let A₀ : Algebra ℚ F := inferInstance
  have h₀ : letI := A₀; IsCyclic Gal(F/ℚ) := inferInstance
  have hc : ∀ A : Algebra ℚ F, letI := A; IsCyclic Gal(F/ℚ) := by
    intro A
    have hA : A = A₀ := Subsingleton.elim _ _
    cases hA
    exact h₀
  exact @rationalArithmeticFiniteLocalStage_isCyclic a F (hc _) p hp

/-- The actual cyclic arithmetic local reciprocity character away from the conductor, with all local-stage field structures and unramifiedness derived. -/
theorem arithmeticCyclotomic_reciprocity_away_conductor
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] (hpn : ¬p ∣ n)
    {ζ : F} (hζ : IsPrimitiveRoot ζ n) (u : (rationalPrimeLocalField p hp)ˣ) :
    letI := arithmeticCyclotomicLocalCyclic a F p hp
    hζ.autToPow ℚ (rationalArithmeticFiniteLocalRestriction a F p hp
      (localFieldFiniteCyclicReciprocity (rationalPrimeLocalField p hp)
        (rationalPrimeLocalClosure p hp) (rationalArithmeticFiniteLocalStage a F p hp)
        (Additive.ofMul u)).toMul) =
      ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hpn) ^
        localFieldUnitOrder (rationalPrimeLocalField p hp) (Additive.ofMul u) := by
  let K := rationalPrimeLocalField p hp
  let M := rationalArithmeticFiniteLocalStage a F p hp
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  let normK := localFieldOriginalNorm K
  letI : NontriviallyNormedField K := normK
  letI : NormedField K := normK.toNormedField
  haveI : CompleteSpace K := localFieldOriginalNorm_complete K
  haveI : IsUltrametricDist K := localFieldOriginalNorm_isUltrametric K
  haveI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : NontriviallyNormedField M := spectralNorm.nontriviallyNormedField K M
  letI : NormedAlgebra K M := spectralNorm.normedAlgebra K M
  haveI : IsUltrametricDist M := IsUltrametricDist.of_normedAlgebra K
  letI : ValuativeRel M := ValuativeRel.ofValuation (NormedField.valuation (K := M))
  haveI : IsNonarchimedeanLocalField M := spectralFiniteExtension_isNonarchimedeanLocalField K M
  haveI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M) :=
    spectralValuation_hasExtension K M
  exact arithmeticCyclotomicFiniteLocal_reciprocity_character a F p hp n hpn hζ u

end
end Dubon2026
