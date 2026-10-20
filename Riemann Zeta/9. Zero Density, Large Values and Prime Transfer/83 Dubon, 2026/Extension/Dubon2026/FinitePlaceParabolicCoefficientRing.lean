import Dubon2026.FinitePlaceParabolicFamilyQuotient
import Dubon2026.FinitePrimaryGroupAlgebraComplete

/-! # The actual parabolic auxiliary coefficient ring

The source finite auxiliary quotient and its maximal primary quotient
now instantiate the already proved group-algebra results. This removes
locality, completeness and primary-group certificates for this exact
coefficient ring in DUB-17's BLGG Section 3.6 patching dependency.
The global unitary levels and their localized Hecke modules remain separate.
-/

namespace Dubon2026

noncomputable section

open NumberField IsDedekindDomain IsLocalRing
open scoped NumberField

/-- The actual auxiliary primary group algebra is local with its original augmentation. -/
theorem finitePlaceParabolicCoefficientRing_isLocal
    (K O : Type*) [Field K] [NumberField K] [CommRing O] [IsLocalRing O]
    {S : Type*} [Finite S] (v : S → HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    [Fact q.Prime] [CharP (ResidueField O) q] :
    IsLocalRing (MonoidAlgebra O (FinitePlaceParabolicFamilyDelta K v n q)) :=
  finitePrimaryGroupAlgebra_isLocal O (FinitePlaceParabolicFamilyDelta K v n q)
    q Fact.out (finitePlaceParabolicFamilyDelta_isPGroup K v n q)

/-- Its unique maximal ideal is exactly the inverse image of the coefficient maximal ideal. -/
theorem finitePlaceParabolicCoefficientRing_maximalIdeal
    (K O : Type*) [Field K] [NumberField K] [CommRing O] [IsLocalRing O]
    {S : Type*} [Finite S] (v : S → HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    [Fact q.Prime] [CharP (ResidueField O) q]
    (J : Ideal (MonoidAlgebra O (FinitePlaceParabolicFamilyDelta K v n q))) [J.IsMaximal] :
    J = Ideal.comap
      (coefficientGroupAlgebraAugmentation O (FinitePlaceParabolicFamilyDelta K v n q)).toRingHom
      (maximalIdeal O) :=
  finitePrimaryGroupAlgebra_maximalIdeal_eq O (FinitePlaceParabolicFamilyDelta K v n q)
    q Fact.out (finitePlaceParabolicFamilyDelta_isPGroup K v n q) J

/-- The literal source auxiliary coefficient ring has the required complete local topology. -/
theorem finitePlaceParabolicCoefficientRing_completeData
    (K O : Type) [Field K] [NumberField K] [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O]
    {S : Type} [Finite S] (v : S → HeightOneSpectrum (𝓞 K)) (n q : ℕ)
    [Fact q.Prime] [CharP (ResidueField O) q] :
    let D := FinitePlaceParabolicFamilyDelta K v n q
    letI : TopologicalSpace (MonoidAlgebra O D) := moduleTopology O (MonoidAlgebra O D)
    letI : Module.Finite O (MonoidAlgebra O D) := Module.Finite.of_basis (MonoidAlgebra.basis D O)
    letI := IsModuleTopology.isTopologicalRing O (MonoidAlgebra O D)
    letI := finitePlaceParabolicCoefficientRing_isLocal K O v n q
    IsNoetherianRing (MonoidAlgebra O D) ∧ IsTopologicalRing (MonoidAlgebra O D) ∧
      CompactSpace (MonoidAlgebra O D) ∧ T2Space (MonoidAlgebra O D) ∧
      IsAdicTopology (MonoidAlgebra O D) ∧
      IsAdicComplete (maximalIdeal (MonoidAlgebra O D)) (MonoidAlgebra O D) :=
  finitePrimaryGroupAlgebra_completeData O (FinitePlaceParabolicFamilyDelta K v n q)
    q Fact.out (finitePlaceParabolicFamilyDelta_isPGroup K v n q)

end
end Dubon2026
