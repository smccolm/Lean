import Dubon2026.GaloisUnitH2FiniteDirectedSystem

/-! # Actual continuous Galois H2 respects equality of original algebra structures -/

namespace Dubon2026
noncomputable section

/-- Transport the original discrete-coefficient continuous H2 along
a proved equality of the actual algebra structures. The original fields,
Krull topology and cocycles are unchanged after equality elimination. -/
def galoisUnitH2AlgebraCongruence
    {K L : Type} [Field K] [Field L] (a b : Algebra K L) (hab : a = b)
    (ha : letI := a; IsGalois K L) (hb : letI := b; IsGalois K L) :
    (letI := a
     letI := ha
     letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
     letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
     GaloisUnitContinuousH2 (K := K) (Ω := L)) ≃ₗ[ℤ]
    (letI := b
     letI := hb
     letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K L) := ⊥
     letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K L) := ⟨rfl⟩
     GaloisUnitContinuousH2 (K := K) (Ω := L)) := by
  subst b
  exact LinearEquiv.refl ℤ _

/-- The transport along proved equality of the actual algebra structures
is bijective on the original continuous cohomology classes. -/
theorem galoisUnitH2AlgebraCongruence_bijective
    {K L : Type} [Field K] [Field L] (a b : Algebra K L) (hab : a = b)
    (ha : letI := a; IsGalois K L) (hb : letI := b; IsGalois K L) :
    Function.Bijective (galoisUnitH2AlgebraCongruence a b hab ha hb) :=
  (galoisUnitH2AlgebraCongruence a b hab ha hb).bijective

end
end Dubon2026
