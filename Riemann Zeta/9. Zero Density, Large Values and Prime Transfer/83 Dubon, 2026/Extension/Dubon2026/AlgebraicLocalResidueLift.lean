import Dubon2026.AlgebraicLocalIntegerAction
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.Finite.Basic

/-! Lift actual residue automorphisms to the original local algebraic
Galois group. This reuses pinned profinite invariant-ring surjectivity for
DUB-17's missing unramified cyclicity and Frobenius input, on the native
integer action constructed from norm uniqueness. -/

namespace Dubon2026
noncomputable section
open scoped Pointwise

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [IsGalois K L]

attribute [local instance] algebraicLocalIntegerAction algebraicLocalIntegerBaseAlgebra

/-- The residue scalar map is the canonical quotient of the original inclusion. -/
local instance algebraicLocalResidueAlgebra :
    Algebra (algebraicLocalIntegerRing K ⧸
      (IsLocalRing.maximalIdeal (algebraicLocalIntegerRing L)).under (algebraicLocalIntegerRing K))
      (IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) :=
  Ideal.Quotient.algebraQuotientOfLEComap le_rfl

/-- Each automorphism of the original residue extension lifts to the
original Galois group and retains its literal action on every integer. -/
theorem algebraicLocal_residueAut_exists_lift
    (σ : IsLocalRing.ResidueField (algebraicLocalIntegerRing L) ≃ₐ[
      algebraicLocalIntegerRing K ⧸
        (IsLocalRing.maximalIdeal (algebraicLocalIntegerRing L)).under (algebraicLocalIntegerRing K)]
      IsLocalRing.ResidueField (algebraicLocalIntegerRing L)) :
    ∃ g : Gal(L/K), ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (g • x) = σ (IsLocalRing.residue _ x) := by
  letI : SMulCommClass Gal(L/K) (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L) :=
    algebraicLocalIntegerAction_smulComm K L
  letI : Algebra.IsInvariant (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L) Gal(L/K) :=
    algebraicLocalIntegerAction_isInvariant K L
  letI : TopologicalSpace (algebraicLocalIntegerRing L) := ⊥
  letI : DiscreteTopology (algebraicLocalIntegerRing L) := ⟨rfl⟩
  letI : ContinuousSMul Gal(L/K) (algebraicLocalIntegerRing L) :=
    algebraicLocalIntegerAction_continuous K L
  let Q := IsLocalRing.maximalIdeal (algebraicLocalIntegerRing L)
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Gal(L/K)) (Q.under (algebraicLocalIntegerRing K)) Q σ
  refine ⟨g.val, fun x => ?_⟩
  exact congrArg (fun e => e (Ideal.Quotient.mk Q x)) hg

/-- A finite original base residue field supplies a genuine original
Galois element inducing its arithmetic Frobenius on all residue classes. -/
theorem algebraicLocal_exists_residueFrobenius
    [Finite (IsLocalRing.ResidueField (algebraicLocalIntegerRing K))] :
    ∃ g : Gal(L/K), ∀ x : algebraicLocalIntegerRing L,
      IsLocalRing.residue _ (g • x) =
        (IsLocalRing.residue _ x) ^ Nat.card (IsLocalRing.ResidueField (algebraicLocalIntegerRing K)) := by
  let R := algebraicLocalIntegerRing K
  let S := algebraicLocalIntegerRing L
  let Q := IsLocalRing.maximalIdeal S
  let P := Q.under R
  letI : Q.IsMaximal := by dsimp [Q]; infer_instance
  letI : Field (S ⧸ Q) := Ideal.Quotient.field Q
  have hP : P = IsLocalRing.maximalIdeal R := algebraicLocalInteger_maximalIdeal_under K L
  letI : P.IsMaximal := by rw [hP]; infer_instance
  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  letI : Finite (R ⧸ P) := Finite.of_equiv (IsLocalRing.ResidueField R)
    (Ideal.quotEquivOfEq hP).toEquiv.symm
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  letI : SMulCommClass Gal(L/K) R S := algebraicLocalIntegerAction_smulComm K L
  letI : Algebra.IsInvariant R S Gal(L/K) := algebraicLocalIntegerAction_isInvariant K L
  letI : TopologicalSpace S := ⊥
  letI : DiscreteTopology S := ⟨rfl⟩
  letI : ContinuousSMul Gal(L/K) S := algebraicLocalIntegerAction_continuous K L
  letI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral_of_profinite (G := Gal(L/K))
  letI : Algebra.IsAlgebraic (R ⧸ P) (S ⧸ Q) := inferInstance
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic (R ⧸ P) (S ⧸ Q)
  obtain ⟨g, hg⟩ := algebraicLocal_residueAut_exists_lift K L σ
  refine ⟨g, fun x => ?_⟩
  rw [hg]
  have hcard : Fintype.card (R ⧸ P) = Nat.card (IsLocalRing.ResidueField R) := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Ideal.quotEquivOfEq hP).toEquiv
  change (IsLocalRing.residue S x) ^ Fintype.card (R ⧸ P) = _
  rw [hcard]

end
end Dubon2026
