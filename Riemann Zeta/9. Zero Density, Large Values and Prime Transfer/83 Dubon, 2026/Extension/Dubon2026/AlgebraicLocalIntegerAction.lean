import Dubon2026.CompleteNonarchimedeanGaloisNorm
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite

/-! Original local algebraic integers and their Galois action. This is the
arithmetic entry to DUB-17's unramified local H1 cyclicity/depth conditions.
Native complete-base norm uniqueness replaces the reviewed external
p-adic closure-specific action. The underlying original field and Krull
Galois group are retained; no alternative cohomology object is introduced. -/

namespace Dubon2026
noncomputable section

/-- The actual valuation integer ring for the given nonarchimedean norm. -/
abbrev algebraicLocalIntegerRing (L : Type) [NormedField L] [IsUltrametricDist L] :=
  (NormedField.valuation (K := L)).valuationSubring

variable (K L : Type) [NontriviallyNormedField K] [NormedField L]
  [NormedAlgebra K L] [IsUltrametricDist K] [IsUltrametricDist L] [CompleteSpace K]
  [Algebra.IsAlgebraic K L]

/-- Original norm invariance restricts every original field automorphism
to the same valuation integer ring. -/
@[implicit_reducible]
def algebraicLocalIntegerAction : MulSemiringAction Gal(L/K) (algebraicLocalIntegerRing L) where
  smul g x := ⟨g x.val, by
    change ‖g x.val‖₊ ≤ 1
    rw [← NNReal.coe_le_coe]
    change ‖g x.val‖ ≤ 1
    rw [completeNonarchimedeanGalois_norm_map]
    exact_mod_cast x.property⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero g := Subtype.ext (map_zero g)
  smul_add g x y := Subtype.ext (map_add g x.val y.val)
  smul_one g := Subtype.ext (map_one g)
  smul_mul g x y := Subtype.ext (map_mul g x.val y.val)

attribute [local instance] algebraicLocalIntegerAction

/-- The integer action is the restriction of the original field action. -/
theorem algebraicLocalIntegerAction_coe (g : Gal(L/K)) (x : algebraicLocalIntegerRing L) :
    ((g • x : algebraicLocalIntegerRing L) : L) = g x.val := rfl

/-- The original base inclusion restricts to the actual valuation rings. -/
def algebraicLocalIntegerBaseMap : algebraicLocalIntegerRing K →+* algebraicLocalIntegerRing L :=
  ((algebraMap K L).comp (NormedField.valuation (K := K)).valuationSubring.subtype).codRestrict
    (NormedField.valuation (K := L)).valuationSubring (fun x => by
      change ‖algebraMap K L x.val‖₊ ≤ 1
      rw [nnnorm_algebraMap, nnnorm_one, mul_one]
      exact x.property)

/-- The base-ring structure is induced by the original field inclusion. -/
@[implicit_reducible]
def algebraicLocalIntegerBaseAlgebra :
    Algebra (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L) :=
  (algebraicLocalIntegerBaseMap K L).toAlgebra

attribute [local instance] algebraicLocalIntegerBaseAlgebra

omit [CompleteSpace K] [Algebra.IsAlgebraic K L] in
/-- The original extended norm identifies the prime below the local
maximal ideal with the original base maximal ideal. -/
theorem algebraicLocalInteger_maximalIdeal_under :
    (IsLocalRing.maximalIdeal (algebraicLocalIntegerRing L)).under (algebraicLocalIntegerRing K) =
      IsLocalRing.maximalIdeal (algebraicLocalIntegerRing K) := by
  ext x
  change algebraicLocalIntegerBaseMap K L x ∈
    IsLocalRing.maximalIdeal (algebraicLocalIntegerRing L) ↔ _
  rw [Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
  change ‖algebraMap K L x.val‖₊ < 1 ↔ ‖x.val‖₊ < 1
  rw [nnnorm_algebraMap']

/-- Original Galois automorphisms commute with the original integer scalars. -/
theorem algebraicLocalIntegerAction_smulComm :
    SMulCommClass Gal(L/K) (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L) := by
  constructor
  intro g r x
  apply Subtype.ext
  change g (algebraMap K L r.val * x.val) = algebraMap K L r.val * g x.val
  rw [map_mul, AlgEquiv.commutes]

/-- A fixed algebraic integer is the same original base integer: field
Galois invariance and equality of the extended norms supply both parts. -/
theorem algebraicLocalIntegerAction_isInvariant [IsGalois K L] :
    Algebra.IsInvariant (algebraicLocalIntegerRing K) (algebraicLocalIntegerRing L) Gal(L/K) := by
  constructor
  intro x hx
  obtain ⟨r, hr⟩ := Algebra.IsInvariant.isInvariant (A := K) (G := Gal(L/K)) x.val
    (fun g => congrArg Subtype.val (hx g))
  have hnorm : ‖r‖₊ ≤ 1 := by
    have he : ‖algebraMap K L r‖₊ = ‖r‖₊ := by
      rw [nnnorm_algebraMap, nnnorm_one, mul_one]
    rw [← he, hr]
    exact x.property
  exact ⟨⟨r, hnorm⟩, Subtype.ext hr⟩

/-- The original Krull action on discrete valuation integers is continuous,
using the pinned open stabilizer theorem for the same algebraic element. -/
theorem algebraicLocalIntegerAction_continuous
    [TopologicalSpace (algebraicLocalIntegerRing L)] [DiscreteTopology (algebraicLocalIntegerRing L)] :
    ContinuousSMul Gal(L/K) (algebraicLocalIntegerRing L) := by
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro x
  have h := stabilizer_isOpen_of_isIntegral (K := K) x.val
  convert h using 1
  ext g
  change (g • x = x) ↔ g x.val = x.val
  exact Subtype.ext_iff

end
end Dubon2026
