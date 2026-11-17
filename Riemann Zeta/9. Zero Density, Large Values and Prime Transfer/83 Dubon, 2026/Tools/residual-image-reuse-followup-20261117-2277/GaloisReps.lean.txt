import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.NumberTheory.NumberField.Basic

variable (k : Type _) [CommRing k] [TopologicalSpace k] [TopologicalRing k]

/-- `galois_rep k` is the type of 2-dimensional Galois representations where `k` is a
topological ring defined as the continuous monoid homomorphism of the absolute Galois group
of the rationals to the `GL_2 k`-/
def GaloisRep :=
  ContinuousMonoidHom (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (GL (Fin 2) k)

open ValuationSubring

variable {k}

/-- `is_unramified ρ q` if the inertia subgroup is contained in its kernel -/
noncomputable def IsUnramified (ρ : GaloisRep k) (q : ValuationSubring (AlgebraicClosure ℚ)) :
    Prop :=
  inertiaSubgroup ℚ q ≤ ρ.toMonoidHom.ker.subgroupOf (decompositionSubgroup ℚ q)
