import Dubon2026.SourceCurveAdeleCore
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! DUB-17/18 -> the original function-field Riemann--Roch theorem ->
global index and residue duality. The index is the dimension of the actual
repartition quotient, and its dual is the annihilator used in residue
pairing. No finiteness of the global index or duality with canonical
divisor spaces is assumed here. Adapted from the selected definitions and
quotient-dual proofs of Def_AlgebraicCurve_AdelicIndex,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The dimension of repartitions modulo the divisor bound and global functions. -/
def indexOfSpecialty (D : Divisor K F) : ℕ :=
  Module.finrank K
    ((adeleSpace K F) ⧸
      ((adeleBdd D).comap (adeleSpace K F).subtype ⊔
        (globalSub K F).comap (adeleSpace K F).subtype))

theorem adeleBdd_directed :
    Directed (· ≤ ·) (adeleBdd (K := K) (F := F)) := fun D E =>
  ⟨D ⊔ E, adeleBdd_mono le_sup_left, adeleBdd_mono le_sup_right⟩

theorem mem_adeleSpace_iff {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ ∃ D : Divisor K F, α ∈ adeleBdd D := by
  unfold adeleSpace
  exact Submodule.mem_iSup_of_directed _ adeleBdd_directed

variable (K F) in

/-- The sum of bounded and global repartitions inside the actual repartition space. -/
abbrev adeleBddPrincipal (D : Divisor K F) : Submodule K (adeleSpace K F) :=
  (adeleBdd D).comap (adeleSpace K F).subtype ⊔
    (globalSub K F).comap (adeleSpace K F).subtype

theorem indexOfSpecialty_eq (D : Divisor K F) :
    indexOfSpecialty D = Module.finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) := rfl

/-- Linear functionals annihilating the bounded and global repartitions. -/
def omegaSpace (D : Divisor K F) : Submodule K (Module.Dual K (adeleSpace K F)) :=
  (adeleBddPrincipal K F D).dualAnnihilator

theorem omegaSpace_vanishBdd {D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace D) {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ adeleBdd D) :
    φ α = 0 :=
  (Submodule.mem_dualAnnihilator φ).mp hφ α (Submodule.mem_sup_left hα)

theorem omegaSpace_vanishGlobal {D : Divisor K F} {φ : Module.Dual K (adeleSpace K F)}
    (hφ : φ ∈ omegaSpace D) {α : adeleSpace K F} (hα : (α : Place K F → F) ∈ globalSub K F) :
    φ α = 0 :=
  (Submodule.mem_dualAnnihilator φ).mp hφ α (Submodule.mem_sup_right hα)

theorem omegaSpace_antitone {D E : Divisor K F} (hDE : D ≤ E) :
    omegaSpace E ≤ omegaSpace D :=
  Submodule.dualAnnihilator_anti
    (sup_le_sup_right (Submodule.comap_mono (adeleBdd_mono hDE)) _)

/-- The annihilator identified with the dual of the actual quotient. -/
def omegaSpaceEquivIndexDual (D : Divisor K F) :
    omegaSpace D ≃ₗ[K] Module.Dual K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=
  (Submodule.dualQuotEquivDualAnnihilator (adeleBddPrincipal K F D)).symm

theorem finrank_omegaSpace_eq_indexOfSpecialty (D : Divisor K F) :
    Module.finrank K (omegaSpace D) = indexOfSpecialty D := by
  rw [indexOfSpecialty_eq, (omegaSpaceEquivIndexDual D).finrank_eq,
    Subspace.dual_finrank_eq]


end
end Dubon2026.SourceCurve
