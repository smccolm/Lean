import Dubon2026.SourceCurveDivisors
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-! DUB-17/18 -> residual modular Galois association -> the Tate module
of the original modular curve -> its genuine degree-zero divisor classes.
These are finite integer divisors on the existing normalized places,
quotiented by actual nonzero function divisors. The definitions follow
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_AlgebraicCurve_DivisorClassGroup. Existing local places,
orders and principal-divisor existence are reused; no torsion cardinality
or arithmetic realization is assumed or claimed here.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Divisor
variable {K F}

/-- Divisors with zero actual residue-weighted degree. -/
def degZero : AddSubgroup (Divisor K F) := degree.ker

/-- A literal normalized-order divisor of a nonzero function. -/
def IsPrincipal (D : Divisor K F) : Prop :=
  ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, D v = v.ord f

/-- The subgroup of genuine principal divisors. -/
def principal : AddSubgroup (Divisor K F) where
  carrier := {D | IsPrincipal D}
  zero_mem' := ⟨1, one_ne_zero, fun v => by simp [v.ord_one]⟩
  add_mem' := by
    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩
    exact ⟨f * g, mul_ne_zero hf hg, fun v => by
      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩
  neg_mem' := by
    rintro D ⟨f, hf, hD⟩
    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by
      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩

end Divisor

/-- Degree-zero divisors modulo actual principal divisors. -/
abbrev Pic0 := Divisor.degZero (K := K) (F := F) ⧸
  (Divisor.principal (K := K) (F := F)).addSubgroupOf Divisor.degZero

namespace Pic0
variable {K F}

/-- The canonical additive divisor-class map. -/
def mk : Divisor.degZero (K := K) (F := F) →+ Pic0 K F :=
  QuotientAddGroup.mk' _

theorem mk_surjective : Function.Surjective (mk (K := K) (F := F)) :=
  QuotientAddGroup.mk_surjective

theorem mk_eq_zero_iff (D : Divisor.degZero (K := K) (F := F)) :
    mk D = 0 ↔ Divisor.IsPrincipal D.val := by
  exact QuotientAddGroup.eq_zero_iff D

/-- The actual divisor classes annihilated by the given natural number. -/
def torsion (n : ℕ) : AddSubgroup (Pic0 K F) :=
  (Submodule.torsionBy ℤ (Pic0 K F) (n : ℤ)).toAddSubgroup

theorem mem_torsion_iff {n : ℕ} {x : Pic0 K F} :
    x ∈ torsion n ↔ n • x = 0 := by
  change (n : ℤ) • x = 0 ↔ n • x = 0
  rw [natCast_zsmul]

theorem mk_mem_torsion_iff (D : Divisor.degZero (K := K) (F := F)) (n : ℕ) :
    mk D ∈ torsion n ↔ Divisor.IsPrincipal (n • D.val) := by
  rw [mem_torsion_iff, ← map_nsmul, mk_eq_zero_iff]
  rfl

end Pic0
end
end Dubon2026.SourceCurve
