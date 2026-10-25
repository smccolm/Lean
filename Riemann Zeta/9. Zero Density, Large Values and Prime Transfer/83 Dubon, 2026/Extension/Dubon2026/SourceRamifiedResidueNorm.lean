import Dubon2026.SourceResidueAlgebraNormPi
import Mathlib.NumberTheory.RamificationInertia.Basic

/-! DUB-17/18 -> Frobenius determinant -> Weil reciprocity and Hecke
adjointness -> norm evaluation on a place fiber. Reuse Mathlib's ramified
Chinese remainder equivalence and factor dimensions. These two calculations
are precisely the finite-algebra steps needed by the existing integral closure. -/
namespace Dubon2026
noncomputable section
open UniqueFactorizationMonoid
open scoped Classical
attribute [local instance] Ideal.Quotient.field
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDedekindDomain S] [Module.Finite R S]

theorem norm_residue_quotient_eq_prod (p : Ideal R) [p.IsMaximal]
    (hp : p.map (algebraMap R S) ≠ ⊥) (c : S) :
    Algebra.norm (R ⧸ p) (Ideal.Quotient.mk (p.map (algebraMap R S)) c) =
      ∏ P : (factors (p.map (algebraMap R S))).toFinset,
        Algebra.norm (R ⧸ p) (Ideal.Quotient.mk (P.val ^ p.ramificationIdx P.val) c) := by
  let ee : (S ⧸ p.map (algebraMap R S)) ≃ₐ[R ⧸ p]
      (∀ P : (factors (p.map (algebraMap R S))).toFinset,
        S ⧸ P.val ^ p.ramificationIdx P.val) :=
    { Ideal.Factors.piQuotientEquiv p hp with
      commutes' r := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        rfl }
  rw [← Algebra.norm_eq_of_algEquiv ee (Ideal.Quotient.mk _ c), algebra_norm_finite_pi]
  rfl

theorem norm_ramified_factor_eq_residue_pow (p : Ideal R) [p.IsMaximal]
    (P : (factors (p.map (algebraMap R S))).toFinset) (c : S) (r : R)
    (hr : c - algebraMap R S r ∈ P.val) :
    Algebra.norm (R ⧸ p) (Ideal.Quotient.mk (P.val ^ p.ramificationIdx P.val) c) =
      Ideal.Quotient.mk p r ^ (p.ramificationIdx P.val * p.inertiaDeg P.val) := by
  have hn : IsNilpotent (Ideal.Quotient.mk (P.val ^ p.ramificationIdx P.val) c -
      algebraMap (R ⧸ p) (S ⧸ P.val ^ p.ramificationIdx P.val) (Ideal.Quotient.mk p r)) := by
    refine ⟨p.ramificationIdx P.val, ?_⟩
    rw [Ideal.Quotient.algebraMap_quotient_pow_ramificationIdx, ← map_sub, ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hr _)
  rw [algebra_norm_nilpotent_scalar hn, Ideal.Factors.finrank_pow_ramificationIdx]

end
end Dubon2026
