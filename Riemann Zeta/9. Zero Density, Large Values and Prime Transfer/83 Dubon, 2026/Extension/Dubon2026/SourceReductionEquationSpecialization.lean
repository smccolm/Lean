import Dubon2026.SourceReductionMonicOrder

/-! DUB-17/18 -> original Frobenius/inertia -> actual good reduction ->
genus comparison -> preservation of pole spaces. A literal monic equation with
coefficient degree bounds forces the same pole-order bound after reduction.
Existing actual-place order criteria and the constructed constant reduction
are reused; no genus or place-map conclusion is assumed. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial

section Reduction

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem subtype_comp_constHom (R : RegularProlongation A F Fbar) :
    R.integers.subtype.comp (constHom R) = (algebraMap L F).comp A.subtype := by
  ext a; rfl

/-- Reduction of constants followed by inclusion into the residue function field. -/
def resConst (A : ValuationSubring L) (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar] :
    A →+* Fbar :=
  (algebraMap (ResidueField A) Fbar).comp (IsLocalRing.residue A)

theorem residue_comp_constHom (R : RegularProlongation A F Fbar) :
    R.residue.comp (constHom R) = resConst A Fbar := by
  ext a; exact residue_constHom R a

theorem resConst_mem (w : Place (ResidueField A) Fbar) (a : A) :
    resConst A Fbar a ∈ w.toValuationSubring :=
  w.algebraMap_mem' _

theorem eval₂_residue_eq_zero (R : RegularProlongation A F Fbar) (f h : R.integers)
    (p : Polynomial (Polynomial A))
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0) :
    p.eval₂ (eval₂RingHom (resConst A Fbar) (R.residue f)) (R.residue h) = 0 := by

  set ψ : Polynomial A →+* R.integers := eval₂RingHom (constHom R) f with hψ
  have hcoeψ : R.integers.subtype.comp ψ =
      eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ]
    · simp [hψ]
  have hO : p.eval₂ ψ h = 0 := by
    apply R.integers.subtype_injective

    have := Polynomial.hom_eval₂ p ψ R.integers.subtype h
    rw [map_zero, this, hcoeψ]
    exact hroot

  have hres := congrArg R.residue hO
  rw [map_zero, Polynomial.hom_eval₂] at hres
  have hcomp : R.residue.comp ψ = eval₂RingHom (resConst A Fbar) (R.residue f) := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · simp [hψ, residue_constHom, resConst]
    · simp [hψ]
  rw [hcomp] at hres
  exact hres

theorem mul_min_ord_residue_le (R : RegularProlongation A F Fbar) (f h : R.integers) (m : ℕ)
    (p : Polynomial (Polynomial A)) (hp : p.Monic)
    (hdeg : ∀ j, (p.coeff j).natDegree ≤ (p.natDegree - j) * m)
    (hroot : p.eval₂ (eval₂RingHom ((algebraMap L F).comp A.subtype) (f : F)) (h : F) = 0)
    (w : Place (ResidueField A) Fbar) :
    (m : ℤ) * min 0 (w.ord (R.residue f)) ≤ w.ord (R.residue h) :=
  mul_min_ord_le_ord (resConst A Fbar) (resConst_mem) (R.residue f) (R.residue h) m p hp hdeg
    (eval₂_residue_eq_zero R f h p hroot) w


end Reduction
end
end Dubon2026.SourceCurve.RegularProlongation
