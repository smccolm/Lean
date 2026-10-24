import Dubon2026.SourceReductionSingleChartMonic
import Dubon2026.SourceCurvePlaces

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> place comparison.
Integral chart functions have integral values at an original place centered
over an integral coordinate value; zero Gauss residue forces that value into
the coefficient maximal ideal. These are the properness inputs for the
actual reduction-place construction, not a supplied place-map certificate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_existsUnique_place_forall_residue_sub_mem_nonunits.
The existing local minimal-polynomial integrality theorem replaces the
external valuation-extension and monic-equation development. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem mem_of_sub_algebraMap_mem_nonunits (P : Place L F) {h : F} {b : L}
    (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : h ∈ P.toValuationSubring := by
  have := add_mem (ValuationSubring.nonunits_subset hb) (P.algebraMap_mem' b)
  simpa using this

theorem mem_of_sub_mem_nonunits (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits)
    {h : F} (hhO : h ∈ R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h)
    {b : L} (hb : h - algebraMap L F b ∈ P.toValuationSubring.nonunits) : b ∈ A := by
  obtain ⟨p, hpm, hp⟩ := exists_monic_equation_of_integral_chart R x hx hfin hdeg ⟨h, hhO⟩ hh
  set OP := P.toValuationSubring with hOP
  have hxP : (x : F) ∈ OP := mem_of_sub_algebraMap_mem_nonunits P ha₀
  have hhP : h ∈ OP := mem_of_sub_algebraMap_mem_nonunits P hb

  set ψ : A[X] →+* OP := eval₂RingHom ((algebraMap L OP).comp A.subtype) ⟨x, hxP⟩ with hψ
  have hψF : (algebraMap OP F).comp ψ = eval₂RingHom ((algebraMap L F).comp A.subtype) (x : F) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
      rfl
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]
      rfl
  have hp' : p.eval₂ ψ ⟨h, hhP⟩ = 0 := by
    apply IsFractionRing.injective OP F
    rw [Polynomial.hom_eval₂, hψF, map_zero]
    exact hp

  have hπx : IsLocalRing.residue OP ⟨x, hxP⟩ = algebraMap L (ResidueField OP) (a₀ : L) := by
    have hm : (⟨x, hxP⟩ : OP) - algebraMap L OP (a₀ : L) ∈ maximalIdeal OP := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact ha₀
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    rw [hm]
    exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
  have hπh : IsLocalRing.residue OP ⟨h, hhP⟩ = algebraMap L (ResidueField OP) b := by
    have hm : (⟨h, hhP⟩ : OP) - algebraMap L OP b ∈ maximalIdeal OP := by
      rw [← ValuationSubring.coe_mem_nonunits_iff]; exact hb
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero] at hm
    rw [hm]
    exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
  have hcomp : (IsLocalRing.residue OP).comp ψ =
      ((algebraMap L (ResidueField OP)).comp A.subtype).comp (evalRingHom a₀) := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, coe_evalRingHom, eval_C]
      exact (IsScalarTower.algebraMap_apply L OP (ResidueField OP) _).symm
    · simp only [hψ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, coe_evalRingHom, eval_X]
      exact hπx
  have h2 := congrArg (IsLocalRing.residue OP) hp'
  rw [Polynomial.hom_eval₂, map_zero, hπh, hcomp, ← eval₂_map, ← Polynomial.hom_eval₂,
    map_eq_zero] at h2

  have hint : IsIntegral A b := by
    refine ⟨p.map (evalRingHom a₀), hpm.map _, ?_⟩
    rw [show algebraMap A L = A.subtype from RingHom.ext fun _ => rfl]
    exact h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← ha]
  exact a.2


end
end Dubon2026.SourceCurve.RegularProlongation
