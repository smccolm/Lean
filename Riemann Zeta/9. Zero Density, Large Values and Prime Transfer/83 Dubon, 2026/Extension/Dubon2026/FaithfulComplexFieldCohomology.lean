import Dubon2026.FaithfulComplexFieldGaloisEquiv

/-! # Actual complex stabilizer unit H2

The exact original field-unit coefficient is compared with the pullback of
the original real/complex unit representation. Existing group reindexing
and the original order-two calculation give the actual stabilizer order.
This supplies the complex branch of DUB-17's archimedean local factors.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance] Units.mulDistribMulActionRight
variable (G F : Type) [Group G] [Field F] [MulSemiringAction G F]
  (e : F ≃+* ℂ) (hc : ∀ g : G, Continuous (fun z : ℂ => e (g • e.symm z)))

/-- The original complex-completion unit action is the pullback of the actual real/complex Galois coefficient. -/
def faithfulComplexUnitCoefficientIso :
    Rep.ofMulDistribMulAction G Fˣ ≅
      Rep.res (faithfulComplexActionHom G F e hc) (Rep.ofAlgebraAutOnUnits ℝ ℂ) := by
  apply Rep.mkIso
  refine Representation.Equiv.mk
    (Units.mapEquiv e.toMulEquiv).toAdditive.toIntLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro x
  apply Units.ext
  change e (g • (x.toMul : F)) = e (g • e.symm (e (x.toMul : F)))
  rw [e.symm_apply_apply]

variable [Finite G] [FaithfulSMul G F]

include e hc in
/-- Original complex-completion unit H2 is finite of precisely the original faithful stabilizer order. -/
theorem faithfulComplexField_second_cohomology_order :
    Finite (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) ∧
      Nat.card (groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2) = Nat.card G := by
  rcases subsingleton_or_nontrivial G with hs | hn
  · haveI := hs
    have hz := isZero_groupCohomology_succ_of_subsingleton
      (Rep.ofMulDistribMulAction G Fˣ) 1
    haveI := ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨Finite.of_subsingleton, (Nat.card_unique (α := groupCohomology
      (Rep.ofMulDistribMulAction G Fˣ) 2)).trans (Nat.card_unique (α := G)).symm⟩
  · haveI := hn
    let g := faithfulComplexActionEquiv G F e hc
    let c : groupCohomology (Rep.ofMulDistribMulAction G Fˣ) 2 ≅
        groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2 :=
      (groupCohomology.functor ℤ G 2).mapIso (faithfulComplexUnitCoefficientIso G F e hc) ≪≫
        (originalCohomologyReindex (Rep.ofAlgebraAutOnUnits ℝ ℂ) g 2).symm
    obtain ⟨hfin, hcard⟩ := originalRealComplex_second_cohomology_order
    haveI : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits ℝ ℂ) 2) := hfin
    refine ⟨Finite.of_equiv _ c.toLinearEquiv.symm.toEquiv, ?_⟩
    haveI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
    have hG : Nat.card G = 2 := (Nat.card_congr g.toEquiv).trans
      ((IsGalois.card_aut_eq_finrank ℝ ℂ).trans Complex.finrank_real_complex)
    exact (Nat.card_congr c.toLinearEquiv.toEquiv).trans (hcard.trans hG.symm)

end
end Dubon2026
