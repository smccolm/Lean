import Dubon2026.SourceOriginalFieldGeneration

/-! DUB-17/18 -> original cusp-form lower dimension bound -> regular
differential realization -> injectivity of the actual differential expansion
-> separability over the actual j coordinate. The conditional consumer here uses
monic relations for divisor j series and derives finite extension.
SourceAllDivisorMonicRelations proves those relations and
SourceOriginalDifferentialInjectivity assembles the original-field result. Exact polynomial degree and irreducibility
are unnecessary for this finite-extension step.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField Polynomial

/-- Evaluation of the original integral polynomial coordinate at the literal j series. -/
def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom

@[simp] theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]

theorem finiteDimensional_original_of_monic_relations (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (hrelations : ∀ (d : ℕ) [NeZero d], d ∣ N →
      ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
        P.eval₂ evalAtJ (qExpand ℚ d jq) = 0) :
    FiniteDimensional
      (IntermediateField.adjoin L
        ({⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩} :
          Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (laurentBaseChange L (modularFunctionFieldFull N)) := by
  classical

  let ι : Type := {d : ℕ // d ∣ N ∧ d ≠ 0}
  haveI : Finite ι := by
    refine Finite.of_injective (fun d : ι => (⟨d.1, ?_⟩ : Fin (N + 1))) ?_
    · exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) d.2.1)
    · intro d d' h
      exact Subtype.ext (by simpa using congrArg Fin.val h)

  let g : ι → laurentBaseChange L (modularFunctionFieldFull N) := fun d =>
    haveI : NeZero d.1 := ⟨d.2.2⟩
    ⟨coeffEmb L (qExpand ℚ d.1 jq), coeffEmb_mem_laurentBaseChange L (jqd_mem_full N d.2.1)⟩

  let J : laurentBaseChange L (modularFunctionFieldFull N) :=
    ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩

  letI : Algebra L (laurentBaseChange L (modularFunctionFieldFull N)) := inferInstance
  letI : Algebra L
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N)))) :=
    inferInstance

  have hint : ∀ d : ι, IsIntegral
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N)))) (g d) := by
    rintro ⟨d, hdvd, hd0⟩
    haveI : NeZero d := ⟨hd0⟩
    obtain ⟨P, hPm, hP0⟩ := hrelations d hdvd
    let J' : IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))) :=
      ⟨J, IntermediateField.mem_adjoin_simple_self L J⟩
    let ψ : Polynomial ℤ →+*
        IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))) :=
      Polynomial.eval₂RingHom (Int.castRingHom _) J'
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    have hv : Function.Injective
        (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)) :=
      (algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)).injective
    apply hv
    have hcomp : ((algebraMap (laurentBaseChange L (modularFunctionFieldFull N)) (LaurentSeries L)).comp
        (algebraMap (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
          (laurentBaseChange L (modularFunctionFieldFull N)))).comp ψ =
        (coeffEmb L).comp evalAtJ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, evalAtJ_X]
      show (algebraMap _ (LaurentSeries L)) (algebraMap _ _ (Polynomial.eval₂ (Int.castRingHom _) J' X)) =
        coeffEmb L jq
      rw [Polynomial.eval₂_X]
      rfl
    rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
    show Polynomial.eval₂ ((coeffEmb L).comp evalAtJ) (coeffEmb L (qExpand ℚ d jq)) P = 0
    rw [← Polynomial.hom_eval₂]
    have h0 : Polynomial.eval₂ evalAtJ (qExpand ℚ d jq) P = 0 := hP0
    rw [h0, map_zero]

  have hgen : IntermediateField.adjoin
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (Set.range g) = ⊤ := by
    apply IntermediateField.restrictScalars_injective L
    rw [IntermediateField.restrictScalars_top, IntermediateField.adjoin_adjoin_left]
    apply IntermediateField.lift_injective
    erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro _ ⟨y, _, rfl⟩
      exact y.2
    · conv_lhs => rw [laurentBaseChange_full_eq_adjoin]
      rw [adjoin_le_iff]
      rintro _ ⟨x, ⟨d, hd0, hdvd, rfl⟩, rfl⟩
      apply IntermediateField.subset_adjoin
      refine ⟨g ⟨d, hdvd, hd0.ne⟩, Or.inr ⟨⟨d, hdvd, hd0.ne⟩, rfl⟩, ?_⟩
      rfl

  have hfin : FiniteDimensional
      (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
      (IntermediateField.adjoin
        (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
        (Set.range g)) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨d, rfl⟩ := hy
      exact hint d
  rw [hgen] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv :
      (⊤ : IntermediateField
        (IntermediateField.adjoin L ({J} : Set (laurentBaseChange L (modularFunctionFieldFull N))))
        (laurentBaseChange L (modularFunctionFieldFull N))) ≃ₐ[_]
        laurentBaseChange L (modularFunctionFieldFull N)).toLinearEquiv

end
end Dubon2026.SourceFunctionField
