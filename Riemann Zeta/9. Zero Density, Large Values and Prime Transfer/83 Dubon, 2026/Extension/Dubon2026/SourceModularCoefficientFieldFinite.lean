import Dubon2026.SourceModularRelationsInResidueCharacteristic
import Dubon2026.SourceOriginalFieldFinite

/-! DUB-17/18 -> original Frobenius/inertia -> curve reduction ->
finite function-field extension in residue characteristic. The existing
integral monic relations specialize to the actual divisor generators.
Finite divisor generation then proves finiteness over the literal j
coordinate. Exact degree, good reduction and genus preservation remain
separate obligations. Adapted from the already proved local
SourceOriginalFieldFinite argument, using the same source generators. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField Polynomial

theorem finiteDimensional_coeff_field (N : ℕ) [NeZero N] (K : Type*) [Field K] :
    FiniteDimensional (IntermediateField.adjoin K ({jCoeff N K} :
      Set (modularFunctionFieldCoeff N K))) (modularFunctionFieldCoeff N K) := by
  classical
  let F := modularFunctionFieldCoeff N K
  let J : F := jCoeff N K
  letI : Algebra K F := inferInstance
  letI : Algebra K (IntermediateField.adjoin K ({J} : Set F)) := inferInstance
  let ι : Type := {d : ℕ // d ∣ N ∧ d ≠ 0}
  letI : Finite ι := by
    refine Finite.of_injective (fun d : ι => (⟨d.1, ?_⟩ : Fin (N + 1))) ?_
    · exact Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) d.2.1)
    · intro d d' h
      exact Subtype.ext (by simpa using congrArg Fin.val h)
  let g : ι → F := fun d =>
    haveI : NeZero d.1 := ⟨d.2.2⟩
    ⟨qExpand K d.1 (jqModC K), jqd_mem_coeff_field N K d.2.1⟩
  have hint : ∀ d : ι, IsIntegral (IntermediateField.adjoin K ({J} : Set F)) (g d) := by
    rintro ⟨d, hdvd, hd0⟩
    letI : NeZero d := ⟨hd0⟩
    obtain ⟨P, hPm, hP0⟩ := exists_monic_relation_coeff d K
    let J' : IntermediateField.adjoin K ({J} : Set F) :=
      ⟨J, IntermediateField.mem_adjoin_simple_self K J⟩
    let ψ : Polynomial ℤ →+* IntermediateField.adjoin K ({J} : Set F) :=
      Polynomial.eval₂RingHom (Int.castRingHom _) J'
    refine ⟨P.map ψ, hPm.map ψ, ?_⟩
    apply (algebraMap F (LaurentSeries K)).injective
    have hcomp : ((algebraMap F (LaurentSeries K)).comp
        (algebraMap (IntermediateField.adjoin K ({J} : Set F)) F)).comp ψ =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) (jqModC K) := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      change (algebraMap F (LaurentSeries K)) ((algebraMap _ F)
        (Polynomial.eval₂ (Int.castRingHom _) J' X)) =
        Polynomial.eval₂ (Int.castRingHom _) (jqModC K) X
      rw [Polynomial.eval₂_X, Polynomial.eval₂_X]
      rfl
    rw [map_zero, Polynomial.hom_eval₂, Polynomial.eval₂_map, hcomp]
    change Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _)
      (jqModC K)) (qExpand K d (jqModC K)) P = 0
    simpa only [relationAtSeed, Polynomial.eval_map] using hP0
  have hgen : IntermediateField.adjoin (IntermediateField.adjoin K ({J} : Set F))
      (Set.range g) = ⊤ := by
    apply IntermediateField.restrictScalars_injective K
    rw [IntermediateField.restrictScalars_top, IntermediateField.adjoin_adjoin_left]
    apply IntermediateField.lift_injective
    erw [IntermediateField.lift_adjoin, IntermediateField.lift_top]
    apply le_antisymm
    · rw [adjoin_le_iff]
      rintro _ ⟨y, _, rfl⟩
      exact y.property
    · change IntermediateField.adjoin K (divisorExpansionsCoeff N K) ≤ _
      rw [adjoin_le_iff]
      rintro _ ⟨d, hd0, hdvd, rfl⟩
      apply IntermediateField.subset_adjoin
      exact ⟨g ⟨d, hdvd, hd0.ne⟩, Or.inr ⟨⟨d, hdvd, hd0.ne⟩, rfl⟩, rfl⟩
  have hfin : FiniteDimensional (IntermediateField.adjoin K ({J} : Set F))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({J} : Set F)) (Set.range g)) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨d, rfl⟩ := hy
      exact hint d
  rw [hgen] at hfin
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv : (⊤ : IntermediateField
      (IntermediateField.adjoin K ({J} : Set F)) F) ≃ₐ[_] F).toLinearEquiv

end
end Dubon2026.SourceFunctionField
