import Dubon2026.SourceEllipticTorsionReductionCoordinates

/-! Lift the actual finite cyclic generator family through torsion reduction.
Exact orders and distinct cyclic subgroups are derived for the lifted points,
so the characteristic-zero quotient product applies to the same family. -/

namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L] {A : ValuationSubring L}
variable [DecidableEq (ResidueField A)] {W : WeierstrassCurve A}

/-- Equality of the actual cyclic kernels is preserved by torsion reduction. -/
theorem zmultiples_reducePoint_eq (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) (P Q : (W.map A.subtype).toAffine.Point)
    (hP : N • P = 0) (hQ : N • Q = 0)
    (h : AddSubgroup.zmultiples P = AddSubgroup.zmultiples Q) :
    AddSubgroup.zmultiples (reducePoint hΔ P) = AddSubgroup.zmultiples (reducePoint hΔ Q) := by
  let S := Submodule.torsionBy ℤ (W.map A.subtype).toAffine.Point (N : ℤ)
  let P' : S := ⟨P, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hP⟩
  let Q' : S := ⟨Q, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using hQ⟩
  have hs : AddSubgroup.zmultiples P' = AddSubgroup.zmultiples Q' := by
    apply AddSubgroup.map_injective (f := S.subtype.toAddMonoidHom) Subtype.val_injective
    simpa only [AddMonoidHom.map_zmultiples] using h
  have hr := congrArg (AddSubgroup.map (torsionReductionHom hΔ hN)) hs
  simpa only [AddMonoidHom.map_zmultiples] using hr

/-- Every actual reduced family of distinct cyclic kernels lifts with the same exact orders. -/
theorem exists_cyclic_generator_lifts [IsAlgClosed L] (hΔ : (W.map (residue A)).Δ ≠ 0)
    {N : ℕ} (hN : IsUnit (N : A)) {ι : Type*}
    (Q : ι → (W.map (residue A)).toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = N)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    ∃ R : ι → (W.map A.subtype).toAffine.Point,
      (∀ i, addOrderOf (R i) = N) ∧ (∀ i, reducePoint hΔ (R i) = Q i) ∧
        Function.Injective (fun i => AddSubgroup.zmultiples (R i)) := by
  have hlift (i : ι) : ∃ R : (W.map A.subtype).toAffine.Point,
      N • R = 0 ∧ reducePoint hΔ R = Q i := by
    let P : Submodule.torsionBy ℤ (W.map (residue A)).toAffine.Point (N : ℤ) :=
      ⟨Q i, by
        rw [Submodule.mem_torsionBy_iff, natCast_zsmul, ← hQ i]
        exact addOrderOf_nsmul_eq_zero _⟩
    obtain ⟨R, hR⟩ := (torsionReductionEquiv hΔ hN).surjective P
    exact ⟨R, by simpa only [Submodule.mem_torsionBy_iff, natCast_zsmul] using R.property,
      congrArg Subtype.val hR⟩
  choose R hkill hred using hlift
  refine ⟨R, ?_, hred, ?_⟩
  · intro i
    rw [← addOrderOf_reducePoint hΔ hN (R i) (hkill i), hred, hQ]
  · intro i j hij
    apply hinj
    have he := zmultiples_reducePoint_eq hΔ hN (R i) (R j) (hkill i) (hkill j) hij
    simpa only [hred] using he

end
end Dubon2026.SourceEllipticReduction
