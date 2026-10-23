import Dubon2026.SourceResidueConjugateRootBounds
import Dubon2026.SourceUniqueCommonRootDescent

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> joint generation/degree induction. Adapt local SourceOriginalPredecessorGeneration
to the actual coefficient-field divisor field. Lower-level conjugate products
force a unique common root of the prime relation and minimal polynomial;
native descent recovers the preceding j series. Proper-divisor induction
inputs remain explicit; the current-level degree is not assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
open scoped IntermediateField
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem residue_predecessor_mem_pair_of_lower_product (M p : ℕ)
    [NeZero M] [hp : Fact p.Prime] (hpK : (p : K) ≠ 0) (η : Kˣ)
    (hlower : residueExpandedJMinpoly K M M = slotProduct M η) :
    qExpand K M (jqModC K) ∈ IntermediateField.adjoin K
      ({(jqModC K), qExpand K (M * p) (jqModC K)} : Set (LaurentSeries K)) := by
  haveI : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  let ζ := hz.isUnit (NeZero.ne p) |>.unit
  have hζ : IsPrimitiveRoot (ζ : K) p := by
    simpa only [ζ, IsUnit.unit_spec] using hz
  obtain ⟨P, hPm, _, _, hP⟩ := exists_residue_prime_compatible_relations K p ζ hζ
  let F := IntermediateField.adjoin K
    ({(jqModC K), qExpand K (M * p) (jqModC K)} : Set (LaurentSeries K))
  have hj : (jqModC K) ∈ F := IntermediateField.subset_adjoin K _ (Or.inl rfl)
  have hjN : qExpand K (M * p) (jqModC K) ∈ F :=
    IntermediateField.subset_adjoin K _ (Or.inr rfl)
  have hBF : K⟮(jqModC K)⟯ ≤ F :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hj)
  let ι : K⟮(jqModC K)⟯ →+* F := Subfield.inclusion
    (show (K⟮(jqModC K)⟯).toSubfield ≤ F.toSubfield from hBF)
  let φ : F →+* LaurentSeries K :=
    ((qExpand K (M * p))).comp (algebraMap F (LaurentSeries K))
  letI : Algebra F (LaurentSeries K) := φ.toAlgebra
  have halg : algebraMap F (LaurentSeries K) = φ := rfl
  let A := relationAtSeed P (⟨qExpand K (M * p) (jqModC K), hjN⟩ : F)
  let B := (minpoly K⟮(jqModC K)⟯ (qExpand K M (jqModC K))).map ι
  let e := M * p * M
  have hmapA : A.map φ = relationAtSeed P (TS K (e * p) 1) := by
    dsimp only [A]
    rw [relationAtSeed_map]
    congr 1
    change (qExpand K (M * p) (qExpand K (M * p) (jqModC K))) = _
    rw [qExpand_qExpand, TS, qTwist_one_apply]
    exact qExpand_congr (by dsimp [e]; ring) (jqModC K)
  have hmapB : B.map φ = residueExpandedJMinpoly K (M * p) M := by
    dsimp only [B]
    rw [Polynomial.map_map, residueExpandedJMinpoly]
    congr 1
  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      y = TS K (e * (p * p)) 1 ∨ ∃ c < p, y = TS K e (ζ ^ c) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapA]
    simpa only [one_pow, one_mul] using residue_prime_root_iff_of_root_list p e ζ 1 P hPm (hP e 1).1 y
  have hBev : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      (residueExpandedJMinpoly K (M * p) M).IsRoot y := by
    intro y hy
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB] at hy
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP e 1).2.1
  have hAn : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [halg, hmapA]
    simpa only [one_pow] using (hP e 1).2.2
  have hxA : Polynomial.aeval (TS K e 1) A = 0 :=
    (hrootA _).mpr (Or.inr ⟨0, hp.out.pos, by rw [pow_zero]⟩)
  have hxB : Polynomial.aeval (TS K e 1) B = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, halg, hmapB]
    exact residueExpandedJMinpoly_distinguished_root K (M * p) M
  have hu : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = TS K e 1 := by
    intro y hyA hyB
    have hy := hBev y hyB
    rcases (hrootA y).mp hyA with hbig | ⟨c, _, hc⟩
    · exfalso
      apply residue_lower_root_ne_larger_branch M p η hlower y hy
      exact hbig.trans (TS_congr (by dsimp [e]; ring) 1)
    · have hw := residue_lower_root_top_twist_eq_one M p η hlower y hy (ζ ^ c) hc
      simpa only [hw] using hc
  obtain ⟨f, hf⟩ := mem_range_of_unique_common_root_monic A B (hPm.map _)
    hAs hAn (TS K e 1) hxA hxB hu
  have hx : (qExpand K (M * p) (qExpand K M (jqModC K))) = TS K e 1 := by
    simp only [TS, qTwist_one_apply, qExpand_qExpand, e]
  have he : (f : LaurentSeries K) = qExpand K M (jqModC K) :=
    (((qExpand K (M * p))).injective (hf.trans hx.symm))
  rw [← he]
  exact f.2

end
end Dubon2026.SourceFunctionField
