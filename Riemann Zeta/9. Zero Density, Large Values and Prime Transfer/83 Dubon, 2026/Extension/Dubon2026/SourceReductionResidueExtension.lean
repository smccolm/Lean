import Dubon2026.SourceReductionAlgebraicNormalization
import Dubon2026.SourceValuationExtensionComparisons

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting.
Residue degree one gives an actual regular prolongation with the original
residue field. Native surjective lifting avoids introducing two auxiliary
quotient fields. Normalization is proved by the existing algebraic argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing
variable {L F Fbar E : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (ResidueField A) Fbar]
  [Field E] [Algebra F E] [Algebra L E] [IsScalarTower L F E]
  [Algebra.IsAlgebraic F E]

theorem exists_regularProlongation_of_residue_degree_one
    (R : RegularProlongation A F Fbar) (V : ValuationSubring E)
    (hV : V.comap (algebraMap F E) = R.integers)
    (hf1 : ∀ x ∈ V, ∃ y ∈ R.integers, x - algebraMap F E y ∈ V.nonunits) :
    ∃ S : RegularProlongation A E Fbar, S.integers = V ∧
      ∀ (x : S.integers) (y : R.integers), algebraMap F E y = x →
        S.residue x = R.residue y := by
  classical
  let incl : R.integers →+* V := ((algebraMap F E).comp R.integers.subtype).codRestrict V
    (fun y => ValuationApproximation.algebraMap_mem hV y)
  let θ : R.integers →+* ResidueField V := (IsLocalRing.residue V).comp incl
  have hθzero (y : R.integers) : θ y = 0 ↔ R.residue y = 0 := by
    rw [show θ y = IsLocalRing.residue V (incl y) from rfl,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    change V.valuation (algebraMap F E (y : F)) < 1 ↔ R.residue y = 0
    rw [ValuationApproximation.lt_one_iff hV]
    rw [← RingHom.mem_ker, R.ker_residue, ValuationSubring.valuation_lt_one_iff]
  have hk : RingHom.ker R.residue ≤ RingHom.ker θ := fun y hy => (hθzero y).mpr hy
  let φ : Fbar →+* ResidueField V := R.residue.liftOfSurjective R.residue_surjective ⟨θ, hk⟩
  have hφ (y : R.integers) : φ (R.residue y) = θ y :=
    R.residue.liftOfRightInverse_comp_apply _ _ ⟨θ, hk⟩ y
  have hsurj : Function.Surjective φ := by
    intro z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨y, hy, hxy⟩ := hf1 x x.2
    refine ⟨R.residue ⟨y, hy⟩, ?_⟩
    rw [hφ]
    change IsLocalRing.residue V (incl ⟨y, hy⟩) = IsLocalRing.residue V x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    change V.valuation (algebraMap F E y - x) < 1
    rw [Valuation.map_sub_swap]
    exact hxy
  let e : Fbar ≃+* ResidueField V := RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  let ρ : V →+* Fbar := e.symm.toRingHom.comp (IsLocalRing.residue V)
  have hρ (y : R.integers) : ρ (incl y) = R.residue y := by
    change e.symm (θ y) = R.residue y
    rw [← hφ]
    exact e.symm_apply_apply _
  have hρzero (x : V) : ρ x = 0 ↔ x ∈ maximalIdeal V := by
    change e.symm (IsLocalRing.residue V x) = 0 ↔ _
    rw [EmbeddingLike.map_eq_zero_iff, IsLocalRing.residue_eq_zero_iff]
  let S : RegularProlongation A E Fbar :=
    { integers := V
      residue := ρ
      algebraMap_mem_iff := fun c => by
        rw [IsScalarTower.algebraMap_apply L F E,
          ← ValuationSubring.mem_comap, hV, R.algebraMap_mem_iff]
      residue_surjective := fun z => by
        obtain ⟨y, hy⟩ := R.residue_surjective z
        exact ⟨incl y, (hρ y).trans hy⟩
      ker_residue := by ext x; exact hρzero x
      residue_algebraMap := fun a => by
        have heq : ∀ hm : algebraMap L E (a : L) ∈ V, (⟨algebraMap L E (a : L), hm⟩ : V) =
            incl ⟨algebraMap L F (a : L), (R.algebraMap_mem_iff a).mpr a.2⟩ :=
          fun _ => Subtype.ext (IsScalarTower.algebraMap_apply L F E (a : L))
        rw [heq, hρ, R.residue_algebraMap]
      exists_smul_mem := fun x hx => by
        obtain ⟨c, hc⟩ := R.exists_smul_valuation_eq_one_of_isIntegral V hV hx
          (Algebra.IsIntegral.isIntegral x)
        refine ⟨c, (V.valuation_le_one_iff _).mp hc.le, ?_⟩
        rw [ne_eq, hρzero, ValuationSubring.valuation_lt_one_iff]
        exact fun hlt => hlt.ne hc }
  refine ⟨S, rfl, fun x y hxy => ?_⟩
  have heq : x = incl y := Subtype.ext hxy.symm
  change ρ x = _
  rw [heq, hρ]

end
end Dubon2026.SourceCurve.RegularProlongation
