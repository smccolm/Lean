import Dubon2026.SourceKummerIntegralRelations

/-! DUB-17/18 -> Picard torsion injectivity -> Kummer power lifting ->
distinct extending reductions. Every reduced Kummer root is the center of
an actual valuation on the extension field. The native valuation-domination
theorem applies to the residue kernel on the integral generated algebra;
the preceding monic-relation proof makes that residue map well defined. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open Polynomial IsLocalRing
variable {L F Fbar E : Type*} [Field L] {A : ValuationSubring L}
  [Field F] [Algebra L F] [Field Fbar] [Algebra (ResidueField A) Fbar]
  [Field E] [Algebra F E]

/-- A valuation centered at the given actual reduced root on the integral generated algebra. -/
structure KummerCenter (R : RegularProlongation A F Fbar) (α : E) (s : Fbar)
    (V : ValuationSubring E) : Prop where
  /-- Every integral polynomial in the generator lies in the valuation ring. -/
  integral : ∀ p : R.integers[X], aeval α (p.map R.integers.subtype) ∈ V
  /-- Relations vanishing at the reduced root lie in the maximal ideal. -/
  vanishes : ∀ p : R.integers[X], eval₂ R.residue s p = 0 →
    V.valuation (aeval α (p.map R.integers.subtype)) < 1

theorem exists_kummerCenter (R : RegularProlongation A F Fbar)
    {q : ℕ} [Fact q.Prime] (f : R.integers) (hf : ∀ g : F, g ^ q ≠ (f : F))
    {α : E} (hα : α ^ q = algebraMap F E (f : F))
    {s : Fbar} (hs : s ^ q = R.residue f) :
    ∃ V : ValuationSubring E, KummerCenter R α s V := by
  let e : R.integers[X] →+* E :=
    (aeval α : F[X] →ₐ[F] E).toRingHom.comp (mapRingHom R.integers.subtype)
  let ρ : R.integers[X] →+* Fbar := eval₂RingHom R.residue s
  have hsurj := e.rangeRestrict_surjective
  have hker : RingHom.ker e.rangeRestrict ≤ RingHom.ker ρ := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    apply R.kummer_residue_eval_zero_of_relation f hf hα hs p
    exact congrArg Subtype.val hp
  let φ : e.range →+* Fbar := e.rangeRestrict.liftOfSurjective hsurj ⟨ρ, hker⟩
  have hφ (p) : φ (e.rangeRestrict p) = ρ p :=
    e.rangeRestrict.liftOfRightInverse_comp_apply _ _ ⟨ρ, hker⟩ p
  have hproper : RingHom.ker φ ≠ ⊤ := by
    rw [ne_eq, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one]
    exact one_ne_zero
  obtain ⟨V, hBV, hIV⟩ := Ideal.image_subset_nonunits_valuationSubring (RingHom.ker φ) hproper
  refine ⟨V, ⟨fun p => hBV ⟨p, rfl⟩, fun p hp => ?_⟩⟩
  have hmem : e.rangeRestrict p ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, hφ]
    exact hp
  exact hIV ⟨e.rangeRestrict p, hmem, rfl⟩

theorem KummerCenter.algebraMap_mem
    {R : RegularProlongation A F Fbar} {α : E} {s : Fbar} {V : ValuationSubring E}
    (h : KummerCenter R α s V) (y : R.integers) : algebraMap F E (y : F) ∈ V := by
  simpa using h.integral (C y)

theorem KummerCenter.valuation_sub_lt_one
    {R : RegularProlongation A F Fbar} {α : E} {s : Fbar} {V : ValuationSubring E}
    (h : KummerCenter R α s V) {y : R.integers} (hy : R.residue y = s) :
    V.valuation (α - algebraMap F E (y : F)) < 1 := by
  have hh := h.vanishes (X - C y) (by simp [hy])
  rw [Polynomial.map_sub, map_X, map_C, map_sub, aeval_X, aeval_C] at hh
  exact hh

end
end Dubon2026.SourceCurve.RegularProlongation
