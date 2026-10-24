import Dubon2026.SourceReductionZeroChartValues
import Dubon2026.SourceCurveSeparableChartValuations
import Dubon2026.SourceIntegralChartPoleBound

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

private theorem isIntegral_self (y : F) : IsIntegral (Algebra.adjoin L ({y} : Set F)) y :=
  isIntegral_algebraMap (x := (⟨y, Algebra.self_mem_adjoin_singleton L y⟩ : Algebra.adjoin L {y}))

private theorem isIntegral_const (y : F) (c : L) :
    IsIntegral (Algebra.adjoin L ({y} : Set F)) (algebraMap L F c) := by
  have h := isIntegral_algebraMap (R := Algebra.adjoin L ({y} : Set F)) (A := F)
    (x := algebraMap L (Algebra.adjoin L ({y} : Set F)) c)
  rwa [← IsScalarTower.algebraMap_apply] at h

private theorem ne_top_of_mem_nonunits {V : ValuationSubring F} {y : F} (hy : y ∈ V.nonunits)
    (hy0 : y ≠ 0) : V ≠ ⊤ := by
  intro htop
  rcases (ValuationSubring.mem_nonunits_iff_or (A := V)).mp hy with h | h
  · exact hy0 h
  · exact h (by rw [htop]; exact ValuationSubring.mem_top _)

theorem exists_reduction_chart_place (R : RegularProlongation A F Fbar) (x : R.integers)
    (hx : Transcendental (ResidueField A) (R.residue x))
    [Algebra.IsSeparable (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar]
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (P : Place L F) {a₀ : A}
    (ha₀ : (x : F) - algebraMap L F a₀ ∈ P.toValuationSubring.nonunits) :
    ∃ Q : Place (ResidueField A) Fbar,
      ∀ h : R.integers, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (h : F) →
        ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
          R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∈
            Q.toValuationSubring.nonunits := by
  classical
  have hxP : (x : F) ∈ P.toValuationSubring := mem_of_sub_algebraMap_mem_nonunits P ha₀

  set Sic : Subalgebra (Algebra.adjoin L ({(x : F)} : Set F)) F :=
    integralClosure (Algebra.adjoin L ({(x : F)} : Set F)) F with hSic
  set S : Subring F := Sic.toSubring ⊓ R.integers.toSubring with hSdef
  have hS_int : ∀ s : S, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (s : F) :=
    fun s => (Subring.mem_inf.mp s.2).1
  have hS_O : ∀ s : S, (s : F) ∈ R.integers := fun s => (Subring.mem_inf.mp s.2).2
  have hS_P : ∀ s : S, (s : F) ∈ P.toValuationSubring := fun s =>
    P.mem_of_integral_adjoin hxP (hS_int s)
  have hmkS : ∀ {h : F}, IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) h → h ∈ R.integers →
      h ∈ S :=
    fun hh hhO => Subring.mem_inf.mpr ⟨hh, hhO⟩
  have hconstS : ∀ a : A, algebraMap L F a ∈ S := fun a =>
    hmkS (isIntegral_const (x : F) (a : L)) ((R.algebraMap_mem_iff a).mpr a.2)
  have hxS : (x : F) ∈ S := hmkS (isIntegral_self (x : F)) x.2
  let toO : S →+* R.integers := S.subtype.codRestrict R.integers hS_O
  let toP : S →+* P.toValuationSubring := S.subtype.codRestrict P.toValuationSubring hS_P
  let resS : S →+* Fbar := R.residue.comp toO
  have hresS : ∀ s : S, resS s = R.residue (toO s) := fun _ => rfl

  set I : Ideal S := (maximalIdeal P.toValuationSubring).comap toP with hI
  have hmemI : ∀ s : S, s ∈ I ↔ (s : F) ∈ P.toValuationSubring.nonunits := by
    intro s
    rw [hI, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff]
    exact Iff.rfl

  set B : Subring Fbar := resS.range with hB
  set resS' : S →+* B := resS.rangeRestrict with hresS'
  have hsurj : Function.Surjective resS' := RingHom.rangeRestrict_surjective resS
  have hcoe_resS' : ∀ s : S, ((resS' s : B) : Fbar) = resS s := fun _ => rfl
  set N : Ideal B := I.map resS' with hN

  have hNtop : N ≠ ⊤ := by
    intro htop
    have h1 : (1 : B) ∈ N := htop ▸ Submodule.mem_top
    obtain ⟨s, hsI, hs1⟩ := (Ideal.mem_map_iff_of_surjective resS' hsurj).mp h1
    have hs1' : resS s = 1 := by
      have := congrArg (fun b : B => (b : Fbar)) hs1
      simpa [hcoe_resS'] using this
    have hsO1 : (s : F) - 1 ∈ R.integers := sub_mem (hS_O s) (one_mem _)
    have hres0 : R.residue ⟨(s : F) - 1, hsO1⟩ = 0 := by
      have : (⟨(s : F) - 1, hsO1⟩ : R.integers) = toO s - 1 := Subtype.ext rfl
      rw [this, map_sub, map_one, sub_eq_zero, ← hresS]
      exact hs1'
    have hint : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) ((s : F) - 1) :=
      (hS_int s).sub isIntegral_one
    have hnu : (s : F) - 1 - algebraMap L F (-1) ∈ P.toValuationSubring.nonunits := by
      rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
      exact (hmemI s).mp hsI
    have := mem_nonunits_of_residue_eq_zero R x hx hfin hdeg P ha₀ hsO1 hint hres0 hnu
    rw [ValuationSubring.mem_nonunits_iff, Valuation.map_neg, map_one] at this
    exact lt_irrefl _ this

  obtain ⟨V, hBV, hNV⟩ := Ideal.image_subset_nonunits_valuationSubring N hNtop
  have hkB : ∀ κ : ResidueField A, algebraMap (ResidueField A) Fbar κ ∈ B := by
    intro κ
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective κ
    refine ⟨⟨algebraMap L F a, hconstS a⟩, ?_⟩
    rw [hresS, show toO ⟨algebraMap L F a, hconstS a⟩ = constHom R a from Subtype.ext rfl,
      residue_constHom]
  have hkV : ∀ κ : ResidueField A, algebraMap (ResidueField A) Fbar κ ∈ V :=
    fun κ => hBV (hkB κ)
  have hIV : ∀ s : S, s ∈ I → resS s ∈ V.nonunits := fun s hsI =>
    hNV ⟨resS' s, Ideal.mem_map_of_mem resS' hsI, rfl⟩

  have hres_sub : ∀ (h : R.integers) (hh : IsIntegral (Algebra.adjoin L ({(x : F)} : Set F)) (h : F))
      (a : A), resS ⟨(h : F) - algebraMap L F a, sub_mem (hmkS hh h.2) (hconstS a)⟩ =
        R.residue h - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
    intro h hh a
    rw [hresS, show toO ⟨(h : F) - algebraMap L F a, sub_mem (hmkS hh h.2) (hconstS a)⟩ =
      h - constHom R a from Subtype.ext rfl, map_sub, residue_constHom]

  have hVtop : V ≠ ⊤ := by
    refine ne_top_of_mem_nonunits (y := R.residue x - algebraMap (ResidueField A) Fbar
      (IsLocalRing.residue A a₀)) ?_ ?_
    · rw [← hres_sub x (isIntegral_self (x : F)) a₀]
      exact hIV _ ((hmemI _).mpr ha₀)
    · intro h0
      apply hx
      rw [sub_eq_zero] at h0
      rw [h0]
      exact isAlgebraic_algebraMap _

  haveI : FiniteDimensional
      (IntermediateField.adjoin (ResidueField A) ({R.residue x} : Set Fbar)) Fbar :=
    Module.finite_of_finrank_pos hfin
  have hxV : R.residue x ∈ V := by
    apply hBV
    exact ⟨⟨(x : F), hxS⟩, rfl⟩
  obtain ⟨Q, hQ⟩ := exists_place_of_separable_chart (R.residue x) hx V hkV hxV hVtop
  refine ⟨Q, fun h hh a ha => ?_⟩
  rw [hQ, ← hres_sub h hh a]
  exact hIV _ ((hmemI _).mpr ha)


end
end Dubon2026.SourceCurve.RegularProlongation
