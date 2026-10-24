import Dubon2026.SourceCurvePlaceConstantValues
import Dubon2026.SourceReductionChartPlaceUniqueness

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy and residual association -> original weight-two
Frobenius/inertia -> modular good reduction -> reduction-place comparison.
The two proved chart comparisons are glued with their exact finite-chart
fiber descriptions, required by the subsequent principal-divisor identity.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_exists_placeMap_mapDomain_eq_ord_of_residue_integralClosure_surjective.
Existing finite-coordinate residue surjectivity supplies actual constant
values; no abstract curve package or place-map certificate is assumed. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing

section
variable {ι κ : Type*}
private theorem exists_map_of_two_charts (Dom₁ Dom₂ : ι → Prop) (Red₁ Red₂ : ι → κ → Prop)
    (Fin : κ → Prop)
    (hcover : ∀ P, Dom₁ P ∨ Dom₂ P)
    (E₁ : ∀ P, Dom₁ P → ∃! Q, Red₁ P Q) (E₂ : ∀ P, Dom₂ P → ∃! Q, Red₂ P Q)
    (hfin₁ : ∀ P Q, Dom₁ P → Red₁ P Q → Fin Q)
    (hinf₂ : ∀ P Q, ¬ Dom₁ P → Dom₂ P → Red₂ P Q → ¬ Fin Q)
    (hboth : ∀ P Q, Dom₁ P → Dom₂ P → Red₂ P Q → Fin Q) :
    ∃ r : ι → κ, (∀ P Q, Fin Q → (r P = Q ↔ Dom₁ P ∧ Red₁ P Q)) ∧
      (∀ P Q, ¬ Fin Q → (r P = Q ↔ Dom₂ P ∧ Red₂ P Q)) := by
  classical
  let r : ι → κ := fun P =>
    if h : Dom₁ P then (E₁ P h).exists.choose
    else (E₂ P ((hcover P).resolve_left h)).exists.choose
  have hr₁ : ∀ P (h : Dom₁ P), Red₁ P (r P) := fun P h => by
    simp only [r, dif_pos h]
    exact (E₁ P h).exists.choose_spec
  have hr₂ : ∀ P (h : ¬ Dom₁ P), Red₂ P (r P) := fun P h => by
    simp only [r, dif_neg h]
    exact (E₂ P ((hcover P).resolve_left h)).exists.choose_spec
  refine ⟨r, fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩,
    fun P Q hQ => ⟨fun hPQ => ?_, fun ⟨hd, hred⟩ => ?_⟩⟩
  · by_cases h : Dom₁ P
    · exact ⟨h, hPQ ▸ hr₁ P h⟩
    · exact absurd hQ (hinf₂ P Q h ((hcover P).resolve_left h) (hPQ ▸ hr₂ P h))
  · exact (E₁ P hd).unique (hr₁ P hd) hred
  · by_cases h : Dom₁ P
    · exact absurd (hfin₁ P _ h (hr₁ P h)) (hPQ ▸ hQ)
    · exact ⟨(hcover P).resolve_left h, hPQ ▸ hr₂ P h⟩
  · by_cases h : Dom₁ P
    · exact absurd (hboth P Q h hd hred) hQ
    · exact (E₂ P ((hcover P).resolve_left h)).unique (hr₂ P h) hred

end

variable {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]

/-- Original places whose coordinate value lies in the coefficient valuation ring. -/
def ChartDomain (P : Place L F) (y : F) : Prop :=
  ∃ a : A, y - algebraMap L F a ∈ P.toValuationSubring.nonunits

/-- Reduction of all integral-chart functions and their actual constant values. -/
def ChartReducesTo (R : RegularProlongation A F Fbar) (y : F) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) : Prop :=
  ∀ h : R.integers, IsIntegral (Algebra.adjoin L {y}) (h : F) →
    ∀ a : A, (h : F) - algebraMap L F a ∈ P.toValuationSubring.nonunits →
      R.residue h - algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a) ∈
        Q.toValuationSubring.nonunits

variable {A}

private theorem isIntegral_self (y : F) : IsIntegral (Algebra.adjoin L {y}) y :=
  isIntegral_algebraMap (x := (⟨y, Algebra.self_mem_adjoin_singleton L y⟩ : Algebra.adjoin L {y}))

theorem residue_mem_of_chart_reducesTo (R : RegularProlongation A F Fbar) (y : R.integers) (P : Place L F)
    (Q : Place (IsLocalRing.ResidueField A) Fbar) (hd : ChartDomain A P (y : F)) (hred : ChartReducesTo A R y P Q) :
    R.residue y ∈ Q.toValuationSubring := by
  obtain ⟨a, ha⟩ := hd
  have h1 := ValuationSubring.nonunits_subset (hred y (isIntegral_self (y : F)) a ha)
  have h2 := Q.algebraMap_mem' (IsLocalRing.residue A a)
  simpa using add_mem h1 h2

theorem exists_reduction_place_map_of_two_charts
    (R : RegularProlongation A F Fbar) (x xi : R.integers)
    (hx0 : R.residue x ≠ 0) (hxiF : (xi : F) = (x : F)⁻¹)
    (hxires : R.residue xi = (R.residue x)⁻¹)
    (hres : ∀ P : Place L F, Function.Surjective (algebraMap L P.ResidueField))
    (E₁ : ∀ P : Place L F, ChartDomain A P (x : F) → ∃! Q, ChartReducesTo A R (x : F) P Q)
    (E₂ : ∀ P : Place L F, ChartDomain A P (xi : F) → ∃! Q, ChartReducesTo A R (xi : F) P Q) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      (∀ P Q, R.residue x ∈ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (x : F) ∧ ChartReducesTo A R (x : F) P Q)) ∧
      (∀ P Q, R.residue x ∉ Q.toValuationSubring →
        (r P = Q ↔ ChartDomain A P (xi : F) ∧ ChartReducesTo A R (xi : F) P Q)) := by
  have hxF0 : (x : F) ≠ 0 := by
    intro h
    exact hx0 (by rw [show x = 0 from Subtype.ext h, map_zero])
  have hcover : ∀ P : Place L F, ChartDomain A P (x : F) ∨ ChartDomain A P (xi : F) := fun P =>
    or_iff_not_imp_left.mpr fun h => by
      rw [hxiF]; exact Place.exists_inv_sub_mem_nonunits A P (hres P) (x : F) h
  have hfin₁ : ∀ P Q, ChartDomain A P (x : F) → ChartReducesTo A R (x : F) P Q →
      R.residue x ∈ Q.toValuationSubring := fun P Q hd hred =>
    residue_mem_of_chart_reducesTo R x P Q hd hred
  have hinf₂ : ∀ P Q, ¬ ChartDomain A P (x : F) → ChartDomain A P (xi : F) → ChartReducesTo A R (xi : F) P Q →
      R.residue x ∉ Q.toValuationSubring := by
    intro P Q hnd hd hred hfinQ
    obtain ⟨a', ha'⟩ := hd
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'
    by_cases hunit : IsUnit a'
    ·
      obtain ⟨u, hu⟩ := hunit
      apply hnd
      refine ⟨(u⁻¹ : Aˣ), ?_⟩
      have ha'0 : ((a' : A) : L) ≠ 0 := fun h =>
        (hu ▸ u.isUnit).ne_zero (Subtype.ext h)
      have hcoe : (((u⁻¹ : Aˣ) : A) : L) = ((a' : A) : L)⁻¹ := by
        refine eq_inv_of_mul_eq_one_right ?_
        rw [← hu]
        exact_mod_cast congrArg Subtype.val u.mul_inv
      have := Place.inv_sub_inv_mem_nonunits P ha'0 ha'
      rwa [hxiF, inv_inv, ← hcoe] at this
    ·
      have hmax : a' ∈ maximalIdeal A :=
        (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hunit)
      have hzero : IsLocalRing.residue A a' = 0 := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
      rw [hzero, map_zero, sub_zero, hxires, ValuationSubring.mem_nonunits_iff, map_inv₀] at hres
      rw [← Q.toValuationSubring.valuation_le_one_iff] at hfinQ
      have hv0 : 0 < Q.toValuationSubring.valuation (R.residue x) :=
        zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx0)
      exact absurd hfinQ (not_le.mpr ((inv_lt_one₀ hv0).mp hres))
  have hboth : ∀ P Q, ChartDomain A P (x : F) → ChartDomain A P (xi : F) → ChartReducesTo A R (xi : F) P Q →
      R.residue x ∈ Q.toValuationSubring := by
    intro P Q hd hd' hred
    obtain ⟨a, ha⟩ := hd
    obtain ⟨a', ha'⟩ := hd'
    obtain ⟨ha0, haa'⟩ := Place.inv_const_eq P hxF0 ha (hxiF ▸ ha')
    have hres := hred xi (isIntegral_self (xi : F)) a' ha'

    have hunit : IsUnit a' := by
      refine isUnit_iff_exists_inv.mpr ⟨a, Subtype.ext ?_⟩
      show ((a' : A) : L) * ((a : A) : L) = 1
      rw [haa', inv_mul_cancel₀ ha0]
    have hres0 : IsLocalRing.residue A a' ≠ 0 := fun h0 =>
      mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp ((IsLocalRing.residue_eq_zero_iff _).mp h0))
        hunit
    have hvc : Q.toValuationSubring.valuation
        (algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a')) = 1 :=
      Place.valuation_algebraMap_eq_one Q hres0
    rw [ValuationSubring.mem_nonunits_iff] at hres
    have hvxi : Q.toValuationSubring.valuation (R.residue xi) = 1 := by
      have := Valuation.map_add_eq_of_lt_left Q.toValuationSubring.valuation
        (x := algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a'))
        (y := R.residue xi - algebraMap (IsLocalRing.ResidueField A) Fbar
          (IsLocalRing.residue A a')) (by rwa [hvc])
      rwa [add_sub_cancel, hvc] at this
    rw [← Q.toValuationSubring.valuation_le_one_iff, show R.residue x = (R.residue xi)⁻¹ by
      rw [hxires, inv_inv], map_inv₀, hvxi, inv_one]

  obtain ⟨r, hr₁, hr₂⟩ := exists_map_of_two_charts
    (fun P : Place L F => ChartDomain A P (x : F)) (fun P : Place L F => ChartDomain A P (xi : F))
    (ChartReducesTo A R (x : F)) (ChartReducesTo A R (xi : F))
    (fun Q : Place (IsLocalRing.ResidueField A) Fbar => R.residue x ∈ Q.toValuationSubring)
    hcover E₁ E₂ hfin₁ hinf₂ hboth
  exact ⟨r, hr₁, hr₂⟩

end
end Dubon2026.SourceCurve.RegularProlongation
