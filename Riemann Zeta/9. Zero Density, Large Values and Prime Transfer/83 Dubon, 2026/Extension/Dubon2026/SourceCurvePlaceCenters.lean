import Dubon2026.SourceCurvePlaceRestriction
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Algebra.Polynomial.Lifts

/-! DUB-17/18 -> regular differential realization and dimension -> local
derivative regularity and principal-divisor finiteness. Actual valuation
rings are identified with the localizations at their centers on a Dedekind
chart. This also gives finite support for positive orders on each chart.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_AlgebraicCurve_PlacesOverDVR, IntegrallyClosed and Chart sections.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain WithZero IsLocalRing

section
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
theorem ord_eq_zero_iff_adicValuation_eq_one {f : F} (hf : f ≠ 0) :
    v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [ord, neg_eq_zero]
  constructor
  · intro h
    have h2 := exp_log (v.adicValuation_ne_zero hf)
    rw [h, exp_zero] at h2
    exact h2.symm
  · intro h
    rw [h, log_one]


end

section IntegrallyClosed

open Polynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (w : Place K F)

theorem ord_neg (f : F) : w.ord (-f) = w.ord f := by
  simp only [ord, Valuation.map_neg]

theorem mem_of_eval_monic_eq_zero {P : Polynomial F} (hP : P.Monic)
    (hcoeff : ∀ i, P.coeff i ∈ w.toValuationSubring) {x : F} (hx : P.eval x = 0) :
    x ∈ w.toValuationSubring := by

  have hlift : P ∈ lifts (algebraMap w.toValuationSubring F) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨P.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨Q, hQmap, -, hQmonic⟩ := lifts_and_degree_eq_and_monic hlift hP

  have hint : IsIntegral w.toValuationSubring x := by
    refine ⟨Q, hQmonic, ?_⟩
    rw [show eval₂ (algebraMap w.toValuationSubring F) x Q = (Q.map _).eval x from
      (eval_map _ x).symm, hQmap, hx]
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact hy ▸ y.2

theorem mem_maximalIdeal_iff_ord_pos {x : F} (hx : x ≠ 0)
    (hmem : x ∈ w.toValuationSubring) :
    (⟨x, hmem⟩ : w.toValuationSubring) ∈ IsLocalRing.maximalIdeal w.toValuationSubring ↔
      0 < w.ord x := by
  have hnonneg : 0 ≤ w.ord x := w.ord_nonneg_of_mem hmem
  have hcoe : ((⟨x, hmem⟩ : w.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← w.adicValuation_coe_eq_one_iff,
    hcoe, ← w.ord_eq_zero_iff_adicValuation_eq_one hx]
  omega

end IntegrallyClosed

section Chart

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
variable (w : Place K F)

private def chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    R →+* w.toValuationSubring :=
  (algebraMap R F).codRestrict w.toValuationSubring.toSubring hw

omit [IsDedekindDomain R] [IsFractionRing R F] in
@[simp]
private theorem coe_chartHom (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) (r : R) :
    (chartHom w hw r : F) = algebraMap R F r := rfl

variable (R) in

/-- The actual center of the place on the given Dedekind chart. -/
def center (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) : Ideal R :=
  (IsLocalRing.maximalIdeal w.toValuationSubring).comap (chartHom w hw)

instance (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (center R w hw).IsPrime :=
  Ideal.comap_isPrime _ _

omit [IsDedekindDomain R] [IsFractionRing R F] in
theorem mem_center_iff (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) {r : R} :
    r ∈ center R w hw ↔
      (⟨algebraMap R F r, hw r⟩ : w.toValuationSubring) ∈
        IsLocalRing.maximalIdeal w.toValuationSubring :=
  Iff.rfl

theorem mem_center_iff_ord_pos (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {r : R} (hr : r ≠ 0) :
    r ∈ center R w hw ↔ 0 < w.ord (algebraMap R F r) := by
  have hr' : algebraMap R F r ≠ 0 := by
    simpa using (IsFractionRing.injective R F).ne_iff.mpr hr
  rw [mem_center_iff, w.mem_maximalIdeal_iff_ord_pos hr']

omit [IsDedekindDomain R] [IsFractionRing R F] in

private theorem inv_algebraMap_mem (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    {s : R} (hs : IsUnit (chartHom w hw s)) :
    (algebraMap R F s)⁻¹ ∈ w.toValuationSubring := by
  obtain ⟨u, hu⟩ := hs
  have hcoe : ((u : w.toValuationSubring) : F) = algebraMap R F s := by rw [hu]; rfl
  have h1 : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
      * algebraMap R F s = 1 := by
    have hmul := congrArg (fun a : w.toValuationSubring => (a : F)) u.inv_mul
    push_cast at hmul
    rwa [hcoe] at hmul
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact SetLike.coe_mem _

theorem center_ne_bot (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    center R w hw ≠ ⊥ := by
  intro hbot
  apply w.ne_top'

  have hunit : ∀ r : R, r ≠ 0 → IsUnit (chartHom w hw r) := by
    intro r hr
    by_contra hu
    have : r ∈ center R w hw :=
      (mem_center_iff w hw).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    rw [hbot] at this
    exact hr (by simpa using this)

  refine SetLike.ext fun x => ⟨fun _ => ValuationSubring.mem_top x, fun _ => ?_⟩
  obtain ⟨a, b, hb, hx⟩ := IsFractionRing.div_surjective (A := R) x
  rw [← hx, div_eq_mul_inv]
  exact mul_mem (hw a) (inv_algebraMap_mem w hw (hunit b (nonZeroDivisors.ne_zero hb)))

variable (R) in

/-- The nonzero prime center of the actual place. -/
def centerHeightOneSpectrum (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum R :=
  ⟨center R w hw, inferInstance, center_ne_bot w hw⟩

@[simp]
theorem centerHeightOneSpectrum_asIdeal
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    (centerHeightOneSpectrum R w hw).asIdeal = center R w hw := rfl

theorem valuationSubringAtPrime_centerHeightOneSpectrum_le
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) ≤
      w.toValuationSubring := by
  rintro x ⟨a, s, hs, rfl⟩
  refine mul_mem (hw a) (inv_algebraMap_mem w hw ?_)
  rw [← IsLocalRing.notMem_maximalIdeal]
  exact fun hmem => hs ((mem_center_iff w hw).mpr hmem)

theorem toValuationSubring_eq_of_forall_mem
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring) :
    w.toValuationSubring =
      HeightOneSpectrum.valuationSubringAtPrime F (centerHeightOneSpectrum R w hw) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtPrime_centerHeightOneSpectrum_le w hw) w.ne_top').symm

theorem finite_setOf_forall_mem_and_ord_pos {r₀ : R} (hr₀ : r₀ ≠ 0) :
    {w : Place K F | (∀ r : R, algebraMap R F r ∈ w.toValuationSubring) ∧
      0 < w.ord (algebraMap R F r₀)}.Finite := by
  have hfin : {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hr₀)
  rw [← Set.finite_coe_iff]
  haveI := hfin.to_subtype
  refine Finite.of_injective
    (fun w => (⟨centerHeightOneSpectrum R w.1 w.2.1, ?_⟩ :
      {p : HeightOneSpectrum R | p.asIdeal ∣ Ideal.span {r₀}})) ?_
  · rw [Set.mem_setOf_eq, centerHeightOneSpectrum_asIdeal, Ideal.dvd_span_singleton]
    exact (mem_center_iff_ord_pos w.1 w.2.1 hr₀).mpr w.2.2
  · intro w w' h
    have hcenter : centerHeightOneSpectrum R w.1 w.2.1
        = centerHeightOneSpectrum R w'.1 w'.2.1 := congrArg Subtype.val h
    refine Subtype.ext (Place.ext ?_)
    rw [toValuationSubring_eq_of_forall_mem w.1 w.2.1,
      toValuationSubring_eq_of_forall_mem w'.1 w'.2.1, hcenter]

end Chart

end
end Dubon2026.SourceCurve.Place
