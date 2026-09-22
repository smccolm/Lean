import TaoTrudgianYang2025.BourgainIntegerSlice

/-!
# One shift comparing the full integer slice with all component occupancies

The signed first-moment argument compares both the cardinality and its square
root at the same shift. Its upstream hypothesis is an integrated weighted mass
inequality; later actual-component consumers derive that inequality.
-/

open MeasureTheory Set
open scoped Interval Classical

noncomputable section

namespace TaoTrudgianYang2025

/-- An integrated comparison yields the full two-term integer-slice comparison
at one common shift, including strict positivity and hence a nonempty slice. -/
theorem bourgain_full_slice_common_shift {ι : Type*}
    (A : Finset ι) (w : ι → ℝ) (D : ι → Finset ℤ)
    {H T V a b : ℝ} (hH : 0 < H) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hmass : a*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real (bourgainZetaBand T V)) <
      ∑ i ∈ A, w i*bourgainZetaBandMass (D i) H T V) :
    ∃ u ∈ Ioc (-H) H,
      (bourgainIntegerSlice H T V u).Nonempty ∧
      a*((bourgainIntegerSlice H T V u).card : ℝ)+
        b*Real.sqrt ((bourgainIntegerSlice H T V u).card : ℝ) <
      ∑ i ∈ A, w i*((D i ∩ bourgainIntegerSlice H T V u).card : ℝ) := by
  let S := bourgainZetaBand T V
  let E := bourgainIntegerCover H T
  let X := bourgainBandOccupancy E S
  let Y := fun u => ∑ i ∈ A, w i*bourgainBandOccupancy (D i) S u
  have hS := measurableSet_bourgainZetaBand T V
  have hXi := bourgainBandOccupancy_intervalIntegrable E hS (-H) H
  have hXs := bourgainBandOccupancy_sqrt_intervalIntegrable E hS (-H) H
  have hwi (i : ι) : IntervalIntegrable
      (fun u => w i*bourgainBandOccupancy (D i) S u) volume (-H) H :=
    (bourgainBandOccupancy_intervalIntegrable (D i) hS _ _).const_mul _
  have hYi : IntervalIntegrable Y volume (-H) H := by
    convert IntervalIntegrable.sum A (fun i _ => hwi i) using 1
    ext u
    simp only [Y, Finset.sum_apply]
  let f := fun u => Y u-a*X u-b*Real.sqrt (X u)
  have hfi : IntervalIntegrable f volume (-H) H :=
    (hYi.sub (hXi.const_mul a)).sub (hXs.const_mul b)
  have hY : (∫ u in -H..H, Y u) =
      ∑ i ∈ A, w i*bourgainZetaBandMass (D i) H T V := by
    rw [intervalIntegral.integral_finsetSum (fun i _ => hwi i)]
    simp only [intervalIntegral.integral_const_mul, bourgainZetaBandMass, S]
  have hX : (∫ u in -H..H, X u) ≤
      (2*Nat.ceil H+1 : ℕ)*volume.real S :=
    bourgainZetaBandMass_le_measure E hH.le T V
  have hsqrt : (∫ u in -H..H, Real.sqrt (X u)) ≤
      Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real S) := by
    simpa only [bourgainIntegerSlice_card] using
      bourgainIntegerSlice_integral_sqrt_card_le hH.le T V
  have hpos : 0 < ∫ u in -H..H, f u := by
    dsimp only [f]
    rw [intervalIntegral.integral_sub (hYi.sub (hXi.const_mul a)) (hXs.const_mul b),
      intervalIntegral.integral_sub hYi (hXi.const_mul a),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hY]
    have h₁ := mul_le_mul_of_nonneg_left hX ha
    have h₂ := mul_le_mul_of_nonneg_left hsqrt hb
    change a*(2*Nat.ceil H+1 : ℕ)*volume.real S+
      b*Real.sqrt (2*H*(2*Nat.ceil H+1 : ℕ)*volume.real S) < _ at hmass
    nlinarith
  obtain ⟨u, hu, havg⟩ := bourgain_interval_integral_common_shift hH hfi
  have hfpos : 0 < f u := by
    have hp : 0 < 2*H*f u := hpos.trans_le havg
    exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2*H)).mp hp
  have hucc : u ∈ Icc (-H) H := ⟨hu.1.le, hu.2⟩
  have hfinal : a*((bourgainIntegerSlice H T V u).card : ℝ)+
      b*Real.sqrt ((bourgainIntegerSlice H T V u).card : ℝ) <
      ∑ i ∈ A, w i*((D i ∩ bourgainIntegerSlice H T V u).card : ℝ) := by
    simp_rw [bourgainIntegerSlice_inter_card _ hucc, bourgainIntegerSlice_card]
    change a*X u+b*Real.sqrt (X u) < Y u
    dsimp only [f] at hfpos
    linarith
  refine ⟨u, hu, ?_, hfinal⟩
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hfinal
  simp only [Finset.inter_empty, Finset.card_empty, Nat.cast_zero, mul_zero,
    Real.sqrt_zero, add_zero, Finset.sum_const_zero] at hfinal
  exact (lt_irrefl 0) hfinal

end TaoTrudgianYang2025
