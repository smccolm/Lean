import Mathlib

/-! DUB-17/18 -> Kummer power lifting -> sum-of-genera comparison ->
dimension one of the algebraic constant valuation. A rational valuation
ring is a localization of the integers. The proof is adapted from the
frozen Apache-2.0 FLT source (6e837e75355538c7f80bab5b956861e86c4eacc2).
Only the rational base case is used; no general transcendence-degree
valuation inequality is introduced. -/
namespace Dubon2026.SourceCurve.RationalValuation
noncomputable section
open ValuationSubring

/-- The integers that become units in the rational valuation ring. -/
def unitInts (B : ValuationSubring ℚ) : Submonoid ℤ :=
  (IsUnit.submonoid B).comap (algebraMap ℤ B)

lemma mem_unitInts {B : ValuationSubring ℚ} {n : ℤ} :
    n ∈ unitInts B ↔ IsUnit (algebraMap ℤ B n) := Iff.rfl

lemma unitInts_le_nonZeroDivisors (B : ValuationSubring ℚ) : unitInts B ≤ nonZeroDivisors ℤ := by
  intro n hn
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rintro rfl
  rw [mem_unitInts, map_zero] at hn
  exact not_isUnit_zero hn

lemma isUnit_den (B : ValuationSubring ℚ) (x : B) : IsUnit (algebraMap ℤ B ((x : ℚ).den : ℤ)) := by
  set r : ℚ := (x : ℚ) with hr
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨u, v, huv⟩ := hcop
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero

  have hinv : ((r.den : ℚ))⁻¹ = u * r + v := by
    have h1 : (u : ℚ) * r.num + v * r.den = 1 := by exact_mod_cast huv
    have h2 : (r.num : ℚ) = r * r.den := by rw [Rat.mul_den_eq_num]
    rw [h2] at h1
    field_simp
    linarith [h1]
  have hmem : ((r.den : ℚ))⁻¹ ∈ B := by
    rw [hinv]
    exact B.add_mem _ _ (B.mul_mem _ _ (intCast_mem B u) x.2) (intCast_mem B v)
  refine ⟨⟨algebraMap ℤ B (r.den : ℤ), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    simp [hden0]
  · apply Subtype.ext
    simp [hden0]

theorem integerUnits_isLocalization (B : ValuationSubring ℚ) : IsLocalization (unitInts B) B := by
  rw [isLocalization_iff]
  refine ⟨fun n => n.2, fun z => ?_, fun {a b} h => ⟨1, by
    have : (a : ℚ) = b := by
      have h' := congrArg (fun t : B => (t : ℚ)) h
      simpa using h'
    exact_mod_cast congrArg (fun t => 1 * t) (show a = b by exact_mod_cast this)⟩⟩
  refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), isUnit_den B z⟩⟩, ?_⟩
  apply Subtype.ext
  simp [Rat.mul_den_eq_num]

theorem ringKrullDim_le_one (B : ValuationSubring ℚ) : ringKrullDim B ≤ 1 := by
  letI : IsLocalization (unitInts B) B := integerUnits_isLocalization B
  have h : Ring.DimensionLEOne B :=
    Ring.DimensionLEOne.localization B (unitInts_le_nonZeroDivisors B)
  have : Ring.KrullDimLE 1 B := inferInstance
  exact (Ring.krullDimLE_iff).mp this


end
end Dubon2026.SourceCurve.RationalValuation
