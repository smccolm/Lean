import Dubon2026.FiniteAdeleClassicalIntersection

/-! # Actual integral finite-adele residues modulo every positive integer -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- Every genuine level multiple is integral at all finite places. -/
theorem finiteAdeleLevelMultiple_integral (N : ℕ) {x : FiniteAdeleRing ℤ ℚ}
    (hx : finiteAdeleLevelMultiple N x) : x ∈ finiteAdeleIntegerSubring := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact finiteAdeleIntegerSubring.mul_mem (by simp) hy

/-- The actual level ideal is closed under addition in the original finite adele ring. -/
theorem finiteAdeleLevelMultiple_add (N : ℕ) {x y : FiniteAdeleRing ℤ ℚ}
    (hx : finiteAdeleLevelMultiple N x) (hy : finiteAdeleLevelMultiple N y) :
    finiteAdeleLevelMultiple N (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, finiteAdeleIntegerSubring.add_mem ha hb, (mul_add _ _ _).symm⟩

/-- On actual diagonal integers, the finite adelic level ideal is precisely ordinary integer divisibility. -/
theorem finiteAdeleLevelMultiple_int_iff (N : ℕ) [NeZero N] (n : ℤ) :
    finiteAdeleLevelMultiple N (n : FiniteAdeleRing ℤ ℚ) ↔ (N : ℤ) ∣ n := by
  rw [finiteAdeleLevelMultiple_iff]
  have he : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * (n : FiniteAdeleRing ℤ ℚ) =
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹ * (n : ℚ)) := by
    simp only [map_mul, map_intCast]
  rw [he, finiteAdele_rational_integral_iff]
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_mul, Int.cast_natCast, hm, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    rw [Int.cast_mul, Int.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]

/-- Rational density and the genuine open level ideal give an original integer representative for every integral finite adele modulo the level. -/
theorem finiteAdele_integral_integer_representative (N : ℕ) [NeZero N]
    (x : FiniteAdeleRing ℤ ℚ) (hx : x ∈ finiteAdeleIntegerSubring) :
    ∃ n : ℤ, finiteAdeleLevelMultiple N (x - n) := by
  have ho : IsOpen {y : FiniteAdeleRing ℤ ℚ | finiteAdeleLevelMultiple N (x - y)} :=
    (finiteAdeleLevelMultiple_isOpen N).preimage (continuous_const.sub continuous_id)
  obtain ⟨q, hq⟩ := rational_dense_finiteAdeles.exists_mem_open ho
    ⟨x, by exact ⟨0, finiteAdeleIntegerSubring.zero_mem, by simp⟩⟩
  have hi : algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ finiteAdeleIntegerSubring := by
    have h := finiteAdeleIntegerSubring.sub_mem hx (finiteAdeleLevelMultiple_integral N hq)
    simpa only [sub_sub_cancel] using h
  obtain ⟨n, hn⟩ := (finiteAdele_rational_integral_iff q).mp hi
  refine ⟨n, ?_⟩
  simpa only [← hn, map_intCast] using hq

/-- Every actual integral finite adele has a genuine residue in the ordinary finite ring Z/NZ. -/
theorem finiteAdele_integral_residue (N : ℕ) [NeZero N]
    (x : FiniteAdeleRing ℤ ℚ) (hx : x ∈ finiteAdeleIntegerSubring) :
    ∃ r : ZMod N, finiteAdeleLevelMultiple N (x - (r.val : FiniteAdeleRing ℤ ℚ)) := by
  obtain ⟨n, hn⟩ := finiteAdele_integral_integer_representative N x hx
  let r : ZMod N := n
  have hd : (N : ℤ) ∣ n - (r.val : ℤ) :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val : ℤ) n N).mp (by simp [r])
  have hm := (finiteAdeleLevelMultiple_int_iff N (n - (r.val : ℤ))).mpr hd
  have hs := finiteAdeleLevelMultiple_add N hn hm
  refine ⟨r, ?_⟩
  simpa only [Int.cast_sub, Int.cast_natCast, sub_add_sub_cancel] using hs

end
end Dubon2026
