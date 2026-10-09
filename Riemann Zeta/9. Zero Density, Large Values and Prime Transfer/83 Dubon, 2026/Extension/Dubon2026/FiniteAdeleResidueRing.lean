import Dubon2026.FiniteAdeleIntegralResidue

/-! # The genuine residue ring map on integral finite adeles -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain

/-- The actual finite-adelic level ideal is closed under subtraction. -/
theorem finiteAdeleLevelMultiple_sub (N : ℕ) {x y : FiniteAdeleRing ℤ ℚ}
    (hx : finiteAdeleLevelMultiple N x) (hy : finiteAdeleLevelMultiple N y) :
    finiteAdeleLevelMultiple N (x - y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a - b, finiteAdeleIntegerSubring.sub_mem ha hb, (mul_sub _ _ _).symm⟩

/-- Multiplication by an actual integral finite adele preserves the genuine level ideal. -/
theorem finiteAdeleLevelMultiple_mul_left (N : ℕ) {x y : FiniteAdeleRing ℤ ℚ}
    (hx : x ∈ finiteAdeleIntegerSubring) (hy : finiteAdeleLevelMultiple N y) :
    finiteAdeleLevelMultiple N (x * y) := by
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨x * b, finiteAdeleIntegerSubring.mul_mem hx hb, by ring⟩

/-- Two integer representatives of an actual finite-adelic residue have exactly the same ordinary residue class. -/
theorem finiteAdele_integer_representative_unique (N : ℕ) [NeZero N]
    (x : FiniteAdeleRing ℤ ℚ) (n m : ℤ)
    (hn : finiteAdeleLevelMultiple N (x - n)) (hm : finiteAdeleLevelMultiple N (x - m)) :
    (n : ZMod N) = (m : ZMod N) := by
  have hs := finiteAdeleLevelMultiple_sub N hn hm
  have he : (x - n) - (x - m) = ((m - n : ℤ) : FiniteAdeleRing ℤ ℚ) := by
    push_cast
    ring
  rw [he, finiteAdeleLevelMultiple_int_iff] at hs
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub n m N).mpr hs

/-- An actual integer representative supplied by proved rational density and the original open level ideal. -/
def finiteAdeleResidueInteger (N : ℕ) [NeZero N] (x : finiteAdeleIntegerSubring) : ℤ :=
  Classical.choose (finiteAdele_integral_integer_representative N x.val x.property)

/-- The chosen original integer represents the actual finite adele modulo its genuine level ideal. -/
theorem finiteAdeleResidueInteger_spec (N : ℕ) [NeZero N] (x : finiteAdeleIntegerSubring) :
    finiteAdeleLevelMultiple N (x.val - finiteAdeleResidueInteger N x) :=
  Classical.choose_spec (finiteAdele_integral_integer_representative N x.val x.property)

/-- The actual residue class is independent of every permissible original integer representative. -/
theorem finiteAdeleResidueInteger_eq_class (N : ℕ) [NeZero N] (x : finiteAdeleIntegerSubring)
    (n : ℤ) (hn : finiteAdeleLevelMultiple N (x.val - n)) :
    (finiteAdeleResidueInteger N x : ZMod N) = (n : ZMod N) :=
  finiteAdele_integer_representative_unique N x.val _ n (finiteAdeleResidueInteger_spec N x) hn

/-- The original integral finite adeles have their genuine ordinary residue ring map modulo any positive integer. -/
def finiteAdeleResidue (N : ℕ) [NeZero N] : finiteAdeleIntegerSubring →+* ZMod N where
  toFun x := (finiteAdeleResidueInteger N x : ZMod N)
  map_zero' := by
    have h := finiteAdeleResidueInteger_eq_class N 0 0 ⟨0, by simp, by simp⟩
    simpa only [Int.cast_zero] using h
  map_one' := by
    have h := finiteAdeleResidueInteger_eq_class N 1 1 ⟨0, by simp, by simp⟩
    simpa only [Int.cast_one] using h
  map_add' x y := by
    rw [← Int.cast_add]
    apply finiteAdeleResidueInteger_eq_class
    have h := finiteAdeleLevelMultiple_add N (finiteAdeleResidueInteger_spec N x)
      (finiteAdeleResidueInteger_spec N y)
    convert h using 1
    push_cast
    ring
  map_mul' x y := by
    rw [← Int.cast_mul]
    apply finiteAdeleResidueInteger_eq_class
    have h := finiteAdeleLevelMultiple_add N
      (finiteAdeleLevelMultiple_mul_left N x.property (finiteAdeleResidueInteger_spec N y))
      (finiteAdeleLevelMultiple_mul_left N
        (show (finiteAdeleResidueInteger N y : FiniteAdeleRing ℤ ℚ) ∈ finiteAdeleIntegerSubring by simp)
        (finiteAdeleResidueInteger_spec N x))
    convert h using 1
    push_cast
    ring

/-- The genuine residue map sends an original integer to its ordinary residue class. -/
theorem finiteAdeleResidue_intCast (N : ℕ) [NeZero N] (n : ℤ) :
    finiteAdeleResidue N (n : finiteAdeleIntegerSubring) = (n : ZMod N) :=
  map_intCast (finiteAdeleResidue N) n

/-- The original finite-adelic residue map is onto the entire ordinary finite residue ring. -/
theorem finiteAdeleResidue_surjective (N : ℕ) [NeZero N] : Function.Surjective (finiteAdeleResidue N) := by
  intro r
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective r
  exact ⟨n, (finiteAdeleResidue_intCast N n).trans hn⟩

/-- An original residue equals a prescribed integer precisely when their actual adelic difference lies in the genuine level ideal. -/
theorem finiteAdeleResidue_eq_intCast_iff (N : ℕ) [NeZero N] (x : finiteAdeleIntegerSubring) (n : ℤ) :
    finiteAdeleResidue N x = (n : ZMod N) ↔ finiteAdeleLevelMultiple N (x.val - n) := by
  constructor
  · intro h
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (finiteAdeleResidueInteger N x) n N).mp h
    have hi := (finiteAdeleLevelMultiple_int_iff N (n - finiteAdeleResidueInteger N x)).mpr hd
    have hs := finiteAdeleLevelMultiple_sub N (finiteAdeleResidueInteger_spec N x) hi
    convert hs using 1
    push_cast
    ring
  · exact finiteAdeleResidueInteger_eq_class N x n

/-- The genuine residue kernel is exactly the original finite-adelic level ideal. -/
theorem finiteAdeleResidue_eq_zero_iff (N : ℕ) [NeZero N] (x : finiteAdeleIntegerSubring) :
    finiteAdeleResidue N x = 0 ↔ finiteAdeleLevelMultiple N x.val := by
  simpa only [Int.cast_zero, sub_zero] using finiteAdeleResidue_eq_intCast_iff N x 0

end
end Dubon2026
