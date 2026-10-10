import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-! # Actual localization images remain in a unit-reflecting coefficient subalgebra -/

namespace Dubon2026
noncomputable section

variable {O R L A : Type*} [CommRing O] [CommRing R] [CommRing L] [CommRing A]
  [Algebra O A] [Algebra R L]

/-- The image of every genuine localization fraction belongs to the original coefficient subalgebra when its original numerator and denominator do and that subalgebra reflects units. -/
theorem localization_image_mem_subalgebra (M : Submonoid R) [IsLocalization M L]
    (S : Subalgebra O A) (f : L →+* A)
    (hbase : ∀ r : R, f (algebraMap R L r) ∈ S)
    (hunit : ∀ x : S, IsUnit (x : A) → IsUnit x) (x : L) : f x ∈ S := by
  obtain ⟨⟨r, m⟩, hm⟩ := IsLocalization.surj M x
  let b : S := ⟨f (algebraMap R L m), hbase m⟩
  have hb : IsUnit b := hunit b ((IsLocalization.map_units L m).map f)
  obtain ⟨u, hu⟩ := hb
  have huval : (u.val : A) = f (algebraMap R L m) := congrArg Subtype.val hu
  have hcancel : (u.val : A) * (u.inv : A) = 1 :=
    congrArg (fun z : S => (z : A)) u.val_inv
  have heq : f x = f (algebraMap R L r) * (u.inv : A) := by
    calc
      f x = (f x * (u.val : A)) * (u.inv : A) := by
        rw [mul_assoc, hcancel, mul_one]
      _ = f (algebraMap R L r) * (u.inv : A) := by
        rw [huval, ← map_mul, hm]
  rw [heq]
  exact S.mul_mem (hbase r) u.inv.property

end
end Dubon2026
