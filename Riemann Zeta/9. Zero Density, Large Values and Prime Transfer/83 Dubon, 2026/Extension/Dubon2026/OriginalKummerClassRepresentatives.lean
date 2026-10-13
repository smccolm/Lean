import Dubon2026.OriginalKummerGaloisExponent
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Original power classes and actual roots in their generated field

Representatives belong to the original subgroup, and every chosen radical
lies in the original generated field. The exact representative equations
will make finite power classes detect original Galois automorphisms,
discharging finiteness in the global S-unit Kummer dependency of DUB-17.
-/

namespace Dubon2026
noncomputable section
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- The actual image of the prescribed base units in the original nth-power quotient. -/
def originalKummerClassSubgroup (n : ℕ) (Δ : Subgroup Kˣ) :
    Subgroup (Kˣ ⧸ (powMonoidHom (α := Kˣ) n).range) :=
  Δ.map (QuotientGroup.mk' _)

/-- Choose an original prescribed unit representing the same actual field power class. -/
def originalKummerClassRepresentative (n : ℕ) (Δ : Subgroup Kˣ)
    (c : originalKummerClassSubgroup n Δ) : Δ :=
  ⟨c.property.choose, c.property.choose_spec.1⟩

/-- The representative maps to the original class, not a separately chosen class. -/
theorem originalKummerClassRepresentative_spec (n : ℕ) (Δ : Subgroup Kˣ)
    (c : originalKummerClassSubgroup n Δ) :
    QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range
      (originalKummerClassRepresentative n Δ c).val = c.val :=
  c.property.choose_spec.2

/-- An actual root of the chosen original representative, inside the actual generated field. -/
def originalKummerClassRoot [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n) (Δ : Subgroup Kˣ)
    (c : originalKummerClassSubgroup n Δ) : (originalKummerRadicalField (Ω := Ω) n Δ)ˣ :=
  (originalKummerRadicalField_exists_root n hn Δ (originalKummerClassRepresentative n Δ c)).choose

/-- The chosen root satisfies the exact original representative equation. -/
theorem originalKummerClassRoot_pow [IsAlgClosed Ω] (n : ℕ) (hn : 0 < n)
    (Δ : Subgroup Kˣ) (c : originalKummerClassSubgroup n Δ) :
    originalKummerClassRoot (Ω := Ω) n hn Δ c ^ n =
      Units.map (algebraMap K (originalKummerRadicalField (Ω := Ω) n Δ)).toMonoidHom
        (originalKummerClassRepresentative n Δ c).val :=
  (originalKummerRadicalField_exists_root n hn Δ (originalKummerClassRepresentative n Δ c)).choose_spec

/-- The prescribed radical quotient is exactly its actual image in the original field power quotient. -/
def originalKummerRadicalQuotientEquivClasses (n : ℕ) (Δ : Subgroup Kˣ) :
    Δ ⧸ ((powMonoidHom (α := Kˣ) n).range).subgroupOf Δ ≃*
      originalKummerClassSubgroup n Δ := by
  let f := (QuotientGroup.mk' (powMonoidHom (α := Kˣ) n).range).comp Δ.subtype
  have hk : f.ker = ((powMonoidHom (α := Kˣ) n).range).subgroupOf Δ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_subtype]
  have hr : f.range = originalKummerClassSubgroup n Δ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hr))

end
end Dubon2026
