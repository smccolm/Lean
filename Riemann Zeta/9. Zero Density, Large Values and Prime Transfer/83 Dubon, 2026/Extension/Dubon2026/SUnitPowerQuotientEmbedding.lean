import Dubon2026.SUnitPowerSaturation
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # The actual S-unit power quotient inside the original field power quotient

The inclusion is injective because actual field roots of S-units are S-units.
It identifies the finite S-unit quotient with the original radical subgroup
used to build the global Kummer extension for the DUB-17 norm-index route.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual inclusion of original S-units induces the original nth-power class map. -/
def sUnitPowerQuotientToField (S : Set (HeightOneSpectrum R)) (n : ℕ) :
    S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range →*
      Kˣ ⧸ (powMonoidHom (α := Kˣ) n).range :=
  QuotientGroup.map _ _ (S.unit K).subtype (by
    rintro x ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩)

/-- The induced power-class map retains the original representative. -/
theorem sUnitPowerQuotientToField_mk (S : Set (HeightOneSpectrum R))
    (n : ℕ) (x : S.unit K) :
    sUnitPowerQuotientToField S n (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ x.val := rfl

/-- No nontrivial original S-unit power class is killed by the original field inclusion. -/
theorem sUnitPowerQuotientToField_injective (S : Set (HeightOneSpectrum R))
    (n : ℕ) (hn : n ≠ 0) : Function.Injective (sUnitPowerQuotientToField (K := K) S n) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  induction x using QuotientGroup.induction_on with
  | H y =>
    change QuotientGroup.mk' _ y.val = 1 at hx
    change QuotientGroup.mk' _ y = 1
    apply (QuotientGroup.eq_one_iff y).mpr
    exact (sUnit_mem_power_range_iff S n hn y).mpr ((QuotientGroup.eq_one_iff y.val).mp hx)

/-- The original finite S-unit power quotient is exactly its actual image in the field quotient. -/
def sUnitPowerQuotientEquivFieldImage (S : Set (HeightOneSpectrum R)) (n : ℕ) (hn : n ≠ 0) :
    S.unit K ⧸ (powMonoidHom (α := S.unit K) n).range ≃*
      (sUnitPowerQuotientToField (K := K) S n).range :=
  MulEquiv.ofBijective (sUnitPowerQuotientToField (K := K) S n).rangeRestrict
    ⟨fun _ _ h => sUnitPowerQuotientToField_injective S n hn (congrArg Subtype.val h),
      (sUnitPowerQuotientToField (K := K) S n).rangeRestrict_surjective⟩

end
end Dubon2026
