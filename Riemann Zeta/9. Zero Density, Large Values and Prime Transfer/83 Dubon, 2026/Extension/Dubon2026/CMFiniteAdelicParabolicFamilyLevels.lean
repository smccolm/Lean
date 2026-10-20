import Dubon2026.CMFiniteAdelicParabolicLevels
import Dubon2026.FinitePlaceParabolicFamilyQuotient

/-! # The source auxiliary family inside the actual integral unitary group

Both levels are inverse images of the existing original local product
levels. The reduction map retains the existing source family quotient;
its kernel is exactly the lower actual global level. This supplies the
actual groups for DUB-17's unitary auxiliary module construction.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

variable (K : Type) [Field K] [NumberField K] [IsCMField K]
variable {S : Type*} (v : S → HeightOneSpectrum (𝓞 K)) (n : ℕ)

/-- Original simultaneous local integral evaluation of the actual unitary level. -/
def cmFiniteAdelicIntegralLocalFamilyMap (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    cmFiniteAdelicIntegralLevel K H →*
      (∀ s, (Matrix (Fin (n + 1)) (Fin (n + 1)) (Valued.integer ((v s).adicCompletion K)))ˣ) where
  toFun M s := cmFiniteAdelicIntegralLocalMap K H (v s) M
  map_one' := funext fun s => map_one (cmFiniteAdelicIntegralLocalMap K H (v s))
  map_mul' M N := funext fun s => map_mul (cmFiniteAdelicIntegralLocalMap K H (v s)) M N

/-- The actual original unitary upper auxiliary family level. -/
def cmFiniteAdelicParabolicFamilyLevelZero (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Subgroup (cmFiniteAdelicIntegralLevel K H) :=
  (finitePlaceParabolicFamilyLevelZero K v n).comap (cmFiniteAdelicIntegralLocalFamilyMap K v n H)

/-- The actual original unitary lower auxiliary family level. -/
def cmFiniteAdelicParabolicFamilyLevelOne (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Subgroup (cmFiniteAdelicIntegralLevel K H) :=
  (finitePlaceParabolicFamilyLevelOne K v n).comap (cmFiniteAdelicIntegralLocalFamilyMap K v n H)

/-- The original lower unitary family level is contained in the original upper level. -/
theorem cmFiniteAdelicParabolicFamilyLevelOne_le (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    cmFiniteAdelicParabolicFamilyLevelOne K v n H ≤ cmFiniteAdelicParabolicFamilyLevelZero K v n H :=
  Subgroup.comap_mono (finitePlaceParabolicFamilyLevelOne_le K v n)

/-- Original evaluation restricted to the original upper unitary family level. -/
def cmFiniteAdelicParabolicFamilyLocalMap (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    cmFiniteAdelicParabolicFamilyLevelZero K v n H →* finitePlaceParabolicFamilyLevelZero K v n :=
  ((cmFiniteAdelicIntegralLocalFamilyMap K v n H).comp
    (cmFiniteAdelicParabolicFamilyLevelZero K v n H).subtype).codRestrict _ (fun M => M.property)

/-- The actual global auxiliary level reduces to the existing original local family quotient. -/
def cmFiniteAdelicParabolicFamilyReduction (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    cmFiniteAdelicParabolicFamilyLevelZero K v n H →* FinitePlaceParabolicFamilyQuotient K v n :=
  (QuotientGroup.mk' ((finitePlaceParabolicFamilyLevelOne K v n).subgroupOf
    (finitePlaceParabolicFamilyLevelZero K v n))).comp (cmFiniteAdelicParabolicFamilyLocalMap K v n H)

/-- The lower actual global level is exactly the kernel of original family quotient reduction. -/
theorem cmFiniteAdelicParabolicFamilyReduction_kernel
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (cmFiniteAdelicParabolicFamilyLevelOne K v n H).subgroupOf
      (cmFiniteAdelicParabolicFamilyLevelZero K v n H) =
        (cmFiniteAdelicParabolicFamilyReduction K v n H).ker := by
  ext M
  exact (QuotientGroup.eq_one_iff (N := (finitePlaceParabolicFamilyLevelOne K v n).subgroupOf
    (finitePlaceParabolicFamilyLevelZero K v n)) (cmFiniteAdelicParabolicFamilyLocalMap K v n H M)).symm

/-- The original lower unitary family level is normal inside the upper level. -/
instance cmFiniteAdelicParabolicFamilyLevelOne_normal
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    ((cmFiniteAdelicParabolicFamilyLevelOne K v n H).subgroupOf
      (cmFiniteAdelicParabolicFamilyLevelZero K v n H)).Normal := by
  rw [cmFiniteAdelicParabolicFamilyReduction_kernel]
  infer_instance

end
end Dubon2026
