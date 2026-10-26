import Dubon2026.SourceResidualWittCoefficients
import Mathlib.RingTheory.WittVector.Compare

/-! DUB-17/18 -> arithmetic automorphy -> the actual fixed-determinant
residual deformation problem. The native Witt/p-adic comparison gives
the characteristic-zero scalar map; its literal reduction is the
original characteristic-p scalar map. This is the coefficient bridge
for the actual p-adic cyclotomic determinant, not a finite character lift. -/
namespace Dubon2026
noncomputable section
open IsLocalRing

variable (p : ℕ) [Fact p.Prime]

theorem sourcePadicInt_charP_map
    {K : Type} [CommRing K] [CharP K p]
    (φ : ℤ_[p] →+* K) (x : ℤ_[p]) :
    φ x = ZMod.castHom (dvd_refl p) K (PadicInt.toZMod x) := by
  have hx := PadicInt.toZMod_spec x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hx
  obtain ⟨y, hy⟩ := hx
  have he := congrArg φ hy
  rw [map_sub, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul,
    sub_eq_zero] at he
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  simpa only [ZMod.cast_eq_val, map_natCast] using he

variable (K : Type) [Field K] [Finite K] [CharP K p]

/-- The native characteristic-zero scalar map into the actual Witt coefficient ring. -/
def sourcePadicWittCoefficient : ℤ_[p] →+* WittVector p K :=
  (WittVector.map (ZMod.castHom (dvd_refl p) K)).comp (WittVector.fromPadicInt p)

omit [Finite K] in
theorem sourcePadicWittCoefficient_injective :
    Function.Injective (sourcePadicWittCoefficient p K) :=
  (WittVector.map_injective _ (RingHom.injective _)).comp
    (WittVector.equiv p).symm.injective

theorem sourcePadicWittCoefficient_residue (x : ℤ_[p]) :
    sourceResidualWittResidueEquiv p K
      (residue (WittVector p K) (sourcePadicWittCoefficient p K x)) =
      ZMod.castHom (dvd_refl p) K (PadicInt.toZMod x) := by
  rw [sourceResidualWittResidueEquiv_residue]
  exact sourcePadicInt_charP_map p
    ((WittVector.constantCoeff : WittVector p K →+* K).comp
      (sourcePadicWittCoefficient p K)) x

end
end Dubon2026
