import Dubon2026.AdelicCyclicHeckeTrace

/-! # The original finite-adelic Hecke trace as a bounded Hilbert operator -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The literal finite Hecke sum of original bounded unitary Hilbert operators. -/
def adelicBoundedHeckeTrace (p : ℕ) [NeZero p] (hpN : p.Coprime N) :
    AdelicCyclicHilbert f →L[ℂ] AdelicCyclicHilbert f :=
  ∑ i : Option (ZMod p), adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding
    ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
      (finiteAdelicHeckeDiagonal p)⁻¹))

/-- The bounded trace has exactly the original algebraically defined Hecke action. -/
theorem adelicBoundedHeckeTrace_apply (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f) :
    adelicBoundedHeckeTrace f p hpN v = adelicHilbertHeckeTrace f p hpN v := by
  simp only [adelicBoundedHeckeTrace, adelicHilbertHeckeTrace, finiteAdelicHeckeTrace,
    ContinuousLinearMap.sum_apply, LinearMap.sum_apply]
  rfl

/-- The actual trace is bounded by its genuine p+1 unitary summands on every original Hilbert vector. -/
theorem adelicBoundedHeckeTrace_norm_le (p : ℕ) [NeZero p] (hpN : p.Coprime N)
    (v : AdelicCyclicHilbert f) :
    ‖adelicBoundedHeckeTrace f p hpN v‖ ≤ (p + 1 : ℝ) * ‖v‖ := by
  simp only [adelicBoundedHeckeTrace, ContinuousLinearMap.sum_apply]
  calc
    _ ≤ ∑ i : Option (ZMod p), ‖adelicCyclicHilbertOperator f (rationalAdelicFiniteGL2Embedding
      ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
        (finiteAdelicHeckeDiagonal p)⁻¹)) v‖ := norm_sum_le _ _
    _ = _ := by simp [adelicCyclicHilbertOperator_norm, Fintype.card_option, ZMod.card]

end
end Dubon2026
