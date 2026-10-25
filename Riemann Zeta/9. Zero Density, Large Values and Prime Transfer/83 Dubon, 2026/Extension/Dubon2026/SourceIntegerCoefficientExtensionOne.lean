import Dubon2026.SourceIntegerCoefficientExtension

/-! DUB-17/18 -> original primitive Tate projector. The pure integral
Hecke tensor retains its original operator under coefficient extension. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

theorem integerCoefficientExtension_one_tmul
    {F K A B : Type*} [Field F] [Field K] [Ring A] [Ring B] [Algebra K B]
    (ι : F →+* K) (φ : A →+* B) (a : A) :
    integerCoefficientExtension ι φ ((1 : F) ⊗ₜ[ℤ] a) = φ a := by
  rw [integerCoefficientExtension_tmul, map_one, one_smul]

end
end Dubon2026
