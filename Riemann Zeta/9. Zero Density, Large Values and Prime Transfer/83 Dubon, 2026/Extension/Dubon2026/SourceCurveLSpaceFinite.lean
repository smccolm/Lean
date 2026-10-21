import Dubon2026.SourceCurveLSpaceFiniteStep

/-! DUB-17/18 -> regular differential dimension -> finite canonical-divisor
space. Iterate the proved single-pole residue-map step over the positive
part of the actual finite divisor. No adelic finiteness or Riemann--Roch
premise is used.
-/
namespace Dubon2026.SourceCurve
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable [∀ v : Place K F, Module.Finite K v.ResidueField]

theorem finite_lSpace_add_single_nat (D : Divisor K F) (P : Place K F) (n : ℕ)
    [Module.Finite K (LSpace D)] :
    Module.Finite K (LSpace (Finsupp.single P (n : ℤ) + D)) := by
  induction n with
  | zero =>
      rw [Nat.cast_zero, Finsupp.single_zero, zero_add]
      infer_instance
  | succ n ih =>
      have he : Finsupp.single P ((n + 1 : ℕ) : ℤ) + D - Finsupp.single P 1 =
          Finsupp.single P (n : ℤ) + D := by
        push_cast
        rw [Finsupp.single_add]
        abel
      haveI : Module.Finite K
          (LSpace (Finsupp.single P ((n + 1 : ℕ) : ℤ) + D - Finsupp.single P 1)) :=
        he.symm ▸ ih
      exact finite_lSpace_of_sub_single _ P

theorem finite_lSpace_of_nat_divisor [Module.Finite K (LSpace (0 : Divisor K F))]
    (D : Place K F →₀ ℕ) :
    Module.Finite K (LSpace (D.mapRange (fun n : ℕ => (n : ℤ)) (by rfl))) := by
  induction D using Finsupp.induction with
  | zero => simpa using (inferInstance : Module.Finite K (LSpace (0 : Divisor K F)))
  | single_add P n D _ _ ih =>
      rw [Finsupp.mapRange_add (fun x y => Nat.cast_add x y), Finsupp.mapRange_single]
      haveI := ih
      exact finite_lSpace_add_single_nat _ P n

theorem finite_lSpace [Module.Finite K (LSpace (0 : Divisor K F))]
    (D : Divisor K F) : Module.Finite K (LSpace D) := by
  let Dpos : Place K F →₀ ℕ := D.mapRange Int.toNat (by rfl)
  let E : Divisor K F := Dpos.mapRange (fun n : ℕ => (n : ℤ)) (by rfl)
  have hDE : D ≤ E := by
    intro v
    change D v ≤ ((D v).toNat : ℤ)
    exact Int.self_le_toNat (D v)
  haveI : Module.Finite K (LSpace E) := finite_lSpace_of_nat_divisor Dpos
  exact Module.Finite.of_injective (Submodule.inclusion (lSpace_mono hDE))
    (Submodule.inclusion_injective (lSpace_mono hDE))

end
end Dubon2026.SourceCurve
