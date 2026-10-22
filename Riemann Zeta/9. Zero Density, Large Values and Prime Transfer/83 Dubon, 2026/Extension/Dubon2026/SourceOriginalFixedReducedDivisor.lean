import Dubon2026.SourceOriginalReducedDivisorInvariance
import Dubon2026.SourceOriginalFiniteTorsionAction
import Dubon2026.SourceOriginalComplexTranslations

/-! DUB-17/18 -> arithmetic torsion surjectivity -> support descent.
Every actual complex n-torsion class has a reduced divisor fixed by the same
factorial power of every Qbar-linear complex constant automorphism. The bound
comes from the proved finite complex torsion; the unique reduced space and
fixed lifted arithmetic place make this an exact divisor equality.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ

theorem complexAut_fixes_lift_single (τ : ℂ ≃ₐ[Qbar] ℂ) (P : Place Qbar FQ) (r : ℤ) :
    originalArithmeticDivisorEquiv N (complexAutRestrict τ) (Finsupp.single (liftPlace N P) r) =
      Finsupp.single (liftPlace N P) r := by
  change Finsupp.equivMapDomain (originalArithmeticPlaceEquiv N (complexAutRestrict τ))
    (Finsupp.single (liftPlace N P) r) = _
  rw [Finsupp.equivMapDomain_single]
  change Finsupp.single (originalArithmeticPlace N (complexAutRestrict τ) (liftPlace N P)) r = _
  rw [complexAut_fixes_liftPlace]

theorem exists_original_fixed_reduced_divisor (n : ℕ) (hn : n ≠ 0)
    (D : Divisor.degZero (K := ℂ) (F := FC)) (hD : Pic0.mk D ∈ Pic0.torsion n)
    (P : Place Qbar FQ) :
    ∃ (r : ℕ) (f : FC), f ≠ 0 ∧
      ∀ τ : ℂ ≃ₐ[Qbar] ℂ,
        originalArithmeticDivisorEquiv N
          (complexAutRestrict τ ^ (Nat.card (Pic0.torsion (K := ℂ) (F := FC) n)).factorial)
          (D.val + (r : ℤ) • Finsupp.single (liftPlace N P) (1 : ℤ) + originalPrincipalDivisor N ℂ f) =
          D.val + (r : ℤ) • Finsupp.single (liftPlace N P) (1 : ℤ) + originalPrincipalDivisor N ℂ f := by
  obtain ⟨r, f, hf0, hf, huniq⟩ := exists_original_reduced_space N D.val D.property (liftPlace N P)
  refine ⟨r, f, hf0, fun τ => ?_⟩
  let m := (Nat.card (Pic0.torsion (K := ℂ) (F := FC) n)).factorial
  have hsingle : originalArithmeticDivisorEquiv N (complexAutRestrict τ ^ m)
      (Finsupp.single (liftPlace N P) (1 : ℤ)) = Finsupp.single (liftPlace N P) (1 : ℤ) := by
    rw [← map_pow]
    exact complexAut_fixes_lift_single N (τ ^ m) P 1
  apply original_reduced_divisor_fixed N _ hf0 hf huniq
  have he : originalArithmeticDivisorEquiv N (complexAutRestrict τ ^ m)
      (D.val + (r : ℤ) • Finsupp.single (liftPlace N P) (1 : ℤ)) -
      (D.val + (r : ℤ) • Finsupp.single (liftPlace N P) (1 : ℤ)) =
      originalArithmeticDivisorEquiv N (complexAutRestrict τ ^ m) D.val - D.val := by
    rw [map_add, map_zsmul, hsingle]
    abel
  rw [he]
  exact complex_torsion_divisor_factorial_principal N n hn (complexAutRestrict τ) D hD

end
end Dubon2026.SourceFunctionField.OriginalConstantField
