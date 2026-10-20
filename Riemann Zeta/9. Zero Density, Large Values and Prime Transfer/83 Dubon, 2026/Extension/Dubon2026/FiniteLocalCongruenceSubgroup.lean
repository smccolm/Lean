import Dubon2026.FiniteSeparatedReductionPGroup
import Dubon2026.AdicMatrixProductEmbedding
import Dubon2026.MatrixCongruenceKernelImages
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-! # Finite arithmetic stabilizers in the original residual matrix kernel

For the small auxiliary level in DUB-17's unitary automorphic modules,
a finite subgroup of the actual principal congruence group has residue-
prime order. The existing original matrix power images and adic
separation discharge both inputs; no local pro-primary certificate is
assumed. Exclusion of prime torsion is the remaining smallness step.
-/

namespace Dubon2026

noncomputable section

open Matrix IsLocalRing

/-- Every finite subgroup of the original residual matrix kernel is a residue-prime group. -/
theorem finiteLocalCongruenceSubgroup_isPGroup
    {R ι : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : p.Prime)
    [CharP (ResidueField R) p]
    (H : Subgroup (GeneralLinearGroup ι R)) [Finite H]
    (hH : H ≤ MatrixCongruenceKernel (maximalIdeal R)) : IsPGroup p H := by
  letI : WithIdeal R := ⟨maximalIdeal R⟩
  letI : T2Space R :=
    (IsAdic.isHausdorff_iff (I := maximalIdeal R) rfl).mp inferInstance
  let π : ∀ n, H →* GeneralLinearGroup ι (R ⧸ maximalIdeal R ^ n) := fun n =>
    (GeneralLinearGroup.map (n := ι) (Ideal.Quotient.mk (maximalIdeal R ^ n))).comp H.subtype
  have hsep : ∀ x, (∀ n, π n x = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    apply adicMatrixReductionProduct_injective (R := R) (ι := ι)
    exact funext fun n => (hx n).trans ((adicMatrixReductionProduct (R := R) (ι := ι)).map_one ▸ rfl)
  have hmono : Antitone fun n => (π n).ker := by
    intro m n hmn x hx
    exact adicMatrixPowerReduction_kernel_antitone (R := R) (ι := ι) hmn hx
  have hpI : (p : R) ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff (p : R)).mp
    rw [map_natCast, CharP.cast_eq_zero]
  apply finiteSeparatedReduction_isPGroup π hsep hmono p
  intro n
  have hP := matrixCongruenceKernel_powerImage_isPGroup (ι := ι) (maximalIdeal R) hp hpI n
  apply hP.to_le
  rintro _ ⟨x, rfl⟩
  exact ⟨x.val, hH x.property, rfl⟩

end
end Dubon2026
