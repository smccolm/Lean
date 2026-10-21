import Dubon2026.SourcePrimePowerChainExtension

/-! DUB-17/18 -> numerical modular genus -> all-level degree
-> prime-power nonmembership. Leading Laurent coefficients distinguish
the spread root from the smaller expansion range in the source tower
argument. These facts serve that contradiction, without any growth or
asymptotic substitute for actual Laurent-series equality.
-/
namespace Dubon2026.SourceFunctionField.PrimePowerNonmembership
noncomputable section
open PrimeDegreeAux
variable {K : Type*} [Field K]

theorem TS_not_mem_range_qExpand {r e : ℕ} [NeZero r] [NeZero e]
    (hre : ¬ (r : ℤ) ∣ (e : ℤ)) (w : Kˣ) :
    TS K e w ∉ (qExpand K r).range := by
  intro hmem
  obtain ⟨z, hz⟩ := RingHom.mem_range.mp hmem
  have h1 := TS_coeff_neg (K := K) e w
  have h2 : (qExpand K r z).coeff (-(e : ℤ)) = 0 :=
    qExpand_coeff_of_not_dvd r z (by rwa [dvd_neg])
  rw [hz, h1] at h2
  exact (w⁻¹ : Kˣ).ne_zero h2

theorem range_qExpand_congr {A A' : ℕ} [NeZero A] [NeZero A'] (h : A = A') :
    (qExpand K A).range = (qExpand K A').range := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w, (qExpand_congr h w).symm⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, qExpand_congr h w⟩

end
end Dubon2026.SourceFunctionField.PrimePowerNonmembership
