import Dubon2026.MatrixHopfModelCoefficientIdeal
import Dubon2026.MatrixAdicHopfFlatOpenQuotients

/-! # The actual local model condition is vanishing of its original closed coefficient ideal -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [IsLocalRing A] [WithIdeal A] [CompactSpace A] [T2Space A]
  [Fintype ι] [DecidableEq ι]

/-- For the actual compact Hausdorff maximal-adic coefficient ring, the complete original local model condition holds exactly when its literal closed model ideal vanishes. An existing original open quotient model supplies the nonempty model family; neighborhood separation and genuine model closure prove both implications. -/
theorem matrixAdicHopfFlat_iff_modelCoefficientIdeal_eq_bot
    (hA : (WithIdeal.i : Ideal A) = IsLocalRing.maximalIdeal A)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ))) :
    MatrixAdicHopfFlat R F K ρ ↔ matrixHopfModelCoefficientIdeal R F K ρ = ⊥ := by
  have hAdic : IsAdic (IsLocalRing.maximalIdeal A) := by
    rw [← hA]
    rfl
  constructor
  · intro hρ
    apply le_antisymm _ bot_le
    intro x hx
    apply Ideal.mem_bot.mpr
    by_contra hne
    have hzero : (0 : A) ∈ ({x}ᶜ : Set A) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using Ne.symm hne
    obtain ⟨n, _hn, hn⟩ := hAdic.hasBasis_nhds_zero.mem_iff.mp
      (isClosed_singleton.isOpen_compl.mem_nhds hzero)
    have hopen := (isAdic_iff.mp hAdic).1 n
    have hmodel := matrixAdicHopfFlat_openIdealModel hA ρ hρ
      (IsLocalRing.maximalIdeal A ^ n) hopen
    have hle := (matrixHopfModelCoefficientIdeal_le_iff ρ I₀ hI₀ m₀
      (IsLocalRing.maximalIdeal A ^ n) hopen).mpr hmodel
    exact (hn (hle hx)) (Set.mem_singleton x)
  · intro hzero
    apply (matrixAdicHopfFlat_iff_openQuotients hA ρ).mpr
    intro U hU
    apply (matrixHopfModelCoefficientIdeal_le_iff ρ I₀ hI₀ m₀ U hU).mp
    rw [hzero]
    exact bot_le

end
end Dubon2026
