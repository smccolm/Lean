import Dubon2026.MatrixHopfModelCoefficientIdeal
import Dubon2026.MatrixComapQuotientHopfModel
import Dubon2026.MatrixAdicHopfFlatOpenQuotients
import Mathlib.RingTheory.Ideal.Quotient.Index

/-! # The actual closed model ideal classifies original coefficient maps by their kernels -/

namespace Dubon2026
noncomputable section
open Matrix
universe u

variable {R F K A B ι : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [CompactSpace A]
  [CommRing B] [IsLocalRing B] [WithIdeal B] [IsNoetherianRing B]
  [Finite (IsLocalRing.ResidueField B)] [T2Space B] [Fintype ι] [DecidableEq ι]

/-- The actual original coefficient-changed representation satisfies the complete positive-level model condition exactly when the same original coefficient map kills the literal closed model ideal. Original quotient finiteness, faithful comap quotient models, compact model closure and maximal-adic separation derive the criterion. -/
theorem matrixAdicHopfFlat_coefficient_iff_modelIdeal_le_ker
    (hB : (WithIdeal.i : Ideal B) = IsLocalRing.maximalIdeal B)
    (ρ : (K ≃ₐ[F] K) →* GeneralLinearGroup ι A)
    (I₀ : Ideal A) (hI₀ : IsOpen (I₀ : Set A))
    (m₀ : FiniteFreeHopfPointModel.{u,u,u,u,u} R F K (Multiplicative (ι → A ⧸ I₀))
      (matrixUnderlyingGroupAction (matrixIdealQuotientRepresentation I₀ ρ)))
    (f : A →+* B) (hf : Continuous f) :
    MatrixAdicHopfFlat R F K ((GeneralLinearGroup.map f).comp ρ) ↔
      matrixHopfModelCoefficientIdeal R F K ρ ≤ RingHom.ker f := by
  have hAdic : IsAdic (IsLocalRing.maximalIdeal B) := by
    rw [← hB]
    rfl
  have hlevel (n : ℕ) :
      matrixHopfModelCoefficientIdeal R F K ρ ≤
          (IsLocalRing.maximalIdeal B ^ n).comap f ↔
        Nonempty (FiniteFreeHopfPointModel.{u,u,u,u,u} R F K
          (Multiplicative (ι → B ⧸ IsLocalRing.maximalIdeal B ^ n))
          (matrixUnderlyingGroupAction
            (matrixIdealQuotientRepresentation (IsLocalRing.maximalIdeal B ^ n)
              ((GeneralLinearGroup.map f).comp ρ)))) := by
    letI : Finite (B ⧸ IsLocalRing.maximalIdeal B) :=
      inferInstanceAs (Finite (IsLocalRing.ResidueField B))
    letI : Finite (B ⧸ IsLocalRing.maximalIdeal B ^ n) :=
      Ideal.finite_quotient_pow (IsNoetherian.noetherian (IsLocalRing.maximalIdeal B)) n
    have hopen : IsOpen ((IsLocalRing.maximalIdeal B ^ n).comap f : Set A) :=
      ((isAdic_iff.mp hAdic).1 n).preimage hf
    exact (matrixHopfModelCoefficientIdeal_le_iff ρ I₀ hI₀ m₀ _ hopen).trans
      (matrixComapQuotientHopfModel_iff f (IsLocalRing.maximalIdeal B ^ n) ρ)
  constructor
  · intro hρ a ha
    change f a = 0
    by_contra hne
    have hzero : (0 : B) ∈ ({f a}ᶜ : Set B) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using Ne.symm hne
    obtain ⟨n, _hn, hn⟩ := hAdic.hasBasis_nhds_zero.mem_iff.mp
      (isClosed_singleton.isOpen_compl.mem_nhds hzero)
    have hmem : f a ∈ IsLocalRing.maximalIdeal B ^ (n + 1) :=
      (hlevel (n + 1)).mpr (hρ (n + 1) (Nat.zero_lt_succ n)) ha
    have hmem' : f a ∈ IsLocalRing.maximalIdeal B ^ n :=
      Ideal.pow_le_pow_right (Nat.le_succ n) hmem
    exact (hn hmem') (Set.mem_singleton (f a))
  · intro hker n _hn
    apply (hlevel n).mp
    intro a ha
    change f a ∈ IsLocalRing.maximalIdeal B ^ n
    have hz : f a = 0 := hker ha
    rw [hz]
    exact Ideal.zero_mem _

end
end Dubon2026
