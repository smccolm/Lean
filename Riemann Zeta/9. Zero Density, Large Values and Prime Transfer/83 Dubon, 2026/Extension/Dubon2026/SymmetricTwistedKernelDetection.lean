import Dubon2026.CocycleCentralScalarKernel
import Dubon2026.ResidualGL2CentralScalar
import Dubon2026.TraceCocycleKernelDetection

/-! The original higher symmetric-power twisted cohomology is detected
on the joint residual/character kernel. This discharges the nonzero
kernel-value obligation in DUB-17's regular auxiliary-prime chain, from
actual rank-two SL2 image containment and a nontrivial squared character.
The commuting trace test and the modular image theorem remain required. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- A scalar residual matrix acts on the original twisted adjoint by
the actual character scalar, in every dimension. -/
theorem matrixTraceZeroCharacterRep_apply_of_scalarGL
    {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field K]
    (ρ : G →* GeneralLinearGroup ι K) (χ : G →* K)
    (σ : G) (u : Kˣ) (hσ : ρ σ = GeneralLinearGroup.scalar ι u)
    (X : matrixTraceZeroSubmodule ι K) :
    (matrixTraceZeroCharacterRep ρ χ).ρ σ X = χ σ • X := by
  have hval : (ρ σ).val = (u : K) • (1 : Matrix ι ι K) := by
    rw [hσ]
    ext i j
    simp [GeneralLinearGroup.scalar, Matrix.scalar_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
  have hcomm : (ρ σ).val * X.val = X.val * (ρ σ).val := by
    rw [hval, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hfix := matrixTraceZeroAdjoint_fixed_of_commute ρ σ X hcomm
  change χ σ • (matrixTraceZeroAdjointRep ρ).ρ σ X = χ σ • X
  rw [hfix]

/-- The scalar witness is constructed from the original rank-two image.
Every nonzero native continuous twisted H1 class has a nonzero cocycle
value where both the original rank-two representation and the specified
commutative character are trivial. -/
theorem symmetricTwistedH1_exists_nonzero_joint_kernel
    {G B K : Type} [Group G] [CommGroup B] [Field K]
    [NeZero (2 : K)] [NeZero (3 : K)]
    [TopologicalSpace G] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) (ρ : G →* GeneralLinearGroup (Fin 2) K) (χ : G →* B) (ω : B →* K)
    (himage : (SpecialLinearGroup.toGL (n := Fin 2) (R := K)).range ≤ ρ.range)
    (g : G) (hg : ω (χ g) ^ 2 ≠ 1)
    (hA : Continuous (fun z : G × matrixTraceZeroSubmodule (Fin (n + 1)) K =>
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)).ρ z.1 z.2))
    (c : continuousRepresentationCocyclesOne
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)))
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ((homogeneousSymmetricGL n).comp ρ) (ω.comp χ)) hA) ≠ 0) :
    ∃ τ, ρ τ = 1 ∧ χ τ = 1 ∧ c.val τ ≠ 0 := by
  let R := (homogeneousSymmetricGL n).comp ρ
  let ξ := ω.comp χ
  let A := matrixTraceZeroCharacterRep R ξ
  let ψ := ρ.prod χ
  obtain ⟨σ, hχσ, hρσ⟩ := residualGL2_exists_scalar_character_square ρ χ himage g
  have hscalar : R σ = GeneralLinearGroup.scalar (Fin (n + 1))
      (GeneralLinearGroup.det (ρ g) ^ n) := by
    change homogeneousSymmetricGL n (ρ σ) = _
    rw [hρσ, homogeneousSymmetricGL_scalar_ring]
  have hcentral : ∀ x, Commute (ψ σ) (ψ x) := by
    intro x
    change (ρ σ, χ σ) * (ρ x, χ x) = (ρ x, χ x) * (ρ σ, χ σ)
    apply Prod.ext
    · change ρ σ * ρ x = ρ x * ρ σ
      rw [hρσ]
      exact (generalLinear_scalar_commute _ _).eq
    · exact mul_comm _ _
  have hker : ∀ τ, ψ τ = 1 → A.ρ τ = 1 := by
    intro τ hτ
    have hr : ρ τ = 1 := congrArg Prod.fst hτ
    have ht : χ τ = 1 := congrArg Prod.snd hτ
    have hR : R τ = 1 := by change homogeneousSymmetricGL n (ρ τ) = 1; rw [hr, map_one]
    have hξ : ξ τ = 1 := by change ω (χ τ) = 1; rw [ht, map_one]
    apply matrixTraceZeroCharacterRep_eq_one_of_scalar R ξ τ hξ 1
    rw [hR]
    simp
  have hξσ : ξ σ ≠ 1 := by
    change ω (χ σ) ≠ 1
    rw [hχσ, map_pow]
    exact hg
  obtain ⟨τ, hτ, hne⟩ := continuousH1_exists_nonzero_kernel_of_central_scalar
    A ψ hA c hker σ hcentral (ξ σ) hξσ
    (matrixTraceZeroCharacterRep_apply_of_scalarGL R ξ σ _ hscalar) hc
  exact ⟨τ, congrArg Prod.fst hτ, congrArg Prod.snd hτ, hne⟩

end
end Dubon2026
