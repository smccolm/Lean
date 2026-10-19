import Dubon2026.ContinuousRepresentationCohomology

/-! A central scalar in the actual quotient detects nonzero continuous
cohomology on its kernel. This is the Sah argument needed by DUB-17's
twisted dual Selmer detection. It avoids a general finite-group H1
calculation when the residual image supplies the stated scalar element.
The scalar witness and quotient-kernel action remain explicit here. -/

namespace Dubon2026
noncomputable section

variable {K G H : Type} [Field K] [Group G] [Group H]
  (A : Rep K G) (c : groupCohomology.cocycles₁ A) (ψ : G →* H)

/-- A cocycle vanishing on the coefficient-trivial quotient kernel
has equal values on the literal fibers of the quotient homomorphism. -/
theorem cocycle_eq_of_quotient_eq
    (hker : ∀ τ, ψ τ = 1 → A.ρ τ = 1)
    (hc : ∀ τ, ψ τ = 1 → c τ = 0)
    {g h : G} (he : ψ g = ψ h) : c g = c h := by
  have hk : ψ (g * h⁻¹) = 1 := by rw [map_mul, map_inv, he, mul_inv_cancel]
  have heq : c ((g * h⁻¹) * h) = A.ρ (g * h⁻¹) (c h) + c (g * h⁻¹) :=
    (groupCohomology.mem_cocycles₁_iff _).mp c.property (g * h⁻¹) h
  simpa only [inv_mul_cancel_right, hker _ hk, Module.End.one_apply, hc _ hk,
    add_zero] using heq

/-- An actual central scalar in the quotient makes every kernel-vanishing
cocycle a coboundary, with its explicit original coefficient witness. -/
theorem cocycle_coboundary_of_quotient_central_scalar
    (hker : ∀ τ, ψ τ = 1 → A.ρ τ = 1)
    (hc : ∀ τ, ψ τ = 1 → c τ = 0)
    (σ : G) (hcentral : ∀ g, Commute (ψ σ) (ψ g))
    (μ : K) (hμ : μ ≠ 1) (hscalar : ∀ x : A, A.ρ σ x = μ • x) :
    ∀ g, c g = A.ρ g ((μ - 1)⁻¹ • c σ) - (μ - 1)⁻¹ • c σ := by
  intro g
  have he : c (σ * g) = c (g * σ) :=
    cocycle_eq_of_quotient_eq A c ψ hker hc (by
      simpa only [map_mul] using (hcentral g).eq)
  have hmul : ∀ g h, c (g * h) = A.ρ g (c h) + c g :=
    (groupCohomology.mem_cocycles₁_iff _).mp c.property
  rw [hmul, hmul, hscalar] at he
  have hh : (μ - 1) • c g = A.ρ g (c σ) - c σ := by
    rw [sub_smul, one_smul]
    exact sub_eq_sub_iff_add_eq_add.mpr he
  calc
    c g = (μ - 1)⁻¹ • ((μ - 1) • c g) := by
      rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hμ), one_smul]
    _ = (μ - 1)⁻¹ • (A.ρ g (c σ) - c σ) := by rw [hh]
    _ = _ := by rw [smul_sub, map_smul]

variable [TopologicalSpace K] [TopologicalSpace G]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul K A]

/-- A nonzero class in the native continuous H1 has an actual nonzero
cocycle value on the quotient kernel once its central scalar is supplied.
No finite-image H1-vanishing theorem is assumed. -/
theorem continuousH1_exists_nonzero_kernel_of_central_scalar
    (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
    (c : continuousRepresentationCocyclesOne A)
    (hker : ∀ τ, ψ τ = 1 → A.ρ τ = 1)
    (σ : G) (hcentral : ∀ g, Commute (ψ σ) (ψ g))
    (μ : K) (hμ : μ ≠ 1) (hscalar : ∀ x : A, A.ρ σ x = μ • x)
    (hc : (Submodule.Quotient.mk c : ContinuousRepresentationH1 A hA) ≠ 0) :
    ∃ τ, ψ τ = 1 ∧ c.val τ ≠ 0 := by
  by_contra hn
  push Not at hn
  have he := cocycle_coboundary_of_quotient_central_scalar A c.val ψ hker hn
    σ hcentral μ hμ hscalar
  apply hc
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨(μ - 1)⁻¹ • c.val σ, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  exact (he g).symm

end
end Dubon2026
