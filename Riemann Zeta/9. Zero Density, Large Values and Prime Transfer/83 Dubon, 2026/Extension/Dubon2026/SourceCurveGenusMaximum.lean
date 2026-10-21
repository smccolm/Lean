import Dubon2026.SourceCurvePoleDimensionGrowth

/-! DUB-17/18 -> function-field Riemann--Roch -> stabilization of the
global index. The bounded integer-valued degree-minus-dimension function
attains its maximum and is constant above a maximizing divisor. The
auxiliary parameter is not yet identified with the canonical genus.
The structure follows Def_AlgebraicCurve_AdelicIndex and the maximum
argument uses pinned integer order completeness.
-/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- A divisor attaining the global degree-minus-dimension maximum. -/
structure RiemannGenusReachedAt (γ : ℤ) (D₀ : Divisor K F) : Prop where
  /-- The actual divisor space is finite-dimensional. -/
  finite : FiniteDimensional K (LSpace D₀)
  /-- The maximum value determines the auxiliary index parameter. -/
  eq : Divisor.degree D₀ - (ell D₀ : ℤ) = γ - 1
  /-- Every divisor has degree-minus-dimension at most this value. -/
  isMax : ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1

theorem exists_riemannGenusReachedAt_of_bounded
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    (hbdd : RiemannGenusBounded K F) :
    ∃ (γ : ℤ) (D₀ : Divisor K F), RiemannGenusReachedAt γ D₀ := by
  obtain ⟨γ, hγ⟩ := hbdd
  obtain ⟨M, ⟨D₀, hD₀⟩, hMmax⟩ :=
    Int.exists_greatest_of_bdd
      (P := fun n => ∃ D : Divisor K F, Divisor.degree D - ell D = n)
      ⟨γ, fun n ⟨D, hD⟩ => hD ▸ hγ D⟩
      ⟨Divisor.degree (0 : Divisor K F) - ell (0 : Divisor K F), 0, rfl⟩
  refine ⟨M + 1, D₀, finite_lSpace D₀, ?_, ?_⟩
  · rw [hD₀]
    ring
  · intro D
    have := hMmax (Divisor.degree D - ell D) ⟨D, rfl⟩
    linarith

theorem RiemannGenusReachedAt.eq_of_ge
    [∀ v : Place K F, Module.Finite K v.ResidueField]
    [FiniteDimensional K (LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {D : Divisor K F} (hD : D₀ ≤ D) :
    Divisor.degree D - ell D = γ - 1 := by
  haveI := finite_lSpace D
  have hge : Divisor.degree D₀ - (ell D₀ : ℤ) ≤ Divisor.degree D - ell D := by
    have := ell_sub_ell_le_degree_sub_degree hD
    linarith
  exact le_antisymm (h.isMax D) (h.eq ▸ hge)

end
end Dubon2026.SourceCurve
