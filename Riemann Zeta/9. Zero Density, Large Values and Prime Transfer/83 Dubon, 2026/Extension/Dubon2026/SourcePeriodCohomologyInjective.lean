import Dubon2026.SourcePeriodCohomologyBounded
import Dubon2026.SourceOriginalPeriodCohomology

/-! Injectivity of the original analytic period class in native group cohomology.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> modular Galois association -> analytic/etale comparison.
The genuine cohomological kernel gives a corrected nonpositive-weight modular
form. Pinned vanishing/constancy, periodicity and the already proved decay
kill the original Eichler integral, whose derivative recovers the cusp form.
The geometric comparison and continuous Galois action are still separate.
-/

namespace Dubon2026
noncomputable section
open Complex Filter Function Matrix.SpecialLinearGroup MvPolynomial OnePoint
open UpperHalfPlane hiding I
open scoped Real Nat MatrixGroups ModularForm

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {n : ℕ}

/-- A zero native analytic period class forces the original cusp form to vanish. -/
theorem sourcePeriodH1_eq_zero_imp (f : CuspForm (Γ.map (mapGL ℝ)) k)
    (hk : k = n + 2) (hf : sourcePeriodH1 f hk ∞ = 0) : f = 0 := by
  obtain ⟨L, hL⟩ := sourcePeriodH1_eq_zero_coboundary f hk hf
  let h := (Γ.map (mapGL ℝ)).strictWidthInfty
  have hh : 0 < h := (Γ.map (mapGL ℝ)).strictWidthInfty_pos
  have hΓ : h ∈ (Γ.map (mapGL ℝ)).strictPeriods :=
    (Γ.map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
  let E := sourceCorrectedEichlerModularForm f hk hh hΓ L hL
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ τ : UpperHalfPlane, E τ = c := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero E
      exact ⟨c, fun τ => congrFun hc τ⟩
    · have hz := ModularForm.isZero_of_neg_weight (by omega) E
      exact ⟨0, fun τ => by rw [hz]; rfl⟩
  let A : ℂ := (-2 * π * I) ^ (n + 1) / (n ! : ℂ)
  let p : Polynomial ℂ := -Polynomial.C A * sourcePeriodCorrectionPolynomial n L
  have hp (τ : UpperHalfPlane) :
      E τ = sourceEichlerIntegral h (n + 1) f τ + p.eval (τ : ℂ) := by
    change sourceEichlerIntegral h (n + 1) f τ -
      A * (sourcePeriodCorrectionPolynomial n L).eval (τ : ℂ) = _
    simp only [p, Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_C]
    ring
  have hpc := sourceEichlerIntegral_polynomial_eq_const hh (n + 1) f E p hp
    (fun τ => SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E τ hΓ)
  have hei : sourceEichlerIntegral h (n + 1) f = fun _ => c - p.eval I := by
    funext τ
    have hv : p.eval (τ : ℂ) = p.eval I := by
      simpa only [Polynomial.eval_C] using congrArg (Polynomial.eval (τ : ℂ)) hpc
    have ht := hc τ
    rw [hp, hv] at ht
    linear_combination ht
  have hlim := isZeroAtImInfty_sourceEichlerIntegral hh
    (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) n
  rw [hei] at hlim
  have hcz : c - p.eval I = 0 := tendsto_nhds_unique tendsto_const_nhds hlim
  have he0 : sourceEichlerIntegral h (n + 1) f = 0 := by
    simpa only [hcz] using hei
  have hd := sourceCuspForm_iterate_normalizedDerivOfComplex_eichlerIntegral f hh hΓ n
  rw [he0] at hd
  have hz : Derivative.normalizedDerivOfComplex (0 : UpperHalfPlane → ℂ) = 0 :=
    Derivative.normalizedDerivOfComplex_const 0
  rw [Function.iterate_fixed hz] at hd
  exact DFunLike.coe_injective hd.symm

/-- The actual linear period map into native H1 is injective at every rational base cusp. -/
theorem sourcePeriodCohomologyLinear_injective (hk : k = n + 2) (α : OnePoint ℚ) :
    Function.Injective (sourcePeriodCohomologyLinear (Γ := Γ) hk α) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  apply sourcePeriodH1_eq_zero_imp f hk
  change sourcePeriodH1 f hk α = 0 at hf
  rwa [sourcePeriodH1_base_independent f hk α ∞]

/-- The original Gamma0 cusp form is faithfully realized in analytic H1 at every source weight. -/
theorem sourceOriginalPeriodCohomology_injective (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k) :
    Function.Injective (sourceOriginalPeriodCohomology Q k hk) :=
  sourcePeriodCohomologyLinear_injective (by omega) ∞

/-- The class of an actual nonzero original cusp form is nonzero, without an assumed period witness. -/
theorem sourceOriginalPeriodCohomology_ne_zero (Q : ℕ) [NeZero Q] (k : ℤ) (hk : 2 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma0 Q).map (mapGL ℝ)) k) (hf : f ≠ 0) :
    sourceOriginalPeriodCohomology Q k hk f ≠ 0 := by
  intro hz
  apply hf
  exact (sourceOriginalPeriodCohomology_injective Q k hk)
    (hz.trans (map_zero (sourceOriginalPeriodCohomology Q k hk)).symm)

/-- Normalization of the actual primitive source form supplies a nonzero analytic H1 class. -/
theorem sourcePrimitive_periodCohomology_ne_zero {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) :
    sourceOriginalPeriodCohomology Q k hk f.toCuspForm ≠ 0 :=
  sourceOriginalPeriodCohomology_ne_zero Q k hk f.toCuspForm (primitiveCuspForm_ne_zero f)

end
end Dubon2026
