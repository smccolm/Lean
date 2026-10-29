import Dubon2026.SourceIntegralTraceTranslationAssembly
import Dubon2026.SourceIntegralTraceAnalyticProducts
import Dubon2026.SourceIntegralTraceTransversalSplit
import Dubon2026.SourceTraceExponentialCoefficientVanishing
import Dubon2026.SourceIntegralTracePowerCoefficients

/-! DUB-17/18 -> original Gamma1 degree preservation -> even-weight
slash integrality -> peaked auxiliary trace. Assemble the actual
level-one trace and its exact Fourier decomposition. Integral translated
coefficients and vanishing remainder coefficients are derived from the
original expansions, signed cosets and auxiliary decay. No trace identity
or Fourier vanishing is supplied as an assumption.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularForm_qExpansion_slash_coeff_mem_of_peaked_auxiliary. -/
namespace Dubon2026.SourceFunctionField.IntegralTrace
noncomputable section
open scoped MatrixGroups ModularForm Manifold
open UpperHalfPlane

theorem exists_integral_trace_decomposition
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (h : ℕ) (hh : 0 < h)
    (hT : ModularGroup.T ^ h ∈ Γ)
    (hS : ModularGroup.S * ModularGroup.T * ModularGroup.S⁻¹ ∈ Γ)
    (R : Subring ℂ) {k w : ℤ}
    (G : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    (hG : ∀ n, (qExpansion (h : ℝ) (⇑G : ℍ → ℂ)).coeff n ∈ R)
    (Θ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) w)
    (hΘ : ∀ n, (qExpansion (h : ℝ) (⇑Θ : ℍ → ℂ)).coeff n ∈ R)
    (r h₀ m₀ : ℕ) (δ : ℝ) (hev : Even (k + (r : ℤ) * w))
    (hh₀ : 0 < h₀) (hh₀h : h₀ ∣ h)
    (hT₀ : ModularGroup.T ^ h₀ ∈ Γ ∨ -(ModularGroup.T ^ h₀) ∈ Γ)
    (hmin : ∀ j : ℕ, 0 < j → j < h₀ →
      ModularGroup.T ^ j ∉ Γ ∧ -(ModularGroup.T ^ j) ∉ Γ)
    (hdeg : ∀ j : ℤ, ModularGroup.S * ModularGroup.T ^ j ∉ Γ ∧
      -(ModularGroup.S * ModularGroup.T ^ j) ∉ Γ)
    (hdecay : ∀ β : SL(2, ℤ),
      (∀ j : ℤ, β * ModularGroup.T ^ j ∉ Γ ∧ -(β * ModularGroup.T ^ j) ∉ Γ) →
      (β * ModularGroup.S⁻¹ ∉ Γ ∧ -(β * ModularGroup.S⁻¹) ∉ Γ) →
      ((⇑Θ : ℍ → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[atImInfty]
        fun τ : ℍ => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im)) :
    ∃ (F : ModularForm 𝒮ℒ (k + (r : ℤ) * w)) (A C : PowerSeries ℂ),
      qExpansion 1 (F : ℍ → ℂ) = A +
        qExpansion 1 ((⇑G : ℍ → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) *
        qExpansion 1 ((⇑Θ : ℍ → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) ^ r + C ∧
      (∀ i, A.coeff i ∈ R) ∧
      (∀ i : ℕ, (i : ℝ) < r * ((m₀ : ℝ) + δ) → C.coeff i = 0) := by
  classical
  obtain ⟨s, hcover, hsep, hTs, hSs, hrest⟩ :=
    exists_signed_cusp_transversal Γ hdeg h₀ hh₀ hT₀ hmin
  let X : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k + (r : ℤ) * w) := (G.mul (Θ.pow r)).mcast (by ring)
  have hXcoe : (⇑X : UpperHalfPlane → ℂ) = ⇑G * (⇑Θ) ^ r := by
    simp [X, ModularForm.coe_mcast, ModularForm.coe_mul, ModularForm.coe_pow]
  have hXslash : ∀ x : SL(2, ℤ), (⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ) =
      ((⇑G : UpperHalfPlane → ℂ) ∣[k] (x : GL (Fin 2) ℝ)) * ((⇑Θ : UpperHalfPlane → ℂ) ∣[w] (x : GL (Fin 2) ℝ)) ^ r := by
    intro x
    rw [hXcoe, ← ModularForm.SL_slash, ModularForm.mul_slash_SL2, pow_slash_SL2, ModularForm.SL_slash,
      ModularForm.SL_slash]

  have hhR : (h : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := natCast_mem_strictPeriods Γ h hT
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hXR : ∀ m : ℕ, (UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ)).coeff m ∈ R := by
    intro m
    have e : UpperHalfPlane.qExpansion (h : ℝ) (⇑X : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion (h : ℝ) (⇑G : UpperHalfPlane → ℂ) *
          UpperHalfPlane.qExpansion (h : ℝ) (⇑Θ : UpperHalfPlane → ℂ) ^ r := by
      show UpperHalfPlane.qExpansion (h : ℝ) ⇑((G.mul (Θ.pow r)).mcast _) = _
      rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul hh' hhR, ModularForm.qExpansion_pow hh' hhR]
    rw [e]
    exact coeff_mul_mem hG (coeff_pow_mem hΘ r) m

  obtain ⟨F, hF⟩ := exists_levelOne_trace Γ hev X s hcover hsep
  set gS : UpperHalfPlane → ℂ := (⇑G : UpperHalfPlane → ℂ) ∣[k] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) with hgS
  set θS : UpperHalfPlane → ℂ := (⇑Θ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ) with hθS
  set FA : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => ∑ j ∈ Finset.range h₀,
    ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] ((ModularGroup.T ^ j : SL(2, ℤ)) : GL (Fin 2) ℝ)) τ with hFA
  set FS : UpperHalfPlane → ℂ := (⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)
    with hFS
  set C : Finset SL(2, ℤ) := s.filter (fun x => (∀ j : ℕ, j < h₀ → x ≠ ModularGroup.T ^ j) ∧ x ≠ ModularGroup.S)
    with hC
  set FC : UpperHalfPlane → ℂ := fun τ : UpperHalfPlane => ∑ x ∈ C,
    ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) τ with hFC
  have hsplit : (⇑F : UpperHalfPlane → ℂ) = FA + FS + FC := by
    rw [hF, sum_transversal_split s h₀ hTs hSs _, Finset.sum_fn, Finset.sum_fn]
  have hFSeq : FS = gS * θS ^ r := hXslash ModularGroup.S

  have h1SL : (1 : ℝ) ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hXh : ∀ x : SL(2, ℤ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) :=
    fun x => mdifferentiable_slash X x
  have hXb : ∀ x : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty ((⇑X : UpperHalfPlane → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) :=
    fun x => isBoundedAtImInfty_slash X x
  have hgSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) gS := mdifferentiable_slash G _
  have hgSb : UpperHalfPlane.IsBoundedAtImInfty gS := isBoundedAtImInfty_slash G _
  have hθSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) θS := mdifferentiable_slash Θ _
  have hθSb : UpperHalfPlane.IsBoundedAtImInfty θS := isBoundedAtImInfty_slash Θ _
  have hgSp : Function.Periodic (gS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq gS k 1 (slash_S_slash_T_eq G hS)
    rwa [Nat.cast_one] at this
  have hθSp : Function.Periodic (θS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq θS w 1 (slash_S_slash_T_eq Θ hS)
    rwa [Nat.cast_one] at this
  have hFSp : Function.Periodic (FS ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    have := periodic_comp_ofComplex_of_slash_T_pow_eq FS (k + (r : ℤ) * w) 1 (slash_S_slash_T_eq X hS)
    rwa [Nat.cast_one] at this
  have hFSh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FS := hXh _
  have hFSb : UpperHalfPlane.IsBoundedAtImInfty FS := hXb _
  have hFAh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FA := mdifferentiable_finset_sum _ _ fun j _ => hXh _
  have hFAb : UpperHalfPlane.IsBoundedAtImInfty FA := isBoundedAtImInfty_finset_sum _ _ fun j _ => hXb _
  have hFCh : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) FC := mdifferentiable_finset_sum _ _ fun x _ => hXh _
  have hFCb : UpperHalfPlane.IsBoundedAtImInfty FC := isBoundedAtImInfty_finset_sum _ _ fun x _ => hXb _

  have hFAeq : FA = Translates.trSum (⇑X : ℍ → ℂ) h₀ :=
    translation_sum_eq _ _ _
  have hFAp : Function.Periodic (FA ∘ ofComplex) (1 : ℝ) := by
    rw [hFAeq]
    exact Translates.periodic_trSum (periodic_of_pm_mem X hev h₀ hT₀)
  have hFp : Function.Periodic ((⇑F : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (1 : ℝ) :=
    SlashInvariantFormClass.periodic_comp_ofComplex F h1SL
  have hFCeq : FC = (⇑F : UpperHalfPlane → ℂ) - FA - FS := by rw [hsplit]; abel
  have hFCp : Function.Periodic (FC ∘ UpperHalfPlane.ofComplex) (1 : ℝ) := by
    rw [hFCeq]
    exact (hFp.sub hFAp).sub hFSp

  have hqF : UpperHalfPlane.qExpansion 1 (⇑F : UpperHalfPlane → ℂ) =
      UpperHalfPlane.qExpansion 1 FA + UpperHalfPlane.qExpansion 1 FS + UpperHalfPlane.qExpansion 1 FC := by
    rw [hsplit, UpperHalfPlane.qExpansion_add, UpperHalfPlane.qExpansion_add]
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFAp hFAh hFAb
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFSp hFSh hFSb
    · refine UpperHalfPlane.analyticAt_cuspFunction_zero one_pos (hFAp.add hFSp) (hFAh.add hFSh) (hFAb.add hFSb)
    · exact UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hFCp hFCh hFCb
  have hA : ∀ i : ℕ, (UpperHalfPlane.qExpansion 1 FA).coeff i ∈ R := by
    intro i
    have e := coeff_qExpansion_one_sum_slash_T_pow h hh hev X h₀ hh₀ hh₀h hT₀ i
    rw [e]
    exact R.mul_mem (natCast_mem R h₀) (hXR _)
  have hSq : UpperHalfPlane.qExpansion 1 FS = UpperHalfPlane.qExpansion 1 gS * UpperHalfPlane.qExpansion 1 θS ^ r := by
    rw [hFSeq]
    exact qExpansion_one_mul_pow gS θS hgSp hgSh hgSb hθSp hθSh hθSb r
  have hCO : FC =O[UpperHalfPlane.atImInfty]
      fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((r : ℝ) * ((m₀ : ℝ) + δ))) * τ.im) := by
    have hterm : ∀ x ∈ C,
        ((⇑X : ℍ → ℂ) ∣[k + (r : ℤ) * w] (x : GL (Fin 2) ℝ)) =O[atImInfty]
          fun τ : ℍ => Real.exp (-(2 * Real.pi * ((r : ℝ) * ((m₀ : ℝ) + δ))) * τ.im) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [hXslash x]
      exact isBigO_mul_pow_exp _ _ (isBoundedAtImInfty_slash G x) _
        (hdecay x (hrest x hx.1 hx.2.1 hx.2.2).1 (hrest x hx.1 hx.2.1 hx.2.2).2) r
    exact (Asymptotics.IsBigO.sum hterm).congr'
      (Filter.Eventually.of_forall fun _ => rfl) Filter.EventuallyEq.rfl
  have hC0 : ∀ i : ℕ, (i : ℝ) < r * ((m₀ : ℝ) + δ) → (UpperHalfPlane.qExpansion 1 FC).coeff i = 0 :=
    fun i hi => qExpansion_coeff_zero_of_exponential_decay FC hFCp hFCh hFCb _ hCO i hi


  refine ⟨F, qExpansion 1 FA, qExpansion 1 FC, ?_, hA, hC0⟩
  rw [hqF, hSq]

end
end Dubon2026.SourceFunctionField.IntegralTrace
