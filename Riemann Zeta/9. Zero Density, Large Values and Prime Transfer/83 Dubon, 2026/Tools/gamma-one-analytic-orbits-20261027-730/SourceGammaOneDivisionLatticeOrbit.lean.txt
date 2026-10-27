import Dubon2026.SourceJScalarAndLatticeRelations
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-! DUB-17/18 -> original Gamma1 global charts -> orbit separation.
Specialize the lattice-to-orbit argument of DivisionValuesCore.finish,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_CohCarrier_exists_mem_GammaH_smul_eq_of_forall_sum_weierstrassP_pow_eq.
The actual rotation and division-point lattice relation remain explicit
inputs, to be supplied by the division-value comparison. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Complex PeriodLattice CongruenceSubgroup
open scoped MatrixGroups ComplexConjugate

private theorem gamma1_mul_inv_mem_of_bottom_right_eq (N : ℕ)
    (γ δ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) (hδ : δ ∈ Gamma0 N)
    (he : (γ 1 1 : ZMod N) = (δ 1 1 : ZMod N)) :
    γ * δ⁻¹ ∈ Gamma1 N := by
  let g : Gamma0 N := ⟨γ, hγ⟩
  let d : Gamma0 N := ⟨δ, hδ⟩
  have hm : Gamma0Map N g = Gamma0Map N d := he
  have hh : Gamma0Map N (g * d⁻¹) = 1 := by
    rw [map_mul, hm, ← map_mul, mul_inv_cancel, map_one]
  exact (Gamma1_mem N _).mpr ((Gamma1_to_Gamma0_mem (g * d⁻¹)).mp
    (Gamma1_mem'.mpr hh))

private theorem mem_tau_lattice (τ : ℍ) (x : ℂ) :
    x ∈ (ofTau τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = x := by
  rw [PeriodPair.mem_lattice]
  simp only [ofTau_ω₁, ofTau_ω₂, mul_one]

theorem exists_gamma1_smul_eq_of_division_lattice (N : ℕ) [NeZero N]
    (τ : ℍ) (γ₀ : SL(2, ℤ)) (hγ₀ : γ₀ ∈ Gamma0 N)
    (a : ℂ) (han : a * conj a = 1)
    (ha1 : a ∈ (ofTau τ).lattice) (haτ : a * τ ∈ (ofTau τ).lattice)
    (hrel : ((((γ₀ 1 1 : ℤ) : ZMod N).val : ℂ) - a) / N ∈ (ofTau τ).lattice) :
    ∃ γ ∈ Gamma1 N, γ • τ = γ₀ • τ := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  obtain ⟨e, f, hef⟩ := (mem_tau_lattice τ _).mp ha1
  obtain ⟨e', f', hef'⟩ := (mem_tau_lattice τ _).mp haτ
  obtain ⟨m, n, hmn⟩ := (mem_tau_lattice τ _).mp hrel
  have hlin : ((N * m + e : ℤ) : ℂ) * τ + ((N * n + f : ℤ) : ℂ) =
      ((0 : ℤ) : ℂ) * τ + (((((γ₀ 1 1 : ℤ) : ZMod N).val : ℤ)) : ℂ) := by
    have h1 : ((m : ℂ) * τ + n) * N = (((γ₀ 1 1 : ℤ) : ZMod N).val : ℂ) - a := by
      rw [hmn, div_mul_cancel₀ _ hN0]
    rw [← hef] at h1
    push_cast
    linear_combination h1
  obtain ⟨hc1, hc2⟩ := JOrbitSeparation.int_indep τ hlin
  have he : (e : ZMod N) = 0 := by
    have hh := congrArg (Int.cast : ℤ → ZMod N) hc1
    push_cast at hh
    simpa using hh
  have hf : (f : ZMod N) = (γ₀ 1 1 : ZMod N) := by
    have hh := congrArg (Int.cast : ℤ → ZMod N) hc2
    push_cast at hh
    simpa using hh
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at han
  set τc : ℂ := conj (τ : ℂ) with hτc
  have hconj1 : conj a = e * τc + f := by
    rw [← hef]
    simp [hτc]
  have hconj2 : conj a * τc = e' * τc + f' := by
    have hh := congrArg conj hef'
    simp only [map_add, map_mul, map_intCast] at hh
    rw [← hh, hτc]
  have hdetC : ((e' * f - f' * e : ℤ) : ℂ) * ((τ : ℂ) - τc) = (τ : ℂ) - τc := by
    push_cast
    linear_combination (-((e' : ℂ) * τc + f')) * hef + conj a * hef' +
      (-((e' : ℂ) * τ + f')) * hconj1 + a * hconj2 + ((τ : ℂ) - τc) * han
  have hττc : (τ : ℂ) - τc ≠ 0 := by
    rw [hτc, Complex.sub_conj]
    refine mul_ne_zero ?_ Complex.I_ne_zero
    exact_mod_cast mul_ne_zero two_ne_zero (UpperHalfPlane.im_ne_zero τ)
  have hdet : e' * f - f' * e = 1 := by
    have hh : ((e' * f - f' * e : ℤ) : ℂ) = 1 :=
      mul_right_cancel₀ hττc (hdetC.trans (one_mul _).symm)
    exact_mod_cast hh
  let ε : SL(2, ℤ) := ⟨!![e', f'; e, f], by rw [Matrix.det_fin_two_of]; linarith⟩
  have hεΓ : ε ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simpa [ε] using he
  have hετ : ε • τ = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [ε, algebraMap_int_eq, eq_intCast, ofReal_intCast, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [hef, hef', div_eq_iff ha0, mul_comm]
  refine ⟨γ₀ * ε⁻¹, ?_, ?_⟩
  · apply gamma1_mul_inv_mem_of_bottom_right_eq N γ₀ ε hγ₀ hεΓ
    simpa [ε] using hf.symm
  · rw [mul_smul, inv_smul_eq_iff.mpr hετ.symm]

end
end Dubon2026.SourceFunctionField.GammaOne
