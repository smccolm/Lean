/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck

The rational-cusp transport argument adapts HeckeModularForm.lean at
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Dubon2026.HeckeTriangular

/-! # Holomorphy and cusp vanishing of the literal classical Hecke function

This proves the analytic parts of preservation. Slash invariance is a separate
obligation and is not included as a field of a purported Hecke endomorphism.
-/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Finset
open scoped MatrixGroups ModularForm Manifold

noncomputable section

/-- Every rational matrix transports the actual cusps of an arithmetic subgroup to cusps. -/
theorem rationalMatrix_smul_isCusp {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (A : GL (Fin 2) ℚ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    IsCusp (GeneralLinearGroup.map (algebraMap ℚ ℝ) A • c) Γ := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  exact ⟨A • q, OnePoint.map_smul (algebraMap ℚ ℝ) A q⟩

/-- The actual finite sum of upper-triangular slash translates. -/
def heckeTriangularSum (a d : ℕ) [NeZero a] [NeZero d] (k : ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ b ∈ range d, f ∣[k] heckeTriangularMatrix a d b

/-- The literal slash sum equals the scaled Fourier averaging term. -/
theorem heckeTriangularSum_apply (a d : ℕ) [NeZero a] [NeZero d] (k : ℤ)
    (f : ℍ → ℂ) (τ : ℍ) :
    heckeTriangularSum a d k f τ = (a : ℂ) ^ (k - 1) *
      heckeAverage d f (levelRaiseMatrix a • τ) := by
  simp only [heckeTriangularSum, Finset.sum_apply, heckeTriangular_slash_apply,
    heckeAverage, ← Finset.mul_sum, mul_assoc]

/-- The finite slash sum of a holomorphic function is holomorphic. -/
theorem heckeTriangularSum_holomorphic (a d : ℕ) [NeZero a] [NeZero d] (k : ℤ)
    (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (heckeTriangularSum a d k f) :=
  MDifferentiable.sum fun _ _ => hf.slash k _

/-- Every actual summand vanishes at every arithmetic cusp. -/
theorem heckeTriangularSum_zero_at_cusps {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    (a d : ℕ) [NeZero a] [NeZero d] {k : ℤ} (f : CuspForm Γ k)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt (heckeTriangularSum a d k f) k := by
  unfold heckeTriangularSum
  exact Finset.sum_induction _ (fun g => c.IsZeroAt g k) (fun _ _ ha hb => ha.add hb)
    ((0 : CuspForm Γ k).zero_at_cusps' hc) fun b _ =>
      OnePoint.IsZeroAt.smul_iff.mp (f.zero_at_cusps'
        (rationalMatrix_smul_isCusp (heckeTriangularRat a d b) hc))

/-- Each divisor summand in the literal classical operator is holomorphic. -/
theorem classicalHeckeTerm_holomorphic (Q : ℕ) (k : ℤ) (n d : ℕ) (hd : d ∈ n.divisors)
    (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (classicalHeckeTerm Q k n d hd f) := by
  haveI : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
  haveI : NeZero (n / d) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
      (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)).ne'⟩
  by_cases hc : Nat.Coprime d Q
  · have he : classicalHeckeTerm Q k n d hd f = heckeTriangularSum d (n / d) k f := by
      funext τ
      dsimp only [classicalHeckeTerm]
      rw [if_pos hc, heckeTriangularSum_apply]
    rw [he]
    exact heckeTriangularSum_holomorphic d (n / d) k f hf
  · have he : classicalHeckeTerm Q k n d hd f = 0 := by
      funext τ
      simp [classicalHeckeTerm, hc]
    rw [he]
    exact mdifferentiable_const

/-- The literal classical Hecke finite sum preserves holomorphy. -/
theorem classicalHeckeFunction_holomorphic (Q : ℕ) (k : ℤ) (n : ℕ)
    (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (classicalHeckeFunction Q k n f) := by
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun τ => ∑ d ∈ n.divisors.attach, classicalHeckeTerm Q k n d.val d.property f τ)
  simpa only [Finset.sum_fn] using
    (MDifferentiable.sum (t := n.divisors.attach) fun d _ =>
      classicalHeckeTerm_holomorphic Q k n d.val d.property f hf)

/-- Each actual divisor summand vanishes at every cusp of the positive level. -/
theorem classicalHeckeTerm_zero_at_cusps (Q : ℕ) [NeZero Q] (k : ℤ) (n d : ℕ)
    (hd : d ∈ n.divisors) (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 Q).map (mapGL ℝ))) :
    c.IsZeroAt (classicalHeckeTerm Q k n d hd f) k := by
  haveI : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
  haveI : NeZero (n / d) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd))
      (Nat.dvd_of_mem_divisors hd)) (Nat.pos_of_mem_divisors hd)).ne'⟩
  by_cases hcop : Nat.Coprime d Q
  · have he : classicalHeckeTerm Q k n d hd f = heckeTriangularSum d (n / d) k f := by
      funext τ
      dsimp only [classicalHeckeTerm]
      rw [if_pos hcop, heckeTriangularSum_apply]
    rw [he]
    exact heckeTriangularSum_zero_at_cusps d (n / d) f hc
  · have he : classicalHeckeTerm Q k n d hd f = 0 := by
      funext τ
      simp [classicalHeckeTerm, hcop]
    rw [he]
    exact (0 : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k).zero_at_cusps' hc

/-- The actual classical operator preserves vanishing at every arithmetic cusp. -/
theorem classicalHeckeFunction_zero_at_cusps (Q : ℕ) [NeZero Q] (k : ℤ) (n : ℕ)
    (f : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma0 Q).map (mapGL ℝ))) :
    c.IsZeroAt (classicalHeckeFunction Q k n f) k := by
  have he : classicalHeckeFunction Q k n f =
      ∑ d ∈ n.divisors.attach, classicalHeckeTerm Q k n d.val d.property f := by
    ext τ
    simp only [classicalHeckeFunction, Finset.sum_apply]
  rw [he]
  exact Finset.sum_induction _ (fun g => c.IsZeroAt g k) (fun _ _ ha hb => ha.add hb)
    ((0 : CuspForm ((Gamma0 Q).map (mapGL ℝ)) k).zero_at_cusps' hc) fun d _ =>
      classicalHeckeTerm_zero_at_cusps Q k n d.val d.property f hc

end
end Dubon2026
