import Dubon2026.SourceSiegelResidueReduction
import Dubon2026.SourceSiegelSL2Transformation

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> actual peaked auxiliary -> Gamma1-invariant Siegel
product. Prove the literal level shifts of the actual Siegel factors,
reduce integer indices to residue representatives, and show that the
source 12*N exponents kill all derived root-of-unity multipliers. Then
the already constructed exponent translation invariance gives the actual
Gamma1 invariance. No arbitrary multiplier or product invariance premise
is introduced. Common analytic product facts are reused.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_SiegelUnit_siegelFun_add_level and
S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.
The upstream unused-section-variable suppression is not adopted. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel
noncomputable section
open Complex
open scoped Real MatrixGroups

theorem prod_siegelFun_pow_specialLinearGroup_smul (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) :
    (∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s)) ∧
    ((∀ r s : ZMod N, e r (s + r) = e r s) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) := by
  classical

  have h1 : ∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s) := by
    intro β τ
    obtain ⟨μ, hμ, hK⟩ := law_all N β
    refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨ζ, hζ, hred⟩ := exists_siegelFun_eq_mul_reduced N
      ((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
      ((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1) τ
    rw [hK, hred, ← mul_assoc, mul_pow, pow_twelve_mul_eq_one N hμ hζ, one_mul]
  refine ⟨h1, ?_⟩

  intro he γ hγ τ
  rw [h1 γ τ]
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨h00, h11, h10⟩ := hγ
  set b : ZMod N := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod N) with hb

  have he' : ∀ (r s : ZMod N) (k : ℕ), e r (s + k • r) = e r s := by
    intro r s k
    induction k with
    | zero => rw [zero_smul, add_zero]
    | succ k ih => rw [succ_nsmul, ← add_assoc, he, ih]
  have heb : ∀ r s : ZMod N, e r (s + r * b) = e r s := by
    intro r s
    rw [show r * b = b.val • r by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]]
    exact he' r s b.val
  refine Finset.prod_congr rfl fun r _ => ?_

  have hidx1 : ∀ s : ZMod N,
      ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
          (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N)) = r := by
    intro s
    push_cast
    rw [h00, h10, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_one, mul_zero, add_zero]
  have hidx2 : ∀ s : ZMod N,
      ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
          (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N)) = s + r * b := by
    intro s
    push_cast
    rw [h11, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_one, hb, add_comm]
  have hterm : ∀ s : ZMod N,
      siegelFun N
          ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
              (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
          ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
              (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
          (τ : ℂ) ^ (12 * N * e r s) =
        siegelFun N (r.val : ℤ) ((s + r * b).val : ℤ) (τ : ℂ) ^ (12 * N * e r (s + r * b)) := by
    intro s
    rw [hidx1 s, hidx2 s, heb r s]
  rw [Finset.prod_congr rfl (fun s _ => hterm s)]
  exact Fintype.prod_equiv (Equiv.addRight (r * b)) _ _ (fun s => rfl)

end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel
