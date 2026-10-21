import Dubon2026.SourceFiniteCuspBoundary
import Dubon2026.SourceCommutingCommonEigenvector
import Dubon2026.SourceTrivialCoefficientHecke
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-! DUB-17/18 -> residual Galois association -> the nonparabolic branch
of the original complex weight-two class -> its actual Dirichlet pair.
The finite cusp-boundary function is retained inside its simultaneous
Hecke eigenspace. The already proved minimal-prime eigenvector supplies
unit characters, with their exact product and original prime values.
-/
namespace Dubon2026.SourceCuspBoundary
noncomputable section

variable {N : ℕ} (values : sourceBinaryHeckePrime N → ℂ)

private def primeUnit (ell : sourceBinaryHeckePrime N) : (ZMod N)ˣ :=
  ZMod.unitOfCoprime ell.val ell.property.2

/-- The simultaneous original boundary Hecke eigenspace with trivial
Gamma0 diagonal action, inside functions on the actual finite cusp columns. -/
def W : Submodule ℂ (P N → ℂ) where
  carrier := {f | (∀ ell : sourceBinaryHeckePrime N, ∀ p,
    (ell.val : ℂ) * f (scale (primeUnit ell)⁻¹ 1 p) +
      f (scale 1 (primeUnit ell) p) = values ell * f p) ∧
    ∀ d : (ZMod N)ˣ, ∀ p, f (scale d⁻¹ d p) = f p}
  zero_mem' := by constructor <;> intros <;> simp
  add_mem' := by
    intro f g hf hg
    constructor
    · intro ell p
      simp only [Pi.add_apply]
      linear_combination hf.1 ell p + hg.1 ell p
    · intro d p
      simp only [Pi.add_apply, hf.2 d p, hg.2 d p]
  smul_mem' := by
    intro c f hf
    constructor
    · intro ell p
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination c * hf.1 ell p
    · intro d p
      simp only [Pi.smul_apply, hf.2 d p]

/-- Unit-coordinate translation on the original finite cusp functions. -/
def rho (g : (ZMod N)ˣ × (ZMod N)ˣ) : Module.End ℂ (P N → ℂ) where
  toFun f p := f (scale g.1 g.2 p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Each unit-coordinate action preserves the actual boundary Hecke eigenspace. -/
theorem rho_mem_W (g : (ZMod N)ˣ × (ZMod N)ˣ) {f : P N → ℂ} (hf : f ∈ W values) :
    rho g f ∈ W values := by
  constructor
  · intro ell p
    change (ell.val : ℂ) * f (scale g.1 g.2 (scale (primeUnit ell)⁻¹ 1 p)) +
      f (scale g.1 g.2 (scale 1 (primeUnit ell) p)) =
        values ell * f (scale g.1 g.2 p)
    rw [scale_comm g.1 g.2, scale_comm g.1 g.2]
    exact hf.1 ell (scale g.1 g.2 p)
  · intro d p
    change f (scale g.1 g.2 (scale d⁻¹ d p)) = f (scale g.1 g.2 p)
    rw [scale_comm]
    exact hf.2 d (scale g.1 g.2 p)

/-- The actual unit action restricted to the original nonzero boundary eigenspace. -/
def rhoW (g : (ZMod N)ˣ × (ZMod N)ˣ) : Module.End ℂ (W values) :=
  (rho g).restrict (fun _ hf => rho_mem_W values g hf)

/-- The restricted unit-coordinate operators commute on the actual boundary eigenspace. -/
theorem rhoW_comm (g g' : (ZMod N)ˣ × (ZMod N)ˣ) :
    Commute (rhoW values g) (rhoW values g') := by
  ext ⟨f, hf⟩ p
  change f (scale g'.1 g'.2 (scale g.1 g.2 p)) =
    f (scale g.1 g.2 (scale g'.1 g'.2 p))
  rw [scale_comm]

/-- A nonzero actual boundary eigenspace determines two genuine Dirichlet
characters with product one and the exact original good-prime eigenvalues. -/
theorem exists_dirichlet_pair [NeZero N] (b : P N → ℂ) (hb : b ∈ W values) (hb0 : b ≠ 0) :
    ∃ ψ₁ ψ₂ : DirichletCharacter ℂ N,
      (∀ u : (ZMod N)ˣ, ψ₁ (u : ZMod N) * ψ₂ (u : ZMod N) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        values ell = ψ₁ (ell.val : ZMod N) + (ell.val : ℂ) * ψ₂ (ell.val : ZMod N) := by
  classical
  letI : Fintype (P N) := Fintype.ofFinite _
  haveI : Nontrivial (W values) :=
    nontrivial_of_ne (⟨b, hb⟩ : W values) 0 (fun h => hb0 (congrArg Subtype.val h))
  obtain ⟨χ, w, hw0, hw⟩ :=
    sourceCommutingOperators_exists_commonEigenvector (rhoW values) (rhoW_comm values)
  let f : P N → ℂ := w.val
  have hf (g : (ZMod N)ˣ × (ZMod N)ˣ) (p : P N) :
      f (scale g.1 g.2 p) = χ g * f p := by
    exact congrArg (fun v : W values => v.val p) (hw g)
  have hfW : f ∈ W values := w.property
  have hf0 : f ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨p₀, hp₀⟩ := Function.ne_iff.mp hf0
  simp only [Pi.zero_apply] at hp₀
  have hχmul (g g' : (ZMod N)ˣ × (ZMod N)ˣ) : χ (g * g') = χ g * χ g' := by
    have h1 := hf (g * g') p₀
    rw [Prod.fst_mul, Prod.snd_mul, ← scale_scale, hf g, hf g', ← mul_assoc] at h1
    exact (mul_right_cancel₀ hp₀ h1).symm
  have hχone : χ 1 = 1 := by
    have h1 := hf 1 p₀
    rw [Prod.fst_one, Prod.snd_one, scale_one] at h1
    exact (mul_eq_right₀ hp₀).mp h1.symm
  have hχne (g : (ZMod N)ˣ × (ZMod N)ˣ) : χ g ≠ 0 := by
    have h := hχmul g g⁻¹
    rw [mul_inv_cancel, hχone] at h
    exact left_ne_zero_of_mul_eq_one h.symm
  let χu : (ZMod N)ˣ × (ZMod N)ˣ →* ℂˣ :=
    { toFun := fun g => Units.mk0 (χ g) (hχne g)
      map_one' := Units.ext hχone
      map_mul' := fun g g' => Units.ext (hχmul g g') }
  let ψ₁ : DirichletCharacter ℂ N := MulChar.ofUnitHom (χu.comp (MonoidHom.inr _ _))
  let ψ₂ : DirichletCharacter ℂ N :=
    MulChar.ofUnitHom (χu.comp ((MonoidHom.inl _ _).comp invMonoidHom))
  have hψ₁ (u : (ZMod N)ˣ) : ψ₁ (u : ZMod N) = χ (1, u) := by
    change MulChar.ofUnitHom _ (u : ZMod N) = _
    rw [MulChar.ofUnitHom_coe]
    rfl
  have hψ₂ (u : (ZMod N)ˣ) : ψ₂ (u : ZMod N) = χ (u⁻¹, 1) := by
    change MulChar.ofUnitHom _ (u : ZMod N) = _
    rw [MulChar.ofUnitHom_coe]
    rfl
  refine ⟨ψ₁, ψ₂, ?_, ?_⟩
  · intro u
    rw [hψ₁, hψ₂, ← hχmul,
      show ((1 : (ZMod N)ˣ), u) * (u⁻¹, 1) = (u⁻¹, u) from
        Prod.ext (one_mul _) (mul_one _)]
    have h1 := hfW.2 u p₀
    rw [show scale u⁻¹ u p₀ = scale (u⁻¹, u).1 (u⁻¹, u).2 p₀ from rfl, hf] at h1
    exact (mul_eq_right₀ hp₀).mp h1
  · intro ell
    have hu : ((primeUnit ell : (ZMod N)ˣ) : ZMod N) = ell.val :=
      ZMod.coe_unitOfCoprime _ _
    rw [← hu, hψ₁, hψ₂]
    have h1 := hfW.1 ell p₀
    rw [show scale (primeUnit ell)⁻¹ 1 p₀ =
      scale ((primeUnit ell)⁻¹, (1 : (ZMod N)ˣ)).1
        ((primeUnit ell)⁻¹, (1 : (ZMod N)ˣ)).2 p₀ from rfl, hf,
      show scale 1 (primeUnit ell) p₀ = scale ((1 : (ZMod N)ˣ), primeUnit ell).1
        ((1 : (ZMod N)ˣ), primeUnit ell).2 p₀ from rfl, hf] at h1
    have h2 : (χ (1, primeUnit ell) + (ell.val : ℂ) * χ ((primeUnit ell)⁻¹, 1)) * f p₀ =
        values ell * f p₀ := by linear_combination h1
    exact (mul_right_cancel₀ hp₀ h2).symm

end
end Dubon2026.SourceCuspBoundary
