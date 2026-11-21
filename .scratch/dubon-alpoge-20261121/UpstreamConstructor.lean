import Dubon2026.AlpogeEigenformInput
open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm
noncomputable section
namespace UpperTheory.V.Af
def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def HasChar (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → f ∣[(k : ℤ)] γ = χ ((γ 1 1 : ℤ) : ZMod M) • f

def IsEigAt (k : ℕ) {M : ℕ} (χ : DirichletCharacter ℂ M) (f : ℍ → ℂ) (p : ℕ) (lam : ℂ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    coef f (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0) = lam * coef f n

end UpperTheory.V.Af
namespace UpperTheory.V.Sd
open UpperTheory.V.Af
structure Eigenform (k N : ℕ) (χ : DirichletCharacter ℂ N) where

  f : CuspForm (Gamma1 N) (k : ℤ)
  char : HasChar k χ f
  one : coef f 1 = 1
  eig : ∀ p : ℕ, p.Prime → IsEigAt k χ f p (coef f p)

def Eigenform.a {k N : ℕ} {χ : DirichletCharacter ℂ N} (g : Eigenform k N χ) (n : ℕ) : ℂ := coef g.f n

end UpperTheory.V.Sd
open Dubon2026 UpperTheory.V

theorem original_eigenform_constructor {Q k : ℕ} [NeZero Q] (hk : 2 ≤ k)
    (f : PrimitiveCuspForm Q (k : ℤ)) :
    ∃ g : Sd.Eigenform k Q 1, (g.f : ℍ → ℂ) = f.toCuspForm ∧
      ∀ n, g.a n = cuspCoefficients f.toCuspForm n := by
  obtain ⟨g, he, hc, h1, hp⟩ := primitive_alpoge_eigenform_input (by omega) f
  refine ⟨⟨g, hc, h1, hp⟩, he, ?_⟩
  intro n
  change (qExpansion 1 (g : ℍ → ℂ)).coeff n = _
  rw [he]
  rfl

#print axioms original_eigenform_constructor
end
