import Dubon2026.SourceWeightTwoFullEigenlift

/-! DUB-17/18 -> residual modular Galois association. The original residual
H1 eigensystem now yields an actual normalized full cusp eigenform whose
good-prime Fourier coefficients are the same integral lift, with the same
residue map. The alternative is the already proved Dirichlet pair.
Constructing the Galois representation attached to this cusp form remains
the next arithmetic obligation; no Galois existence is asserted here.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

theorem sourceTrivialH1Eigen_normalizedCuspLift_or_dirichletPair
    (F : Type) [Field F] [IsAlgClosed F] (N : ℕ) [NeZero N]
    (values : sourceBinaryHeckePrime N → F)
    (x : H1 (Rep.trivial F (Gamma0 N) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell x = values ell • x) :
    (∃ (θ : sourceBinaryHeckePrime N → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F) (f : CuspForm (Gamma0 N) 2),
      cuspCoefficients f 1 = 1 ∧
      (∀ n, n ≠ 0 → cuspHeckeLinear N 2 n f = cuspCoefficients f n • f) ∧
      (∀ ell, cuspCoefficients f ell.val = (θ ell : ℂ)) ∧
      ∀ ell, φ (θ ell) = values ell) ∨
    ∃ ψ₁ ψ₂ : (ZMod N)ˣ →* Fˣ,
      (∀ u, (ψ₁ u : F) * (ψ₂ u : F) = 1) ∧
      ∀ ell : sourceBinaryHeckePrime N,
        values ell = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : F) +
          (ell.val : F) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : F) := by
  rcases sourceTrivialH1Eigen_cuspLift_or_dirichletPair F N values x hx heig with
    ⟨θ, φ, f, hf, he, hres⟩ | hchars
  · obtain ⟨g, hnorm, hgood, hall⟩ := sourceWeightTwoGoodEigen_exists_normalized N
      (fun ell => (θ ell : ℂ)) f hf he
    exact Or.inl ⟨θ, φ, g, hnorm, hall, hgood, hres⟩
  · exact Or.inr hchars

end
end Dubon2026
