import Dubon2026.SourceNativeH1KernelRepresentative
import Dubon2026.SourceNativeCorrespondenceBoundary
import Dubon2026.HeckeUpperCosets

/-! The exact original Hecke eigenvalue on the coefficient-inclusion kernel.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> the Eisenstein exception for the actual function-flag eigenclass.
The finite trace calculation is adapted from anthropics/fermats-last-theorem,
revision 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_HeckeEis_isEigensystemH1_or_of_isEigensystemH1_of_injective.lean.txt
(Apache-2.0; retained LICENSE and NOTICE). Existing native naturality,
coboundary trace and the original p+1 transversal supply the operator proof.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup CategoryTheory groupCohomology

variable {F : Type} [Field F] {Q ell : ℕ} [NeZero ell]
    (hell : ell.Prime) (hellQ : Nat.Coprime ell Q)
    (A B : Rep F (Gamma0 Q)) (f : A ⟶ B) (hf : Function.Injective f)
    (a : Module.End F A) (b : Module.End F B)
    (ha : ∀ u : heckeUpperSubgroup Q ell,
      a.comp (A.ρ (sourceHeckeConjugation hell u)) = (A.ρ u.val).comp a)
    (hb : ∀ u : heckeUpperSubgroup Q ell,
      b.comp (B.ρ (sourceHeckeConjugation hell u)) = (B.ρ u.val).comp b)
    (hfb : f.hom.toLinearMap.comp a = b.comp f.hom.toLinearMap)

private local instance kernelHeckeFinite :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) := sourceHeckeUpperFintype Q ell

include hellQ hf hb hfb in
/-- An actual native H1 class with a primitive in the one-dimensional
invariant quotient has the exact original Eisenstein Hecke eigenvalue. -/
theorem sourceNativeH1_kernel_hecke (q : B) (c : F)
    (hc : b q - c • q ∈ LinearMap.range f.hom.toLinearMap)
    (hq : ∀ g : Gamma0 Q, B.ρ g q - q ∈ LinearMap.range f.hom.toLinearMap)
    (z : cocycles₁ A) (v : B) (r : F)
    (hv : ∀ g : Gamma0 Q, B.ρ g v - v = f (z g))
    (hr : v - r • q ∈ LinearMap.range f.hom.toLinearMap) :
    sourcePrimeHeckeH1 hell A a ha (H1π A z) = (((ell : F) + 1) * c) • H1π A z := by
  let w : B := cosetTraceZero B (heckeUpperSubgroup Q ell) (b v)
  let e : F := ((ell : F) + 1) * c
  have hT : ∀ g : Gamma0 Q,
      f (sourcePrimeHeckeCocycles hell A a ha z g) = B.ρ g w - w := by
    intro g
    have hn := sourcePrimeHeckeCocycles_naturality hell A B f a b ha hb hfb z
    have hcob : (fun t : Gamma0 Q => f (z t)) = d₀₁ B v := (funext hv).symm
    have hn' := congrArg (fun y : cocycles₁ B => y g) hn
    change f (sourcePrimeHeckeCocycles hell A a ha z g) =
      sourceCorrespondenceOne B (heckeUpperSubgroup Q ell) (sourceHeckeConjugation hell)
        b (fun t => f (z t)) g at hn'
    rw [hcob, sourceCorrespondenceOne_d01 B _ _ b hb v] at hn'
    exact hn'
  have hbv : b v - (r * c) • q ∈ LinearMap.range f.hom.toLinearMap := by
    obtain ⟨u, hu⟩ := hr
    have he : b v - (r * c) • q =
        b (f.hom.toLinearMap u) + r • (b q - c • q) := by
      have hv' : v = f.hom.toLinearMap u + r • q := by rw [hu]; abel
      rw [hv', map_add, map_smul, smul_sub, mul_smul]
      abel
    rw [he]
    exact Submodule.add_mem _ ⟨a u, LinearMap.congr_fun hfb u⟩
      (Submodule.smul_mem _ r hc)
  have hcard : Fintype.card (Gamma0 Q ⧸ heckeUpperSubgroup Q ell) = ell + 1 := by
    letI : Fact ell.Prime := ⟨hell⟩
    rw [← Fintype.card_congr (heckeUpperCosetEquiv hell hellQ)]
    simp
  have hwq : w - (((ell : F) + 1) * (r * c)) • q ∈
      LinearMap.range f.hom.toLinearMap := by
    have he : w - (((ell : F) + 1) * (r * c)) • q =
        ∑ t : Gamma0 Q ⧸ heckeUpperSubgroup Q ell,
          (B.ρ t.out (b v) - (r * c) • q) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard,
        ← Nat.cast_smul_eq_nsmul F, Nat.cast_add, Nat.cast_one, mul_smul]
      simp only [w, cosetTraceZero, LinearMap.sum_apply]
    rw [he]
    exact Submodule.sum_mem _ fun t _ =>
      sourceNativeCoefficient_range_congr A B f q hq t.out (r * c) hbv
  have hwv : w - e • v ∈ LinearMap.range f.hom.toLinearMap := by
    have he : w - e • v =
        (w - (((ell : F) + 1) * (r * c)) • q) - e • (v - r • q) := by
      simp only [smul_sub, smul_smul, e]
      rw [show (((ell : F) + 1) * c) * r = ((ell : F) + 1) * (r * c) by ring]
      abel
    rw [he]
    exact Submodule.sub_mem _ hwq (Submodule.smul_mem _ e hr)
  obtain ⟨s, hs⟩ := hwv
  rw [sourcePrimeHeckeH1_cocycle, ← map_smul, H1π_eq_iff]
  refine ⟨s, funext fun g => ?_⟩
  change A.ρ g s - s = sourcePrimeHeckeCocycles hell A a ha z g - e • z g
  apply hf
  have hfg : f.hom.toLinearMap (A.ρ g s) = B.ρ g (f.hom.toLinearMap s) :=
    LinearMap.congr_fun (f.hom.isIntertwining' g) s
  change f.hom.toLinearMap (A.ρ g s - s) =
    f.hom.toLinearMap (sourcePrimeHeckeCocycles hell A a ha z g - e • z g)
  rw [map_sub, map_sub, map_smul, hfg, hs]
  change B.ρ g (w - e • v) - (w - e • v) =
    f (sourcePrimeHeckeCocycles hell A a ha z g) - e • f (z g)
  rw [hT, ← hv g, map_sub, map_smul, smul_sub]
  abel

end
end Dubon2026
