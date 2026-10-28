import Dubon2026.SourceGammaOneHeckeJDegree
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! DUB17/18 -> actual Gamma1 Picard/Hecke comparison -> exact geometric
fiber multiplicities. Reuse the native positive-weight argument: a surjection
whose positive weighted source sum is at most the target sum is injective.
The actual j degree and native ramification bound give that inequality for
every intersection-curve fiber, including elliptic fibers. -/
namespace Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceCurve
open scoped MatrixGroups StabilizerCharacter GammaOne

private theorem injective_of_positive_weight_sum_le {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B) (hf : Function.Surjective f) (w : B → ℤ) (hw : ∀ b, 0 < w b)
    (hsum : ∑ a, w (f a) ≤ ∑ b, w b) : Function.Injective f := by
  classical
  obtain ⟨g, hg⟩ := hf.hasRightInverse
  have hi : Function.Injective g := hg.injective
  have himage : ∑ a ∈ Finset.univ.image g, w (f a) = ∑ b, w b := by
    rw [Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_congr rfl (fun b _ => congrArg w (hg b))
  have hgs : Function.Surjective g := by
    intro a
    by_contra ha
    have hnot : a ∉ Finset.univ.image g := by simpa using ha
    have hlt := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.image g))
      (Finset.mem_univ a) hnot (hw (f a)) (fun b _ _ => (hw (f b)).le)
    rw [himage] at hlt
    exact (not_lt_of_ge hsum) hlt
  intro a b hab
  obtain ⟨a', rfl⟩ := hgs a
  obtain ⟨b', rfl⟩ := hgs b
  apply congrArg g
  simpa only [hg a', hg b'] using hab

theorem toFiber_bijective (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ) :
    Function.Bijective (toFiber M d hT τ) := by
  classical
  haveI := finite_orbitQuot M d τ
  letI : Fintype (OrbitQuot M d τ) := Fintype.ofFinite _
  haveI : Finite (Fiber M d τ) :=
    Finite.of_surjective (toFiber M d hT τ) (toFiber_surjective M d hT τ)
  letI : Fintype (Fiber M d τ) := Fintype.ofFinite _
  let x := jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
    algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ)
  let w : Fiber M d τ → ℤ := fun P => P.val.ord x
  have hs : (∑ P : Fiber M d τ, w P) =
      ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index : ℤ) := by
    have h := sum_j_fiber_orders_eq_finrank hT (JMultiplicity.jf τ)
    rw [finrank_over_j_eq_index M d hT] at h
    simpa only [finsum_eq_sum_of_fintype] using h
  refine ⟨injective_of_positive_weight_sum_le (toFiber M d hT τ)
    (toFiber_surjective M d hT τ) w (fun P => P.property) ?_,
    toFiber_surjective M d hT τ⟩
  calc
    (∑ q : OrbitQuot M d τ, w (toFiber M d hT τ q)) ≤
        ∑ q : OrbitQuot M d τ,
          ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).relIndex
            (MulAction.stabilizer SL(2, ℤ) (rep M d τ q)) : ℤ) := by
      apply Finset.sum_le_sum
      intro q _
      have h := (analytic_j_order_le_relative_index hT (rep M d τ q)).2.1
      rw [j_rep] at h
      exact h
    _ = ((plusMinus (Gamma1 M ⊓ Gamma0 (d * M))).index : ℤ) :=
      sum_relative_indices_eq_index M d τ
    _ = ∑ P : Fiber M d τ, w P := hs.symm

/-- The actual orbit-to-place bijection for every geometric Hecke j fiber. -/
def equiv (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ) :
    OrbitQuot M d τ ≃ Fiber M d τ :=
  Equiv.ofBijective (toFiber M d hT τ) (toFiber_bijective M d hT τ)

theorem sum_orders (M d : ℕ) [NeZero M] [NeZero d]
    (hT : ModularGroup.T ∈ Gamma1 M ⊓ Gamma0 (d * M)) (τ : ℍ)
    [Fintype (OrbitQuot M d τ)] :
    (∑ q : OrbitQuot M d τ, (analyticPlace hT (rep M d τ q)).ord
      (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ))) =
      ∑ᶠ P : Fiber M d τ, P.1.ord (jCoordinateOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ -
        algebraMap ℂ (functionFieldOver (Gamma1 M ⊓ Gamma0 (d * M)) ℂ) (JMultiplicity.jf τ)) := by
  letI : Finite (Fiber M d τ) := Finite.of_equiv (OrbitQuot M d τ) (equiv M d hT τ)
  letI : Fintype (Fiber M d τ) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  exact Fintype.sum_equiv (equiv M d hT τ) _ _ (fun _ => rfl)

end
end Dubon2026.SourceFunctionField.GammaOne.HeckeFiberOrbits
