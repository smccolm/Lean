import Dubon2026.ScalarLatticeFiltration
import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Separation of the original scalar lattice filtration -/

namespace Dubon2026

/-- Original adic separation forces the literal scalar-power lattice
intersection inside the original ambient ring to be zero. -/
theorem scalarLatticeImage_separated_of_isHausdorff
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A : Submodule R S) (I : Ideal R) [IsHausdorff I A]
    (π : R) (hπ : π ∈ I) (x : S)
    (hx : ∀ j : ℕ, x ∈ scalarLatticeImage A (π ^ j)) : x = 0 := by
  have hA : x ∈ A := scalarLatticeImage_le A (π ^ 0) (hx 0)
  have hz : (⟨x, hA⟩ : A) = 0 := by
    apply IsHausdorff.haus' (I := I)
    intro j
    apply SModEq.zero.mpr
    obtain ⟨a, ha, he⟩ := (mem_scalarLatticeImage A (π ^ j) x).mp (hx j)
    have hm : π ^ j • (⟨a, ha⟩ : A) ∈ (I ^ j • (⊤ : Submodule R A)) :=
      Submodule.smul_mem_smul (Ideal.pow_mem_pow hπ j) (Submodule.mem_top)
    have hid : π ^ j • (⟨a, ha⟩ : A) = ⟨x, hA⟩ := Subtype.ext he
    rwa [hid] at hm
  exact congrArg (fun a : A => (a : S)) hz

end Dubon2026
