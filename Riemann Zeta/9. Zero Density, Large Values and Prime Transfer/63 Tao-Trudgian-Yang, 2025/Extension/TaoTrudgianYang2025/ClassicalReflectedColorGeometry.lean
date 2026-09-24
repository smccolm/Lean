import TaoTrudgianYang2025.ClassicalReflectedCompactTransfer

/-!
# Refining the actual separation coloring by physical block labels

Adding a dyadic label to the parity/rank color preserves one-separation.
This is an injection of color fibers, not an identification of ordinates.
-/

noncomputable section
namespace TaoTrudgianYang2025

theorem oneSeparated_on_labeled_boundedMultiplicityColor
    {ι κ : Type*} [Fintype ι] [LinearOrder ι]
    (W : ι → ℝ) (label : ι → κ) (L : ℕ)
    (hlocal : ∀ z : ℤ, (unitBinFinset W z).card ≤ L)
    (c : κ × (ZMod 2 × Fin (L+1))) :
    ∀ x : EnergyColorFiber (fun i => (label i,boundedMultiplicityColor W L hlocal i)) c,
      ∀ y : EnergyColorFiber (fun i => (label i,boundedMultiplicityColor W L hlocal i)) c,
        x ≠ y → 1 ≤ |W x.1-W y.1| := by
  intro x y hxy
  let fx : EnergyColorFiber (boundedMultiplicityColor W L hlocal) c.2 :=
    ⟨x.1,congrArg Prod.snd x.2⟩
  let fy : EnergyColorFiber (boundedMultiplicityColor W L hlocal) c.2 :=
    ⟨y.1,congrArg Prod.snd y.2⟩
  have hne : fx ≠ fy := by
    intro h
    have hval : x.1 = y.1 :=
      congrArg (fun z : EnergyColorFiber (boundedMultiplicityColor W L hlocal) c.2 => z.1) h
    exact hxy (Subtype.ext hval)
  exact oneSeparated_on_boundedMultiplicityColor W L hlocal c.2 fx fy hne

end TaoTrudgianYang2025
