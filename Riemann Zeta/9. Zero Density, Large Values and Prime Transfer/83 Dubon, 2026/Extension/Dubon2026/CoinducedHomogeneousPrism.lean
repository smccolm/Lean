import Dubon2026.CoinducedHomogeneousCocycles

/-! # Explicit low-degree prism identities for original coinduced cocycles

The identities compare the original homogeneous values with a changed vertex
map. They apply to the actual subgroup coordinate in both Shapiro composites,
without normalization assumptions. They are the algebraic core of the inverse
homotopies needed in DUB-17's continuous local duality route.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G] (A : Rep.{0} R G) (S : Subgroup G)

/-- The original edge cocycle differs under a vertex change by the explicit
degree-zero boundary. No vertex or cocycle normalization is assumed. -/
theorem coinducedHomogeneousOne_prism
    (c : groupCohomology.cocycles₁ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y px py : G) :
    coinducedHomogeneousOne A S c y py - coinducedHomogeneousOne A S c x px =
      coinducedHomogeneousOne A S c px py - coinducedHomogeneousOne A S c x y := by
  have h₁ := coinducedHomogeneousOne_cocycle A S c x px py
  have h₂ := coinducedHomogeneousOne_cocycle A S c x y py
  have he := h₁.symm.trans h₂
  apply sub_eq_zero.mp
  calc
    _ = (coinducedHomogeneousOne A S c y py + coinducedHomogeneousOne A S c x y) -
        (coinducedHomogeneousOne A S c px py + coinducedHomogeneousOne A S c x px) := by abel
    _ = 0 := sub_eq_zero.mpr he.symm

/-- The original triangle cocycle differs under a vertex change by the boundary
of the explicit two-triangle prism. This preserves the precise signs needed in H2. -/
theorem coinducedHomogeneousTwo_prism
    (c : groupCohomology.cocycles₂ (Rep.coind S.subtype (Rep.res S.subtype A)))
    (x y z px py pz : G) :
    (coinducedHomogeneousTwo A S c y py pz - coinducedHomogeneousTwo A S c y z pz) -
      (coinducedHomogeneousTwo A S c x px pz - coinducedHomogeneousTwo A S c x z pz) +
      (coinducedHomogeneousTwo A S c x px py - coinducedHomogeneousTwo A S c x y py) =
        coinducedHomogeneousTwo A S c px py pz - coinducedHomogeneousTwo A S c x y z := by
  have h₁ := coinducedHomogeneousTwo_cocycle A S c x y py pz
  have h₂ := coinducedHomogeneousTwo_cocycle A S c x px py pz
  have h₃ := coinducedHomogeneousTwo_cocycle A S c x y z pz
  have he := congrArg₂ (fun a b : A => a - b)
    (congrArg₂ (fun a b : A => a + b) h₂ h₃) h₁
  apply sub_eq_zero.mp
  calc
    _ = ((coinducedHomogeneousTwo A S c x py pz + coinducedHomogeneousTwo A S c x px py) +
          (coinducedHomogeneousTwo A S c x z pz + coinducedHomogeneousTwo A S c x y z) -
          (coinducedHomogeneousTwo A S c x py pz + coinducedHomogeneousTwo A S c x y py)) -
        ((coinducedHomogeneousTwo A S c px py pz + coinducedHomogeneousTwo A S c x px pz) +
          (coinducedHomogeneousTwo A S c y z pz + coinducedHomogeneousTwo A S c x y pz) -
          (coinducedHomogeneousTwo A S c y py pz + coinducedHomogeneousTwo A S c x y pz)) := by abel
    _ = 0 := sub_eq_zero.mpr he

end
end Dubon2026
