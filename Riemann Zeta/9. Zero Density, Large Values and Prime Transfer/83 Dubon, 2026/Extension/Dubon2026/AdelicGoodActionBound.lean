import Dubon2026.AdelicGoodTailTensorInvariance

/-! # Genuine finite stage bounds for the original adelic action -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable (N : ℕ) [NeZero N]

/-- Every original adelic matrix is in local level at every good place beyond some genuine finite initial family. -/
theorem adelicGoodLevelOutside_exists (a : RationalAdelicGL2) :
    ∃ n, ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin n, w ≠ goodAdelicPlaceInitial N n i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w := by
  obtain ⟨S, hS⟩ := finiteAdeleGL2Gamma0_exists_exceptional_finset N (rationalAdelicGL2RealFiniteEquiv a).2
  obtain ⟨n, hn⟩ := goodAdelicPlaceInitial_covers_finset N S
  refine ⟨n, fun w hw hout => hS w ?_⟩
  intro hwS
  obtain ⟨i, hi⟩ := hn w hwS hw
  exact hout i hi.symm

/-- Enlarging the genuine initial family preserves the original local-level condition outside it. -/
theorem adelicGoodLevelOutside_mono (a : RationalAdelicGL2) {n m : ℕ} (hnm : n ≤ m)
    (ha : ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin n, w ≠ goodAdelicPlaceInitial N n i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w) :
    ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin m, w ≠ goodAdelicPlaceInitial N m i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w := by
  intro w hw hout
  apply ha w hw
  intro i hi
  exact hout (i.castLE hnm) hi

/-- A genuine finite bound containing the exceptional good coordinates of the original matrix. -/
def adelicGoodActionBound (a : RationalAdelicGL2) : ℕ := (adelicGoodLevelOutside_exists N a).choose

/-- The actual chosen bound has the proved original local-level property. -/
theorem adelicGoodActionBound_spec (a : RationalAdelicGL2) (m : ℕ) (hm : adelicGoodActionBound N a ≤ m) :
    ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin m, w ≠ goodAdelicPlaceInitial N m i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w :=
  adelicGoodLevelOutside_mono N a hm (adelicGoodLevelOutside_exists N a).choose_spec

/-- The actual target stage accommodates both an original finite tensor and the original matrix's good-place exceptions. -/
def adelicActionStage (a : RationalAdelicGL2) (n : ℕ) : ℕ := max (adelicGoodActionBound N a) n

/-- The chosen action stage contains every factor of the original input tensor. -/
theorem le_adelicActionStage (a : RationalAdelicGL2) (n : ℕ) : n ≤ adelicActionStage N a n := le_max_right _ _

/-- Outside the actual action stage every original good coordinate of the acting matrix is in local level. -/
theorem adelicActionStage_spec (a : RationalAdelicGL2) (n : ℕ) :
    ∀ w, IsGoodAdelicPlace N w → (∀ i : Fin (adelicActionStage N a n), w ≠ goodAdelicPlaceInitial N (adelicActionStage N a n) i) →
      adelicPlaceGL2Hom w a ∈ finitePlaceGL2Gamma0 N w :=
  adelicGoodActionBound_spec N a _ (le_max_left _ _)

end
end Dubon2026
