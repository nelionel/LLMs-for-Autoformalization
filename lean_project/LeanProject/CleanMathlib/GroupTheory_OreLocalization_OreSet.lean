import Mathlib.Algebra.Group.Submonoid.Defs
namespace AddOreLocalization
class AddOreSet {R : Type*} [AddMonoid R] (S : AddSubmonoid R) where
  ore_right_cancel : ∀ (r₁ r₂ : R) (s : S), r₁ + s = r₂ + s → ∃ s' : S, s' + r₁ = s' + r₂
  oreMin : R → S → R
  oreSubtra : R → S → S
  ore_eq : ∀ (r : R) (s : S), oreSubtra r s + r = oreMin r s + s
end AddOreLocalization
namespace OreLocalization
section Monoid
@[to_additive AddOreLocalization.AddOreSet]
class OreSet {R : Type*} [Monoid R] (S : Submonoid R) where
  ore_right_cancel : ∀ (r₁ r₂ : R) (s : S), r₁ * s = r₂ * s → ∃ s' : S, s' * r₁ = s' * r₂
  oreNum : R → S → R
  oreDenom : R → S → S
  ore_eq : ∀ (r : R) (s : S), oreDenom r s * r = oreNum r s * s
variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
@[to_additive AddOreLocalization.ore_right_cancel]
theorem ore_right_cancel (r₁ r₂ : R) (s : S) (h : r₁ * s = r₂ * s) : ∃ s' : S, s' * r₁ = s' * r₂ :=
  OreSet.ore_right_cancel r₁ r₂ s h
@[to_additive AddOreLocalization.oreMin "The Ore minuend of a difference."]
def oreNum (r : R) (s : S) : R :=
  OreSet.oreNum r s
@[to_additive AddOreLocalization.oreSubtra "The Ore subtrahend of a difference."]
def oreDenom (r : R) (s : S) : S :=
  OreSet.oreDenom r s
@[to_additive AddOreLocalization.add_ore_eq
  "The Ore condition of a difference, expressed in terms of `oreMin` and `oreSubtra`."]
theorem ore_eq (r : R) (s : S) : oreDenom r s * r = oreNum r s * s :=
  OreSet.ore_eq r s
@[to_additive AddOreLocalization.addOreCondition
  "The Ore condition bundled in a sigma type. This is useful in situations where we want to obtain
both witnesses and the condition for a given difference."]
def oreCondition (r : R) (s : S) : Σ'r' : R, Σ's' : S, s' * r = r' * s :=
  ⟨oreNum r s, oreDenom r s, ore_eq r s⟩
@[to_additive AddOreLocalization.addOreSetBot]
instance oreSetBot : OreSet (⊥ : Submonoid R) where
  ore_right_cancel _ _ s h :=
    ⟨s, by
      rcases s with ⟨s, hs⟩
      rw [Submonoid.mem_bot] at hs
      subst hs
      rw [mul_one, mul_one] at h
      subst h
      rfl⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq _ s := by
    rcases s with ⟨s, hs⟩
    rw [Submonoid.mem_bot] at hs
    simp [hs]
@[to_additive AddOreLocalization.addOreSetComm]
instance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where
  ore_right_cancel m n s h := ⟨s, by rw [mul_comm (s : R) n, mul_comm (s : R) m, h]⟩
  oreNum r _ := r
  oreDenom _ s := s
  ore_eq r s := by rw [mul_comm]
end Monoid
end OreLocalization