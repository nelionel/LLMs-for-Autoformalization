import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
assert_not_exists Finset
namespace TwoSidedIdeal
section ker
variable {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocSemiring S]
variable {F : Type*} [FunLike F R S] [NonUnitalRingHomClass F R S]
variable (f : F)
def ker : TwoSidedIdeal R :=
  .mk
  { r := fun x y ↦ f x = f y
    iseqv := by constructor <;> aesop
    mul' := by intro; simp_all [map_add]
    add' := by intro; simp_all [map_mul] }
@[simp]
lemma ker_ringCon {x y : R} : (ker f).ringCon x y ↔ f x = f y := Iff.rfl
lemma mem_ker {x : R} : x ∈ ker f ↔ f x = 0 := by
  rw [mem_iff, ker_ringCon, map_zero]
lemma ker_eq_bot : ker f = ⊥ ↔ Function.Injective f := by
  fconstructor
  · intro h x y hxy
    simpa [h, rel_iff, mem_bot, sub_eq_zero] using show (ker f).ringCon x y from hxy
  · exact fun h ↦ eq_bot_iff.2 fun x hx => h hx
section NonAssocRing
variable {R : Type*} [NonAssocRing R]
@[simp]
lemma ker_ringCon_mk' (I : TwoSidedIdeal R) : ker I.ringCon.mk' = I :=
  le_antisymm
    (fun _ h => by simpa using I.rel_iff _ _ |>.1 (Quotient.eq'.1 h))
    (fun _ h => Quotient.sound' <| I.rel_iff _ _ |>.2 (by simpa using h))
end NonAssocRing
end ker
end TwoSidedIdeal