import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Subsemigroup.Basic
import Mathlib.RingTheory.NonUnitalSubsemiring.Basic
import Mathlib.Algebra.Star.Center
universe v w w'
variable {A : Type v} {B : Type w} {C : Type w'}
structure SubStarSemigroup (M : Type v) [Mul M] [Star M] extends Subsemigroup M : Type v where
  star_mem' : ∀ {a : M} (_ha : a ∈ carrier), star a ∈ carrier
add_decl_doc SubStarSemigroup.toSubsemigroup
structure NonUnitalStarSubsemiring (R : Type v) [NonUnitalNonAssocSemiring R] [Star R]
    extends NonUnitalSubsemiring R : Type v where
  star_mem' : ∀ {a : R} (_ha : a ∈ carrier), star a ∈ carrier
add_decl_doc NonUnitalStarSubsemiring.toNonUnitalSubsemiring
section NonUnitalStarSubsemiring
namespace NonUnitalStarSubsemiring
variable {R : Type v} [NonUnitalNonAssocSemiring R] [StarRing R]
instance instSetLike : SetLike (NonUnitalStarSubsemiring R) R where
  coe {s} := s.carrier
  coe_injective' p q h := by cases p; cases q; congr; exact SetLike.coe_injective h
instance instNonUnitalSubsemiringClass : NonUnitalSubsemiringClass (NonUnitalStarSubsemiring R) R
    where
  add_mem {s} := s.add_mem'
  mul_mem {s} := s.mul_mem'
  zero_mem {s} := s.zero_mem'
instance instStarMemClass : StarMemClass (NonUnitalStarSubsemiring R) R where
  star_mem {s} := s.star_mem'
theorem mem_carrier {s : NonUnitalStarSubsemiring R} {x : R} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl
protected def copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    NonUnitalStarSubsemiring R :=
  { S.toNonUnitalSubsemiring.copy s hs with
    star_mem' := fun {x} (hx : x ∈ s) => by
      show star x ∈ s
      rw [hs] at hx ⊢
      exact S.star_mem' hx }
@[simp]
theorem coe_copy (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) :
    (S.copy s hs : Set R) = s :=
  rfl
theorem copy_eq (S : NonUnitalStarSubsemiring R) (s : Set R) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs
section Center
variable (R)
def center (R) [NonUnitalNonAssocSemiring R] [StarRing R] : NonUnitalStarSubsemiring R where
  toNonUnitalSubsemiring := NonUnitalSubsemiring.center R
  star_mem' := Set.star_mem_center
end Center
end NonUnitalStarSubsemiring
end NonUnitalStarSubsemiring