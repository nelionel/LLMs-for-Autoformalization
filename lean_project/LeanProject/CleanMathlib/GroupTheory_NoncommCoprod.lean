import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Prod
assert_not_exists MonoidWithZero
namespace MulHom
variable {M N P : Type*} [Mul M] [Mul N] [Semigroup P]
  (f : M →ₙ* P) (g : N →ₙ* P)
@[to_additive (attr := simps)
    "Coproduct of two `AddHom`s with the same codomain with `AddCommute` assumption:
    `f.noncommCoprod g _ (p : M × N) = f p.1 + g p.2`.
    (For the commutative case, use `AddHom.coprod`)"]
def noncommCoprod (comm : ∀ m n, Commute (f m) (g n)) : M × N →ₙ* P where
  toFun mn := f mn.fst * g mn.snd
  map_mul' mn mn' := by simpa using (comm _ _).mul_mul_mul_comm _ _
@[to_additive
  "Variant of `AddHom.noncommCoprod_apply`, with the sum written in the other direction"]
theorem noncommCoprod_apply' (comm) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, noncommCoprod_apply]
@[to_additive]
theorem comp_noncommCoprod {Q : Type*} [Semigroup Q] (h : P →ₙ* Q)
    (comm : ∀ m n, Commute (f m) (g n)) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun _ => map_mul h _ _
end MulHom
namespace MonoidHom
variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]
  (f : M →* P) (g : N →* P) (comm : ∀ m n, Commute (f m) (g n))
@[to_additive (attr := simps)
    "Coproduct of two `AddMonoidHom`s with the same codomain,
    with a commutation assumption:
    `f.noncommCoprod g (p : M × N) = f p.1 + g p.2`.
    (Noncommutative case; in the commutative case, use `AddHom.coprod`.)"]
def noncommCoprod : M × N →* P where
  toFun := fun mn ↦ (f mn.fst) * (g mn.snd)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  __ := f.toMulHom.noncommCoprod g.toMulHom comm
@[to_additive
  "Variant of `AddMonoidHom.noncomCoprod_apply` with the sum written in the other direction"]
theorem noncommCoprod_apply' (comm) (mn : M × N) :
    (f.noncommCoprod g comm) mn = g mn.2 * f mn.1 := by
  rw [← comm, MonoidHom.noncommCoprod_apply]
@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inl : (f.noncommCoprod g comm).comp (inl M N) = f :=
  ext fun x => by simp
@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inr : (f.noncommCoprod g comm).comp (inr M N) = g :=
  ext fun x => by simp
@[to_additive (attr := simp)]
theorem noncommCoprod_unique (f : M × N →* P) :
    (f.comp (inl M N)).noncommCoprod (f.comp (inr M N)) (fun _ _ => (commute_inl_inr _ _).map f)
      = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]
@[to_additive (attr := simp)]
theorem noncommCoprod_inl_inr {M N : Type*} [Monoid M] [Monoid N] :
    (inl M N).noncommCoprod (inr M N) commute_inl_inr = id (M × N) :=
  noncommCoprod_unique <| .id (M × N)
@[to_additive]
theorem comp_noncommCoprod {Q : Type*} [Monoid Q] (h : P →* Q) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun x => by simp
end MonoidHom