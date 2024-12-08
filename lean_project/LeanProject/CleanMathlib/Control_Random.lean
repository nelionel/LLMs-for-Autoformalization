import Mathlib.Control.ULiftable
import Mathlib.Order.Fin.Basic
set_option autoImplicit true 
abbrev RandGT (g : Type) := StateT (ULift g)
abbrev RandG (g : Type) := RandGT g Id
abbrev RandT := RandGT StdGen
abbrev Rand := RandG StdGen
instance [MonadLift m n] : MonadLiftT (RandGT g m) (RandGT g n) where
  monadLift x := fun s => x s
class Random (m) (α : Type u) where
  random [RandomGen g] : RandGT g m α
class BoundedRandom (m) (α : Type u) [Preorder α] where
  randomR {g : Type} (lo hi : α) (h : lo ≤ hi) [RandomGen g] : RandGT g m {a // lo ≤ a ∧ a ≤ hi}
namespace Rand
def next [RandomGen g] [Monad m] : RandGT g m Nat := do
  let rng := (← get).down
  let (res, new) := RandomGen.next rng
  set (ULift.up new)
  pure res
def split {g : Type} [RandomGen g] [Monad m] : RandGT g m g := do
  let rng := (← get).down
  let (r1, r2) := RandomGen.split rng
  set (ULift.up r1)
  pure r2
def range {g : Type} [RandomGen g] [Monad m] : RandGT g m (Nat × Nat) := do
  let rng := (← get).down
  pure <| RandomGen.range rng
end Rand
namespace Random
open Rand
variable [Monad m]
def rand (α : Type u) [Random m α] [RandomGen g] : RandGT g m α := Random.random
def randBound (α : Type u)
    [Preorder α] [BoundedRandom m α] (lo hi : α) (h : lo ≤ hi) [RandomGen g] :
    RandGT g m {a // lo ≤ a ∧ a ≤ hi} :=
  (BoundedRandom.randomR lo hi h : RandGT g _ _)
def randFin {n : Nat} [RandomGen g] : RandGT g m (Fin n.succ) :=
  fun ⟨g⟩ ↦ pure <| randNat g 0 n |>.map (Fin.ofNat' _) ULift.up
instance {n : Nat} : Random m (Fin n.succ) where
  random := randFin
def randBool [RandomGen g] : RandGT g m Bool :=
  return (← rand (Fin 2)) == 1
instance : Random m Bool where
  random := randBool
instance {α : Type u} [ULiftable m m'] [Random m α] : Random m' (ULift.{v} α) where
  random := ULiftable.up random
instance : BoundedRandom m Nat where
  randomR lo hi h _ := do
    let z ← rand (Fin (hi - lo).succ)
    pure ⟨
      lo + z.val, Nat.le_add_right _ _,
      Nat.add_le_of_le_sub' h (Nat.le_of_succ_le_succ z.isLt)
    ⟩
instance : BoundedRandom m Int where
  randomR lo hi h _ := do
    let ⟨z, _, h2⟩ ← randBound Nat 0 (Int.natAbs <| hi - lo) (Nat.zero_le _)
    pure ⟨
      z + lo,
      Int.le_add_of_nonneg_left (Int.ofNat_zero_le z),
      Int.add_le_of_le_sub_right <| Int.le_trans
        (Int.ofNat_le.mpr h2)
        (le_of_eq <| Int.natAbs_of_nonneg <| Int.sub_nonneg_of_le h)⟩
instance {n : Nat} : BoundedRandom m (Fin n) where
  randomR lo hi h _ := do
    let ⟨r, h1, h2⟩ ← randBound Nat lo.val hi.val h
    pure ⟨⟨r, Nat.lt_of_le_of_lt h2 hi.isLt⟩, h1, h2⟩
instance {α : Type u} [Preorder α] [ULiftable m m'] [BoundedRandom m α] [Monad m'] :
    BoundedRandom m' (ULift.{v} α) where
  randomR lo hi h := do
    let ⟨x⟩ ← ULiftable.up.{v} (BoundedRandom.randomR lo.down hi.down h)
    pure ⟨ULift.up x.val, x.prop⟩
end Random
namespace IO
variable {m : Type* → Type*} {m₀ : Type → Type}
variable [Monad m] [MonadLiftT (ST RealWorld) m₀] [ULiftable m₀ m]
def runRand (cmd : RandT m α) : m α := do
  let stdGen ← ULiftable.up (stdGenRef.get : m₀ _)
  let (res, new) ← StateT.run cmd stdGen
  let _ ← ULiftable.up (stdGenRef.set new.down : m₀ _)
  pure res
def runRandWith (seed : Nat) (cmd : RandT m α) : m α := do
  pure <| (← cmd.run (ULift.up <| mkStdGen seed)).1
end IO