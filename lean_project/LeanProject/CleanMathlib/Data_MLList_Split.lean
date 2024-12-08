import Batteries.Data.MLList.Basic
import Mathlib.Data.ULift
set_option linter.deprecated false
namespace MLList
universe u
variable {α β : Type u} {m : Type u → Type u} [Monad m]
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def getUpToFirstM (L : MLList m α) (p : α → m (ULift Bool)) : m (List α × MLList m α) := do
  match ← L.uncons with
  | none => return ([], nil)
  | some (x, xs) => (if (← p x).down then
      return ([x], xs)
    else do
      let (acc, R) ← getUpToFirstM xs p
      return (x :: acc, R))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def getUpToFirst (L : MLList m α) (p : α → Bool) : m (List α × MLList m α) :=
  L.getUpToFirstM fun a => pure (.up (p a))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def splitWhileM (L : MLList m α) (p : α → m (ULift Bool)) :
    m (List α × MLList m α) := do
  match ← L.uncons with
  | none => return ([], nil)
  | some (x, xs) => (if (← p x).down then do
      let (acc, R) ← splitWhileM xs p
      return (x :: acc, R)
    else
      return ([], cons x xs))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def splitWhile (L : MLList m α) (p : α → Bool) : m (List α × MLList m α) :=
  L.splitWhileM fun a => pure (.up (p a))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def groupByM [DecidableEq β] (L : MLList m α) (f : α → m β) : MLList m (β × List α) :=
  L.cases (fun _ => nil) fun a t => squash fun _ => do
    let b ← f a
    let (l, t') ← t.splitWhileM (fun a => do return .up ((← f a) = b))
    return cons (b, a :: l) (t'.groupByM f)
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def groupBy [DecidableEq β] (L : MLList m α) (f : α → β) : MLList m (β × List α) :=
  L.groupByM fun a => pure (f a)
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
partial def splitAtBecomesTrueM (L : MLList m α) (p : α → m (ULift Bool)) : MLList m (List α) :=
  aux (L.groupByM p)
where aux (M : MLList m (ULift.{u} Bool × List α)) : MLList m (List α) :=
  M.cases (fun _ => nil) fun (b, l) t => (if b.down then
    t.cases (fun _ => cons l nil)
      fun (_, l') t' => cons (l ++ l') (aux t')
  else
    cons l (aux t))
@[deprecated "See deprecation note in module documentation." (since := "2024-08-22")]
def splitAtBecomesTrue (L : MLList m α) (p : α → Bool) : MLList m (List α) :=
  L.splitAtBecomesTrueM fun a => pure (.up (p a))
end MLList