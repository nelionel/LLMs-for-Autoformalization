import Mathlib.Data.Nat.Notation
import Mathlib.Control.Functor
import Mathlib.Data.SProd
import Mathlib.Util.CompileInductive
import Batteries.Tactic.Lint.Basic
import Batteries.Data.List.Lemmas
import Batteries.Data.RBMap.Basic
import Batteries.Logic
namespace List
open Function Nat
universe u v w x
variable {α β γ δ ε ζ : Type*}
instance [DecidableEq α] : SDiff (List α) :=
  ⟨List.diff⟩
def getI [Inhabited α] (l : List α) (n : Nat) : α :=
  getD l n default
def headI [Inhabited α] : List α → α
  | []       => default
  | (a :: _) => a
@[simp] theorem headI_nil [Inhabited α] : ([] : List α).headI = default := rfl
@[simp] theorem headI_cons [Inhabited α] {h : α} {t : List α} : (h :: t).headI = h := rfl
def getLastI [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => getLastI l
@[inline, deprecated List.pure (since := "2024-03-24")]
protected def ret {α : Type u} (a : α) : List α := [a]
def takeI [Inhabited α] (n : Nat) (l : List α) : List α :=
  takeD n l default
def findM {α} {m : Type u → Type v} [Alternative m] (tac : α → m PUnit) : List α → m α :=
  List.firstM fun a => (tac a) $> a
def findM?'
    {m : Type u → Type v}
    [Monad m] {α : Type u}
    (p : α → m (ULift Bool)) : List α → m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else findM?' p xs
section
variable {m : Type → Type v} [Monad m]
def orM : List (m Bool) → m Bool :=
  anyM id
def andM : List (m Bool) → m Bool :=
  allM id
end
section foldIdxM
variable {m : Type v → Type w} [Monad m]
def foldlIdxM {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)
def foldrIdxM {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)
end foldIdxM
section mapIdxM
variable {m : Type v → Type w} [Monad m]
def mapIdxMAux' {α} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mapIdxMAux' f (i + 1) as
def mapIdxM' {α} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mapIdxMAux' f 0 as
end mapIdxM
@[simp]
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l
section Permutations
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x : List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)
def permutationsAux.rec {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec H0 H1 ts (t :: is)) (permutationsAux.rec H0 H1 is [])
  termination_by ts is => (length ts + length is, length ts)
  decreasing_by all_goals (simp_wf; omega)
def permutationsAux : List α → List α → List (List α) :=
  permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []
@[simp]
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'Aux t ys).map (cons y)
@[simp]
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).flatMap <| permutations'Aux t
end Permutations
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp p l
      (a', a :: l')
instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product
section Chain
instance decidableChain {R : α → α → Prop} [DecidableRel R] (a : α) (l : List α) :
    Decidable (Chain R a l) := by
  induction l generalizing a with
  | nil => simp only [List.Chain.nil]; infer_instance
  | cons a as ih => haveI := ih; simp only [List.chain_cons]; infer_instance
instance decidableChain' {R : α → α → Prop} [DecidableRel R] (l : List α) :
    Decidable (Chain' R l) := by
  cases l <;> dsimp only [List.Chain'] <;> infer_instance
end Chain
def dedup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)
def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' R h l else destutter' R a l
def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []
section Choose
variable (p : α → Prop) [DecidablePred p] (l : List α)
def chooseX : ∀ l : List α, ∀ _ : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun a h => not_mem_nil a h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨mem_cons.mpr <| Or.inl rfl, pl⟩⟩
    else
      let ⟨a, ha⟩ :=
        chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, mem_cons.mpr <| Or.inr ha.1, ha.2⟩
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
end Choose
def mapDiagM' {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
  | [] => return ()
  | h :: t => do
    _ ← f h h
    _ ← t.mapM' (f h)
    t.mapDiagM' f
@[simp]
def map₂Left' (f : α → Option β → γ) : List α → List β → List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs =>
    let rec' := map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)
def map₂Right' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left' (flip f) bs as
@[simp]
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂Left f as bs
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as
def mapAsyncChunked {α β} (f : α → β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).flatMap Task.get
def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith3 f xs ys zs
  | _, _, _ => []
def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith4 f xs ys zs us
  | _, _, _, _ => []
def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith5 f xs ys zs us vs
  | _, _, _, _, _ => []
def replaceIf : List α → List Bool → List α → List α
  | l, _, [] => l
  | [], _, _ => []
  | l, [], _ => l
  | n :: ns, tf :: bs, e@(c :: cs) => if tf then c :: ns.replaceIf bs cs else n :: ns.replaceIf bs e
@[simp]
def iterate (f : α → α) (a : α) : (n : ℕ) → List α
  | 0     => []
  | n + 1 => a :: iterate f (f a) n
@[inline]
def iterateTR (f : α → α) (a : α) (n : ℕ) : List α :=
  loop a n []
where
  @[simp, specialize]
  loop (a : α) (n : ℕ) (l : List α) : List α :=
    match n with
    | 0     => reverse l
    | n + 1 => loop (f a) n (a :: l)
theorem iterateTR_loop_eq (f : α → α) (a : α) (n : ℕ) (l : List α) :
    iterateTR.loop f a n l = reverse l ++ iterate f a n := by
  induction n generalizing a l <;> simp [*]
@[csimp]
theorem iterate_eq_iterateTR : @iterate = @iterateTR := by
  funext α f a n
  exact Eq.symm <| iterateTR_loop_eq f a n []
section MapAccumr
def mapAccumr (f : α → γ → γ × β) : List α → γ → γ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
@[simp]
theorem length_mapAccumr :
    ∀ (f : α → γ → γ × β) (x : List α) (s : γ), length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congr_arg succ (length_mapAccumr f x s)
  | _, [], _ => rfl
def mapAccumr₂ (f : α → β → γ → γ × δ) : List α → List β → γ → γ × List δ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
@[simp]
theorem length_mapAccumr₂ :
    ∀ (f : α → β → γ → γ × δ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (succ_min_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl
end MapAccumr
set_option allowUnsafeReducibility true in
attribute [semireducible] Fin.foldr.loop
section Deprecated
@[deprecated List.mem_cons (since := "2024-08-10")]
theorem mem_cons_eq (a y : α) (l : List α) : (a ∈ y :: l) = (a = y ∨ a ∈ l) :=
  propext List.mem_cons
alias ⟨eq_or_mem_of_mem_cons, _⟩ := mem_cons
@[deprecated List.not_mem_nil (since := "2024-08-10")]
theorem not_exists_mem_nil (p : α → Prop) : ¬∃ x ∈ @nil α, p x :=
  fun ⟨_, hx, _⟩ => List.not_mem_nil _ hx
@[deprecated (since := "2024-03-23")] alias not_bex_nil := not_exists_mem_nil
@[deprecated (since := "2024-03-23")] alias bex_cons := exists_mem_cons
@[deprecated (since := "2024-08-10")] alias length_le_of_sublist := Sublist.length_le
end Deprecated
end List