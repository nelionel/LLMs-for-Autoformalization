import Mathlib.Order.Compare
import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.PSub
import Mathlib.Data.Option.Basic
universe u
inductive Ordnode (α : Type u) : Type u
  | nil : Ordnode α
  | node (size : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
compile_inductive% Ordnode
namespace Ordnode
variable {α : Type*}
instance : EmptyCollection (Ordnode α) :=
  ⟨nil⟩
instance : Inhabited (Ordnode α) :=
  ⟨nil⟩
@[inline]
def delta :=
  3
@[inline]
def ratio :=
  2
@[inline]
protected def singleton (a : α) : Ordnode α :=
  node 1 nil a nil
local prefix:arg "ι" => Ordnode.singleton
instance : Singleton α (Ordnode α) :=
  ⟨Ordnode.singleton⟩
@[inline]
def size : Ordnode α → ℕ
  | nil => 0
  | node sz _ _ _ => sz
@[simp] theorem size_nil : size (nil : Ordnode α) = 0 :=
  rfl
@[simp] theorem size_node (sz : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α) :
    size (node sz l x r) = sz :=
  rfl
@[inline]
def empty : Ordnode α → Bool
  | nil => true
  | node _ _ _ _ => false
@[simp]
def dual : Ordnode α → Ordnode α
  | nil => nil
  | node s l x r => node s (dual r) x (dual l)
@[inline, reducible]
def node' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  node (size l + size r + 1) l x r
def repr {α} [Repr α] (o : Ordnode α) (n : ℕ) : Std.Format :=
  match o with
  | nil => (Std.Format.text "∅")
  | node _ l x r =>
      let fmt := Std.Format.joinSep
        [repr l n, Repr.reprPrec x n, repr r n]
        " "
      Std.Format.paren fmt
instance {α} [Repr α] : Repr (Ordnode α) :=
  ⟨repr⟩
def balanceL (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id r with _ | rs
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact ι x
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3 ll lx ι x
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
  · rcases id l with _ | ⟨ls, ll, lx, lr⟩
    · exact node (rs + 1) nil x r
    · refine if ls > delta * rs then ?_ else node (ls + rs + 1) l x r
      rcases id ll with _ | lls
      · exact nil
      rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
      · exact nil
      exact
        if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (rs + lrs + 1) lr x r)
        else
          node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
            (node (size lrr + rs + 1) lrr x r)
def balanceR (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id l with _ | ls
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rr with _ | rrs
      · rcases rl with _ | ⟨_, _, rlx⟩
        · exact node 2 nil x r
        · exact node 3 (ι x) rlx ι rx
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact node 3 (ι x) rx rr
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact node (ls + 1) l x nil
    · refine if rs > delta * ls then ?_ else node (ls + rs + 1) l x r
      rcases id rr with _ | rrs
      · exact nil
      rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · exact nil
      exact
        if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
        else
          node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
            (node (size rlr + rrs + 1) rlr rx rr)
def balance (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α := by
  rcases id l with _ | ⟨ls, ll, lx, lr⟩
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · exact ι x
    · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
      · cases id rr
        · exact node 2 nil x r
        · exact node 3 (ι x) rx rr
      · rcases id rr with _ | rrs
        · exact node 3 (ι x) rlx ι rx
        · exact
            if rls < ratio * rrs then node (rs + 1) (node (rls + 1) nil x rl) rx rr
            else
              node (rs + 1) (node (size rll + 1) nil x rll) rlx
                (node (size rlr + rrs + 1) rlr rx rr)
  · rcases id r with _ | ⟨rs, rl, rx, rr⟩
    · rcases id ll with _ | lls
      · rcases lr with _ | ⟨_, _, lrx⟩
        · exact node 2 l x nil
        · exact node 3 (ι lx) lrx ι x
      · rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact node 3 ll lx ι x
        · exact
            if lrs < ratio * lls then node (ls + 1) ll lx (node (lrs + 1) lr x nil)
            else
              node (ls + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
                (node (size lrr + 1) lrr x nil)
    · refine
        if delta * ls < rs then ?_ else if delta * rs < ls then ?_ else node (ls + rs + 1) l x r
      · rcases id rl with _ | ⟨rls, rll, rlx, rlr⟩
        · exact nil
        rcases id rr with _ | rrs
        · exact nil
        exact
          if rls < ratio * rrs then node (ls + rs + 1) (node (ls + rls + 1) l x rl) rx rr
          else
            node (ls + rs + 1) (node (ls + size rll + 1) l x rll) rlx
              (node (size rlr + rrs + 1) rlr rx rr)
      · rcases id ll with _ | lls
        · exact nil
        rcases id lr with _ | ⟨lrs, lrl, lrx, lrr⟩
        · exact nil
        exact
          if lrs < ratio * lls then node (ls + rs + 1) ll lx (node (lrs + rs + 1) lr x r)
          else
            node (ls + rs + 1) (node (lls + size lrl + 1) ll lx lrl) lrx
              (node (size lrr + rs + 1) lrr x r)
def All (P : α → Prop) : Ordnode α → Prop
  | nil => True
  | node _ l x r => All P l ∧ P x ∧ All P r
instance All.decidable {P : α → Prop} : (t : Ordnode α) → [DecidablePred P] → Decidable (All P t)
  | nil => isTrue trivial
  | node _ l m r =>
    have : Decidable (All P l) := All.decidable l
    have : Decidable (All P r) := All.decidable r
    inferInstanceAs <| Decidable (All P l ∧ P m ∧ All P r)
def Any (P : α → Prop) : Ordnode α → Prop
  | nil => False
  | node _ l x r => Any P l ∨ P x ∨ Any P r
instance Any.decidable {P : α → Prop} : (t : Ordnode α ) → [DecidablePred P] → Decidable (Any P t)
  | nil => isFalse id
  | node _ l m r =>
    have : Decidable (Any P l) := Any.decidable l
    have : Decidable (Any P r) := Any.decidable r
    inferInstanceAs <| Decidable (Any P l ∨ P m ∨ Any P r)
def Emem (x : α) : Ordnode α → Prop :=
  Any (Eq x)
instance Emem.decidable (x : α) [DecidableEq α] : ∀ t, Decidable (Emem x t) := by
  dsimp [Emem]; infer_instance
def Amem [LE α] (x : α) : Ordnode α → Prop :=
  Any fun y => x ≤ y ∧ y ≤ x
instance Amem.decidable [LE α] [@DecidableRel α (· ≤ ·)] (x : α) :
    ∀ t, Decidable (Amem x t) := by
  dsimp [Amem]; infer_instance
def findMin' : Ordnode α → α → α
  | nil, x => x
  | node _ l x _, _ => findMin' l x
def findMin : Ordnode α → Option α
  | nil => none
  | node _ l x _ => some (findMin' l x)
def findMax' : α → Ordnode α → α
  | x, nil => x
  | _, node _ _ x r => findMax' x r
def findMax : Ordnode α → Option α
  | nil => none
  | node _ _ x r => some (findMax' x r)
def eraseMin : Ordnode α → Ordnode α
  | nil => nil
  | node _ nil _ r => r
  | node _ (node sz l' y r') x r => balanceR (eraseMin (node sz l' y r')) x r
def eraseMax : Ordnode α → Ordnode α
  | nil => nil
  | node _ l _ nil => l
  | node _ l x (node sz l' y r') => balanceL l x (eraseMax (node sz l' y r'))
def splitMin' : Ordnode α → α → Ordnode α → α × Ordnode α
  | nil, x, r => (x, r)
  | node _ ll lx lr, x, r =>
    let (xm, l') := splitMin' ll lx lr
    (xm, balanceR l' x r)
def splitMin : Ordnode α → Option (α × Ordnode α)
  | nil => none
  | node _ l x r => splitMin' l x r
def splitMax' : Ordnode α → α → Ordnode α → Ordnode α × α
  | l, x, nil => (l, x)
  | l, x, node _ rl rx rr =>
    let (r', xm) := splitMax' rl rx rr
    (balanceL l x r', xm)
def splitMax : Ordnode α → Option (Ordnode α × α)
  | nil => none
  | node _ x l r => splitMax' x l r
def glue : Ordnode α → Ordnode α → Ordnode α
  | nil, r => r
  | l@(node _ _ _ _), nil => l
  | l@(node sl ll lx lr), r@(node sr rl rx rr) =>
    if sl > sr then
      let (l', m) := splitMax' ll lx lr
      balanceR l' m r
    else
      let (m, r') := splitMin' rl rx rr
      balanceL l m r'
def merge (l : Ordnode α) : Ordnode α → Ordnode α :=
  (Ordnode.recOn (motive := fun _ => Ordnode α → Ordnode α) l fun r => r)
    fun ls ll lx lr _ IHlr r =>
      (Ordnode.recOn (motive := fun _ => Ordnode α) r (node ls ll lx lr))
        fun rs rl rx rr IHrl _ =>
          if delta * ls < rs then balanceL IHrl rx rr
          else
            if delta * rs < ls then balanceR ll lx (IHlr <| node rs rl rx rr)
            else glue (node ls ll lx lr) (node rs rl rx rr)
def insertMax : Ordnode α → α → Ordnode α
  | nil, x => ι x
  | node _ l y r, x => balanceR l y (insertMax r x)
def insertMin (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node _ l y r => balanceR (insertMin x l) y r
def link (l : Ordnode α) (x : α) : Ordnode α → Ordnode α :=
  match l with
  | nil => insertMin x
  | node ls ll lx lr => fun r ↦
    match r with
    | nil => insertMax l x
    | node rs rl rx rr =>
      if delta * ls < rs then balanceL (link ll x rl) rx rr
      else if delta * rs < ls then balanceR ll lx (link lr x rr)
      else node' l x r
def filter (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then
                      link (filter p l) x (filter p r) else
                      merge (filter p l) (filter p r)
def partition (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    let (l₁, l₂) := partition p l
    let (r₁, r₂) := partition p r
    if p x then (link l₁ x r₁, merge l₂ r₂) else (merge l₁ r₁, link l₂ x r₂)
def map {β} (f : α → β) : Ordnode α → Ordnode β
  | nil => nil
  | node s l x r => node s (map f l) (f x) (map f r)
def fold {β} (z : β) (f : β → α → β → β) : Ordnode α → β
  | nil => z
  | node _ l x r => f (fold z f l) x (fold z f r)
def foldl {β} (f : β → α → β) : β → Ordnode α → β
  | z, nil => z
  | z, node _ l x r => foldl f (f (foldl f z l) x) r
def foldr {β} (f : α → β → β) : Ordnode α → β → β
  | nil, z => z
  | node _ l x r, z => foldr f l (f x (foldr f r z))
def toList (t : Ordnode α) : List α :=
  foldr List.cons t []
def toRevList (t : Ordnode α) : List α :=
  foldl (flip List.cons) [] t
instance [ToString α] : ToString (Ordnode α) :=
  ⟨fun t => "{" ++ String.intercalate ", " (t.toList.map toString) ++ "}"⟩
instance [Std.ToFormat α] : Std.ToFormat (Ordnode α) where
  format := fun t => Std.Format.joinSep (t.toList.map Std.ToFormat.format) (Std.Format.text ", ")
def Equiv (t₁ t₂ : Ordnode α) : Prop :=
  t₁.size = t₂.size ∧ t₁.toList = t₂.toList
instance [DecidableEq α] : DecidableRel (@Equiv α) := fun x y =>
  inferInstanceAs (Decidable (x.size = y.size ∧ x.toList = y.toList))
def powerset (t : Ordnode α) : Ordnode (Ordnode α) :=
  insertMin nil <| foldr (fun x ts => glue (insertMin (ι x) (map (insertMin x) ts)) ts) t nil
protected def prod {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (α × β) :=
  fold nil (fun s₁ a s₂ => merge s₁ <| merge (map (Prod.mk a) t₂) s₂) t₁
protected def copair {β} (t₁ : Ordnode α) (t₂ : Ordnode β) : Ordnode (α ⊕ β) :=
  merge (map Sum.inl t₁) (map Sum.inr t₂)
def pmap {P : α → Prop} {β} (f : ∀ a, P a → β) : ∀ t : Ordnode α, All P t → Ordnode β
  | nil, _ => nil
  | node s l x r, ⟨hl, hx, hr⟩ => node s (pmap f l hl) (f x hx) (pmap f r hr)
def attach' {P : α → Prop} : ∀ t, All P t → Ordnode { a // P a } :=
  pmap Subtype.mk
def nth : Ordnode α → ℕ → Option α
  | nil, _ => none
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => nth l i
    | some 0 => some x
    | some (j + 1) => nth r j
def removeNth : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    match Nat.psub' i (size l) with
    | none => balanceR (removeNth l i) x r
    | some 0 => glue l r
    | some (j + 1) => balanceL l x (removeNth r j)
def takeAux : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | node _ l x r, i =>
    if i = 0 then nil
    else
      match Nat.psub' i (size l) with
      | none => takeAux l i
      | some 0 => l
      | some (j + 1) => link l x (takeAux r j)
def take (i : ℕ) (t : Ordnode α) : Ordnode α :=
  if size t ≤ i then t else takeAux t i
def dropAux : Ordnode α → ℕ → Ordnode α
  | nil, _ => nil
  | t@(node _ l x r), i =>
    if i = 0 then t
    else
      match Nat.psub' i (size l) with
      | none => link (dropAux l i) x r
      | some 0 => insertMin x r
      | some (j + 1) => dropAux r j
def drop (i : ℕ) (t : Ordnode α) : Ordnode α :=
  if size t ≤ i then nil else dropAux t i
def splitAtAux : Ordnode α → ℕ → Ordnode α × Ordnode α
  | nil, _ => (nil, nil)
  | t@(node _ l x r), i =>
    if i = 0 then (nil, t)
    else
      match Nat.psub' i (size l) with
      | none =>
        let (l₁, l₂) := splitAtAux l i
        (l₁, link l₂ x r)
      | some 0 => (glue l r, insertMin x r)
      | some (j + 1) =>
        let (r₁, r₂) := splitAtAux r j
        (link l x r₁, r₂)
def splitAt (i : ℕ) (t : Ordnode α) : Ordnode α × Ordnode α :=
  if size t ≤ i then (t, nil) else splitAtAux t i
def takeWhile (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then link l x (takeWhile p r) else takeWhile p l
def dropWhile (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α
  | nil => nil
  | node _ l x r => if p x then dropWhile p r else link (dropWhile p l) x r
def span (p : α → Prop) [DecidablePred p] : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l x r =>
    if p x then
      let (r₁, r₂) := span p r
      (link l x r₁, r₂)
    else
      let (l₁, l₂) := span p l
      (l₁, link l₂ x r)
def ofAscListAux₁ : ∀ l : List α, ℕ → Ordnode α × { l' : List α // l'.length ≤ l.length }
  | [] => fun _ => (nil, ⟨[], le_rfl⟩)
  | x :: xs => fun s =>
    if s = 1 then (ι x, ⟨xs, Nat.le_succ _⟩)
    else
      match ofAscListAux₁ xs (s <<< 1) with
      | (t, ⟨[], _⟩) => (t, ⟨[], Nat.zero_le _⟩)
      | (l, ⟨y :: ys, h⟩) =>
        have := Nat.le_succ_of_le h
        let (r, ⟨zs, h'⟩) := ofAscListAux₁ ys (s <<< 1)
        (link l y r, ⟨zs, le_trans h' (le_of_lt this)⟩)
        termination_by l => l.length
def ofAscListAux₂ : List α → Ordnode α → ℕ → Ordnode α
  | [] => fun t _ => t
  | x :: xs => fun l s =>
    match ofAscListAux₁ xs s with
    | (r, ⟨ys, h⟩) =>
      have := Nat.lt_succ_of_le h
      ofAscListAux₂ ys (link l x r) (s <<< 1)
      termination_by l => l.length
def ofAscList : List α → Ordnode α
  | [] => nil
  | x :: xs => ofAscListAux₂ xs (ι x) 1
section
variable [LE α] [@DecidableRel α (· ≤ ·)]
def mem (x : α) : Ordnode α → Bool
  | nil => false
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => mem x l
    | Ordering.eq => true
    | Ordering.gt => mem x r
def find (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => find x l
    | Ordering.eq => some y
    | Ordering.gt => find x r
instance : Membership α (Ordnode α) :=
  ⟨fun t x => t.mem x⟩
instance mem.decidable (x : α) (t : Ordnode α) : Decidable (x ∈ t) :=
  Bool.decEq _ _
def insertWith (f : α → α) (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insertWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => balanceR l y (insertWith f x r)
def adjustWith (f : α → α) (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => node sz (adjustWith f x l) y r
    | Ordering.eq => node sz l (f y) r
    | Ordering.gt => node sz l y (adjustWith f x r)
def updateWith (f : α → Option α) (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (updateWith f x l) y r
    | Ordering.eq =>
      match f y with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balanceL l y (updateWith f x r)
def alter (f : Option α → Option α) (x : α) : Ordnode α → Ordnode α
  | nil => Option.recOn (f none) nil Ordnode.singleton
  | _t@(node sz l y r) =>
    match cmpLE x y with
    | Ordering.lt => balance (alter f x l) y r
    | Ordering.eq =>
      match f (some y) with
      | none => glue l r
      | some a => node sz l a r
    | Ordering.gt => balance l y (alter f x r)
protected def insert (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | node sz l y r =>
    match cmpLE x y with
    | Ordering.lt => balanceL (Ordnode.insert x l) y r
    | Ordering.eq => node sz l x r
    | Ordering.gt => balanceR l y (Ordnode.insert x r)
instance : Insert α (Ordnode α) :=
  ⟨Ordnode.insert⟩
def insert' (x : α) : Ordnode α → Ordnode α
  | nil => ι x
  | t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceL (insert' x l) y r
    | Ordering.eq => t
    | Ordering.gt => balanceR l y (insert' x r)
def split (x : α) : Ordnode α → Ordnode α × Ordnode α
  | nil => (nil, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, gt) := split x l
      (lt, link gt y r)
    | Ordering.eq => (l, r)
    | Ordering.gt =>
      let (lt, gt) := split x r
      (link l y lt, gt)
def split3 (x : α) : Ordnode α → Ordnode α × Option α × Ordnode α
  | nil => (nil, none, nil)
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt =>
      let (lt, f, gt) := split3 x l
      (lt, f, link gt y r)
    | Ordering.eq => (l, some y, r)
    | Ordering.gt =>
      let (lt, f, gt) := split3 x r
      (link l y lt, f, gt)
def erase (x : α) : Ordnode α → Ordnode α
  | nil => nil
  | _t@(node _ l y r) =>
    match cmpLE x y with
    | Ordering.lt => balanceR (erase x l) y r
    | Ordering.eq => glue l r
    | Ordering.gt => balanceL l y (erase x r)
def findLtAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best => if x ≤ y then findLtAux x l best else findLtAux x r y
def findLt (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r => if x ≤ y then findLt x l else some (findLtAux x r y)
def findGtAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best => if y ≤ x then findGtAux x r best else findGtAux x l y
def findGt (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r => if y ≤ x then findGt x r else some (findGtAux x l y)
def findLeAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findLeAux x l best
    | Ordering.eq => y
    | Ordering.gt => findLeAux x r y
def findLe (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => findLe x l
    | Ordering.eq => some y
    | Ordering.gt => some (findLeAux x r y)
def findGeAux (x : α) : Ordnode α → α → α
  | nil, best => best
  | node _ l y r, best =>
    match cmpLE x y with
    | Ordering.lt => findGeAux x l y
    | Ordering.eq => y
    | Ordering.gt => findGeAux x r best
def findGe (x : α) : Ordnode α → Option α
  | nil => none
  | node _ l y r =>
    match cmpLE x y with
    | Ordering.lt => some (findGeAux x l y)
    | Ordering.eq => some y
    | Ordering.gt => findGe x r
def findIndexAux (x : α) : Ordnode α → ℕ → Option ℕ
  | nil, _ => none
  | node _ l y r, i =>
    match cmpLE x y with
    | Ordering.lt => findIndexAux x l i
    | Ordering.eq => some (i + size l)
    | Ordering.gt => findIndexAux x r (i + size l + 1)
def findIndex (x : α) (t : Ordnode α) : Option ℕ :=
  findIndexAux x t 0
def isSubsetAux : Ordnode α → Ordnode α → Bool
  | nil, _ => true
  | _, nil => false
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isSome && isSubsetAux l lt && isSubsetAux r gt
def isSubset (t₁ t₂ : Ordnode α) : Bool :=
  decide (size t₁ ≤ size t₂) && isSubsetAux t₁ t₂
def disjoint : Ordnode α → Ordnode α → Bool
  | nil, _ => true
  | _, nil => true
  | node _ l x r, t =>
    let (lt, found, gt) := split3 x t
    found.isNone && disjoint l lt && disjoint r gt
def union : Ordnode α → Ordnode α → Ordnode α
  | t₁, nil => t₁
  | nil, t₂ => t₂
  | t₁@(node s₁ l₁ x₁ r₁), t₂@(node s₂ _ x₂ _) =>
    if s₂ = 1 then insert' x₂ t₁
    else
      if s₁ = 1 then insert x₁ t₂
      else
        let (l₂', r₂') := split x₁ t₂
        link (union l₁ l₂') x₁ (union r₁ r₂')
def diff : Ordnode α → Ordnode α → Ordnode α
  | t₁, nil => t₁
  | t₁, t₂@(node _ l₂ x r₂) =>
    cond t₁.empty t₂ <|
      let (l₁, r₁) := split x t₁
      let l₁₂ := diff l₁ l₂
      let r₁₂ := diff r₁ r₂
      if size l₁₂ + size r₁₂ = size t₁ then t₁ else merge l₁₂ r₁₂
def inter : Ordnode α → Ordnode α → Ordnode α
  | nil, _ => nil
  | t₁@(node _ l₁ x r₁), t₂ =>
    cond t₂.empty t₁ <|
      let (l₂, y, r₂) := split3 x t₂
      let l₁₂ := inter l₁ l₂
      let r₁₂ := inter r₁ r₂
      cond y.isSome (link l₁₂ x r₁₂) (merge l₁₂ r₁₂)
def ofList (l : List α) : Ordnode α :=
  l.foldr insert nil
def ofList' : List α → Ordnode α
  | [] => nil
  | x :: xs => if List.Chain (fun a b => ¬b ≤ a) x xs then ofAscList (x :: xs) else ofList (x :: xs)
def image {α β} [LE β] [@DecidableRel β (· ≤ ·)] (f : α → β) (t : Ordnode α) : Ordnode β :=
  ofList (t.toList.map f)
end
end Ordnode