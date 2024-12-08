import Mathlib.Data.Fin.Fin2
import Mathlib.Util.Notation3
import Mathlib.Tactic.TypeStar
open Fin2 Nat
universe u
variable {α : Type*} {m n : ℕ}
def Vector3 (α : Type u) (n : ℕ) : Type u :=
  Fin2 n → α
instance [Inhabited α] : Inhabited (Vector3 α n) where
  default := fun _ => default
namespace Vector3
@[match_pattern]
def nil : Vector3 α 0 :=
  nofun
@[match_pattern]
def cons (a : α) (v : Vector3 α n) : Vector3 α (n + 1) := fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v
section
open Lean
scoped macro_rules | `([$l,*]) => `(expand_foldr% (h t => cons h t) nil [$(.ofElems l),*])
@[app_unexpander Vector3.nil] def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])
@[app_unexpander Vector3.cons] def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x [])      => `([$x])
  | `($(_) $x [$xs,*]) => `([$x, $xs,*])
  | _                  => throw ()
end
@[inherit_doc]
scoped notation a " :: " b => cons a b
@[simp]
theorem cons_fz (a : α) (v : Vector3 α n) : (a :: v) fz = a :=
  rfl
@[simp]
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a :: v) (fs i) = v i :=
  rfl
abbrev nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i
abbrev ofFn (f : Fin2 n → α) : Vector3 α n :=
  f
def head (v : Vector3 α (n + 1)) : α :=
  v fz
def tail (v : Vector3 α (n + 1)) : Vector3 α n := fun i => v (fs i)
theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i
theorem cons_head_tail (v : Vector3 α (n + 1)) : (head v :: tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i
@[elab_as_elim]  
def nilElim {C : Vector3 α 0 → Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v]; apply H
@[elab_as_elim]  
def consElim {C : Vector3 α (n + 1) → Sort u} (H : ∀ (a : α) (t : Vector3 α n), C (a :: t))
    (v : Vector3 α (n + 1)) : C v := by rw [← cons_head_tail v]; apply H
@[simp]
theorem consElim_cons {C H a t} : @consElim α n C H (a :: t) = H a t :=
  rfl
@[elab_as_elim]
protected def recOn {C : ∀ {n}, Vector3 α n → Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : ∀ {n} (a) (w : Vector3 α n), C w → C (a :: w)) : C v :=
  match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)
@[simp]
theorem recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl
@[simp]
theorem recOn_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (n + 1) (a :: v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  v.recOn w (fun a _ IH => a :: IH)
local infixl:65 " +-+ " => Vector3.append
@[simp]
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl
@[simp]
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a :: v) +-+ w = a :: v +-+ w :=
  rfl
@[simp]
theorem append_left :
    ∀ {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, _, _ => v.consElim fun a _t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun _a t => by simp [append_left, left]
@[simp]
theorem append_add :
    ∀ {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, _, _, _, _ => rfl
  | m + 1, v, n, w, i => v.consElim fun _a t => by simp [append_add, add]
def insert (a : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : Vector3 α (n + 1) := fun j =>
  (a :: v) (insertPerm i j)
@[simp]
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a :: v := by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl
@[simp]
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1)) :
    insert a (b :: v) (fs i) = b :: insert a v i :=
  funext fun j => by
    refine j.cases' ?_ fun j => ?_ <;> simp [insert, insertPerm]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp [insertPerm]
theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
    (e : (n + 1) + m = (n + m) + 1) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) := by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by omega
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a v i)
  rw [← (Eq.recOn e' rfl :
      fs (Eq.recOn e' (i.add k) : Fin2 ((n + k) + 1)) =
        Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (i.add k)))]
  simpa [IH] using Eq.recOn e' rfl
end Vector3
section Vector3
open Vector3
def VectorEx : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∃ x : α, VectorEx k fun v => f (x :: v)
def VectorAll : ∀ k, (Vector3 α k → Prop) → Prop
  | 0, f => f []
  | succ k, f => ∀ x : α, VectorAll k fun v => f (x :: v)
theorem exists_vector_zero (f : Vector3 α 0 → Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩
theorem exists_vector_succ (f : Vector3 α (succ n) → Prop) : Exists f ↔ ∃ x v, f (x :: v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨_, _, fxv⟩ => ⟨_, fxv⟩⟩
theorem vectorEx_iff_exists : ∀ {n} (f : Vector3 α n → Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ _, f =>
    Iff.trans (exists_congr fun _ => vectorEx_iff_exists _) (exists_vector_succ f).symm
theorem vectorAll_iff_forall : ∀ {n} (f : Vector3 α n → Prop), VectorAll n f ↔ ∀ v, f v
  | 0, _ => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ _, f =>
    (forall_congr' fun x => vectorAll_iff_forall fun v => f (x :: v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x :: v)⟩
def VectorAllP (p : α → Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH
@[simp]
theorem vectorAllP_nil (p : α → Prop) : VectorAllP p [] = True :=
  rfl
@[simp]
theorem vectorAllP_singleton (p : α → Prop) (x : α) : VectorAllP p (cons x []) = p x :=
  rfl
@[simp]
theorem vectorAllP_cons (p : α → Prop) (x : α) (v : Vector3 α n) :
    VectorAllP p (x :: v) ↔ p x ∧ VectorAllP p v :=
  Vector3.recOn v (iff_of_eq (and_true _)).symm fun _ _ _ => Iff.rfl
theorem vectorAllP_iff_forall (p : α → Prop) (v : Vector3 α n) :
    VectorAllP p v ↔ ∀ i, p (v i) := by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · simpa using h fz
    · simpa using h (fs i)
theorem VectorAllP.imp {p q : α → Prop} (h : ∀ x, p x → q x) {v : Vector3 α n}
    (al : VectorAllP p v) : VectorAllP q v :=
  (vectorAllP_iff_forall _ _).2 fun _ => h _ <| (vectorAllP_iff_forall _ _).1 al _
end Vector3