import Mathlib.Algebra.BigOperators.Group.List
import Mathlib.Data.Vector.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic
universe u
variable {α β γ σ φ : Type*} {m n : ℕ}
namespace Mathlib
namespace Vector
@[inherit_doc]
infixr:67 " ::ᵥ " => Vector.cons
attribute [simp] head_cons tail_cons
instance [Inhabited α] : Inhabited (Vector α n) :=
  ⟨ofFn default⟩
theorem toList_injective : Function.Injective (@toList α n) :=
  Subtype.val_injective
@[ext]
theorem ext : ∀ {v w : Vector α n} (_ : ∀ m : Fin n, Vector.get v m = Vector.get w m), v = w
  | ⟨v, hv⟩, ⟨w, hw⟩, h =>
    Subtype.eq (List.ext_get (by rw [hv, hw]) fun m hm _ => h ⟨m, hv ▸ hm⟩)
instance zero_subsingleton : Subsingleton (Vector α 0) :=
  ⟨fun _ _ => Vector.ext fun m => Fin.elim0 m⟩
@[simp]
theorem cons_val (a : α) : ∀ v : Vector α n, (a ::ᵥ v).val = a :: v.val
  | ⟨_, _⟩ => rfl
theorem eq_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v = a ::ᵥ v' ↔ v.head = a ∧ v.tail = v' :=
  ⟨fun h => h.symm ▸ ⟨head_cons a v', tail_cons a v'⟩, fun h =>
    _root_.trans (cons_head_tail v).symm (by rw [h.1, h.2])⟩
theorem ne_cons_iff (a : α) (v : Vector α n.succ) (v' : Vector α n) :
    v ≠ a ::ᵥ v' ↔ v.head ≠ a ∨ v.tail ≠ v' := by rw [Ne, eq_cons_iff a v v', not_and_or]
theorem exists_eq_cons (v : Vector α n.succ) : ∃ (a : α) (as : Vector α n), v = a ::ᵥ as :=
  ⟨v.head, v.tail, (eq_cons_iff v.head v v.tail).2 ⟨rfl, rfl⟩⟩
@[simp]
theorem toList_ofFn : ∀ {n} (f : Fin n → α), toList (ofFn f) = List.ofFn f
  | 0, f => by rw [ofFn, List.ofFn_zero, toList, nil]
  | n + 1, f => by rw [ofFn, List.ofFn_succ, toList_cons, toList_ofFn]
@[simp]
theorem mk_toList : ∀ (v : Vector α n) (h), (⟨toList v, h⟩ : Vector α n) = v
  | ⟨_, _⟩, _ => rfl
@[simp] theorem length_val (v : Vector α n) : v.val.length = n := v.2
@[simp]
theorem pmap_cons {p : α → Prop} (f : (a : α) → p a → β) (a : α) (v : Vector α n)
    (hp : ∀ x ∈ (cons a v).toList, p x) :
    (cons a v).pmap f hp = cons (f a (by
      simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
      exact hp.1))
      (v.pmap f (by
        simp only [Nat.succ_eq_add_one, toList_cons, List.mem_cons, forall_eq_or_imp] at hp
        exact hp.2)) := rfl
theorem pmap_cons' {p : α → Prop} (f : (a : α) → p a → β) (a : α) (v : Vector α n)
    (ha : p a) (hp : ∀ x ∈ v.toList, p x) :
    cons (f a ha) (v.pmap f hp) = (cons a v).pmap f (by simpa [ha]) := rfl
@[simp]
theorem toList_map {β : Type*} (v : Vector α n) (f : α → β) :
    (v.map f).toList = v.toList.map f := by cases v; rfl
@[simp]
theorem head_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) : (v.map f).head = f v.head := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, head_cons, head_cons]
@[simp]
theorem tail_map {β : Type*} (v : Vector α (n + 1)) (f : α → β) :
    (v.map f).tail = v.tail.map f := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  rw [h, map_cons, tail_cons, tail_cons]
@[simp]
theorem getElem_map {β : Type*} (v : Vector α n) (f : α → β) {i : ℕ} (hi : i < n) :
    (v.map f)[i] = f v[i] := by
  simp only [getElem_def, toList_map, List.getElem_map]
@[simp]
theorem toList_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α n)
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).toList = v.toList.pmap f hp := by cases v; rfl
@[simp]
theorem head_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α (n + 1))
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).head = f v.head (hp _ <| by
      rw [← cons_head_tail v, toList_cons, head_cons, List.mem_cons]; exact .inl rfl) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, head_cons]
@[simp]
theorem tail_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α (n + 1))
    (hp : ∀ x ∈ v.toList, p x) :
    (v.pmap f hp).tail = v.tail.pmap f (fun x hx ↦ hp _ <| by
      rw [← cons_head_tail v, toList_cons, List.mem_cons]; exact .inr hx) := by
  obtain ⟨a, v', h⟩ := Vector.exists_eq_cons v
  simp_rw [h, pmap_cons, tail_cons]
@[simp]
theorem getElem_pmap {p : α → Prop} (f : (a : α) → p a → β) (v : Vector α n)
    (hp : ∀ x ∈ v.toList, p x) {i : ℕ} (hi : i < n) :
    (v.pmap f hp)[i] = f v[i] (hp _ (by simp [getElem_def, List.getElem_mem])) := by
  simp only [getElem_def, toList_pmap, List.getElem_pmap]
theorem get_eq_get (v : Vector α n) (i : Fin n) :
    v.get i = v.toList.get (Fin.cast v.toList_length.symm i) :=
  rfl
@[simp]
theorem get_replicate (a : α) (i : Fin n) : (Vector.replicate n a).get i = a := by
  apply List.getElem_replicate
@[simp]
theorem get_map {β : Type*} (v : Vector α n) (f : α → β) (i : Fin n) :
    (v.map f).get i = f (v.get i) := by
  cases v; simp [Vector.map, get_eq_get]
@[simp]
theorem map₂_nil (f : α → β → γ) : Vector.map₂ f nil nil = nil :=
  rfl
@[simp]
theorem map₂_cons (hd₁ : α) (tl₁ : Vector α n) (hd₂ : β) (tl₂ : Vector β n) (f : α → β → γ) :
    Vector.map₂ f (hd₁ ::ᵥ tl₁) (hd₂ ::ᵥ tl₂) = f hd₁ hd₂ ::ᵥ (Vector.map₂ f tl₁ tl₂) :=
  rfl
@[simp]
theorem get_ofFn {n} (f : Fin n → α) (i) : get (ofFn f) i = f i := by
  conv_rhs => erw [← List.get_ofFn f ⟨i, by simp⟩]
  simp only [get_eq_get]
  congr <;> simp [Fin.heq_ext_iff]
@[simp]
theorem ofFn_get (v : Vector α n) : ofFn (get v) = v := by
  rcases v with ⟨l, rfl⟩
  apply toList_injective
  dsimp
  simpa only [toList_ofFn] using List.ofFn_get _
def _root_.Equiv.vectorEquivFin (α : Type*) (n : ℕ) : Vector α n ≃ (Fin n → α) :=
  ⟨Vector.get, Vector.ofFn, Vector.ofFn_get, fun f => funext <| Vector.get_ofFn f⟩
theorem get_tail (x : Vector α n) (i) : x.tail.get i = x.get ⟨i.1 + 1, by omega⟩ := by
  cases' i with i ih; dsimp
  rcases x with ⟨_ | _, h⟩ <;> try rfl
  rw [List.length] at h
  rw [← h] at ih
  contradiction
@[simp]
theorem get_tail_succ : ∀ (v : Vector α n.succ) (i : Fin n), get (tail v) i = get v i.succ
  | ⟨a :: l, e⟩, ⟨i, h⟩ => by simp [get_eq_get]; rfl
@[simp]
theorem tail_val : ∀ v : Vector α n.succ, v.tail.val = v.val.tail
  | ⟨_ :: _, _⟩ => rfl
@[simp]
theorem tail_nil : (@nil α).tail = nil :=
  rfl
@[simp]
theorem singleton_tail : ∀ (v : Vector α 1), v.tail = Vector.nil
  | ⟨[_], _⟩ => rfl
@[simp]
theorem tail_ofFn {n : ℕ} (f : Fin n.succ → α) : tail (ofFn f) = ofFn fun i => f i.succ :=
  (ofFn_get _).symm.trans <| by
    congr
    funext i
    rw [get_tail, get_ofFn]
    rfl
@[simp]
theorem toList_empty (v : Vector α 0) : v.toList = [] :=
  List.length_eq_zero.mp v.2
@[simp]
theorem toList_singleton (v : Vector α 1) : v.toList = [v.head] := by
  rw [← v.cons_head_tail]
  simp only [toList_cons, toList_nil, head_cons, eq_self_iff_true, and_self_iff, singleton_tail]
@[simp]
theorem empty_toList_eq_ff (v : Vector α (n + 1)) : v.toList.isEmpty = false :=
  match v with
  | ⟨_ :: _, _⟩ => rfl
theorem not_empty_toList (v : Vector α (n + 1)) : ¬v.toList.isEmpty := by
  simp only [empty_toList_eq_ff, Bool.coe_sort_false, not_false_iff]
@[simp]
theorem map_id {n : ℕ} (v : Vector α n) : Vector.map id v = v :=
  Vector.eq _ _ (by simp only [List.map_id, Vector.toList_map])
theorem nodup_iff_injective_get {v : Vector α n} : v.toList.Nodup ↔ Function.Injective v.get := by
  cases' v with l hl
  subst hl
  exact List.nodup_iff_injective_get
theorem head?_toList : ∀ v : Vector α n.succ, (toList v).head? = some (head v)
  | ⟨_ :: _, _⟩ => rfl
def reverse (v : Vector α n) : Vector α n :=
  ⟨v.toList.reverse, by simp⟩
theorem toList_reverse {v : Vector α n} : v.reverse.toList = v.toList.reverse :=
  rfl
@[simp]
theorem reverse_reverse {v : Vector α n} : v.reverse.reverse = v := by
  cases v
  simp [Vector.reverse]
@[simp]
theorem get_zero : ∀ v : Vector α n.succ, get v 0 = head v
  | ⟨_ :: _, _⟩ => rfl
@[simp]
theorem head_ofFn {n : ℕ} (f : Fin n.succ → α) : head (ofFn f) = f 0 := by
  rw [← get_zero, get_ofFn]
theorem get_cons_zero (a : α) (v : Vector α n) : get (a ::ᵥ v) 0 = a := by simp [get_zero]
@[simp]
theorem get_cons_nil : ∀ {ix : Fin 1} (x : α), get (x ::ᵥ nil) ix = x
  | ⟨0, _⟩, _ => rfl
@[simp]
theorem get_cons_succ (a : α) (v : Vector α n) (i : Fin n) : get (a ::ᵥ v) i.succ = get v i := by
  rw [← get_tail_succ, tail_cons]
def last (v : Vector α (n + 1)) : α :=
  v.get (Fin.last n)
theorem last_def {v : Vector α (n + 1)} : v.last = v.get (Fin.last n) :=
  rfl
theorem reverse_get_zero {v : Vector α (n + 1)} : v.reverse.head = v.last := by
  rw [← get_zero, last_def, get_eq_get, get_eq_get]
  simp_rw [toList_reverse]
  rw [List.get_eq_getElem, List.get_eq_getElem, ← Option.some_inj, Fin.cast, Fin.cast,
    ← List.getElem?_eq_getElem, ← List.getElem?_eq_getElem, List.getElem?_reverse]
  · congr
    simp
  · simp
section Scan
variable {β : Type*}
variable (f : β → α → β) (b : β)
variable (v : Vector α n)
def scanl : Vector β (n + 1) :=
  ⟨List.scanl f b v.toList, by rw [List.length_scanl, toList_length]⟩
@[simp]
theorem scanl_nil : scanl f b nil = b ::ᵥ nil :=
  rfl
@[simp]
theorem scanl_cons (x : α) : scanl f b (x ::ᵥ v) = b ::ᵥ scanl f (f b x) v := by
  simp only [scanl, toList_cons, List.scanl]; dsimp
  simp only [cons]; rfl
@[simp]
theorem scanl_val : ∀ {v : Vector α n}, (scanl f b v).val = List.scanl f b v.val
  | _ => rfl
@[simp]
theorem toList_scanl : (scanl f b v).toList = List.scanl f b v.toList :=
  rfl
@[simp]
theorem scanl_singleton (v : Vector α 1) : scanl f b v = b ::ᵥ f b v.head ::ᵥ nil := by
  rw [← cons_head_tail v]
  simp only [scanl_cons, scanl_nil, head_cons, singleton_tail]
@[simp]
theorem scanl_head : (scanl f b v).head = b := by
  cases n
  · have : v = nil := by simp only [eq_iff_true_of_subsingleton]
    simp only [this, scanl_nil, head_cons]
  · rw [← cons_head_tail v]
    simp only [← get_zero, get_eq_get, toList_scanl, toList_cons, List.scanl, Fin.val_zero,
      List.get]
@[simp]
theorem scanl_get (i : Fin n) :
    (scanl f b v).get i.succ = f ((scanl f b v).get (Fin.castSucc i)) (v.get i) := by
  cases' n with n
  · exact i.elim0
  induction' n with n hn generalizing b
  · have i0 : i = 0 := Fin.eq_zero _
    simp [scanl_singleton, i0, get_zero]; simp [get_eq_get, List.get]
  · rw [← cons_head_tail v, scanl_cons, get_cons_succ]
    refine Fin.cases ?_ ?_ i
    · simp only [get_zero, scanl_head, Fin.castSucc_zero, head_cons]
    · intro i'
      simp only [hn, Fin.castSucc_fin_succ, get_cons_succ]
end Scan
def mOfFn {m} [Monad m] {α : Type u} : ∀ {n}, (Fin n → m α) → m (Vector α n)
  | 0, _ => pure nil
  | _ + 1, f => do
    let a ← f 0
    let v ← mOfFn fun i => f i.succ
    pure (a ::ᵥ v)
theorem mOfFn_pure {m} [Monad m] [LawfulMonad m] {α} :
    ∀ {n} (f : Fin n → α), (@mOfFn m _ _ _ fun i => pure (f i)) = pure (ofFn f)
  | 0, _ => rfl
  | n + 1, f => by
    rw [mOfFn, @mOfFn_pure m _ _ _ n _, ofFn]
    simp
def mmap {m} [Monad m] {α} {β : Type u} (f : α → m β) : ∀ {n}, Vector α n → m (Vector β n)
  | 0, _ => pure nil
  | _ + 1, xs => do
    let h' ← f xs.head
    let t' ← mmap f xs.tail
    pure (h' ::ᵥ t')
@[simp]
theorem mmap_nil {m} [Monad m] {α β} (f : α → m β) : mmap f nil = pure nil :=
  rfl
@[simp]
theorem mmap_cons {m} [Monad m] {α β} (f : α → m β) (a) :
    ∀ {n} (v : Vector α n),
      mmap f (a ::ᵥ v) = do
        let h' ← f a
        let t' ← mmap f v
        pure (h' ::ᵥ t')
  | _, ⟨_, rfl⟩ => rfl
@[elab_as_elim, induction_eliminator]
def inductionOn {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (v : Vector α n)
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) : C v := by
  induction' n with n ih
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    exact cons (ih ⟨v, (add_left_inj 1).mp v_property⟩)
@[simp]
theorem inductionOn_nil {C : ∀ {n : ℕ}, Vector α n → Sort*}
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) :
    Vector.nil.inductionOn nil cons = nil :=
  rfl
@[simp]
theorem inductionOn_cons {C : ∀ {n : ℕ}, Vector α n → Sort*} {n : ℕ} (x : α) (v : Vector α n)
    (nil : C nil) (cons : ∀ {n : ℕ} {x : α} {w : Vector α n}, C w → C (x ::ᵥ w)) :
    (x ::ᵥ v).inductionOn nil cons = cons (v.inductionOn nil cons : C v) :=
  rfl
variable {β γ : Type*}
@[elab_as_elim]
def inductionOn₂ {C : ∀ {n}, Vector α n → Vector β n → Sort*}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil) (cons : ∀ {n a b} {x : Vector α n} {y}, C x y → C (a ::ᵥ x) (b ::ᵥ y)) :
    C v w := by
  induction' n with n ih
  · rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  · rcases v with ⟨_ | ⟨a, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨b, w⟩, w_property⟩
    cases w_property
    apply @cons n _ _ ⟨v, (add_left_inj 1).mp v_property⟩ ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
@[elab_as_elim]
def inductionOn₃ {C : ∀ {n}, Vector α n → Vector β n → Vector γ n → Sort*}
    (u : Vector α n) (v : Vector β n) (w : Vector γ n) (nil : C nil nil nil)
    (cons : ∀ {n a b c} {x : Vector α n} {y z}, C x y z → C (a ::ᵥ x) (b ::ᵥ y) (c ::ᵥ z)) :
    C u v w := by
  induction' n with n ih
  · rcases u with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases v with ⟨_ | ⟨-, -⟩, - | -⟩
    rcases w with ⟨_ | ⟨-, -⟩, - | -⟩
    exact nil
  · rcases u with ⟨_ | ⟨a, u⟩, u_property⟩
    cases u_property
    rcases v with ⟨_ | ⟨b, v⟩, v_property⟩
    cases v_property
    rcases w with ⟨_ | ⟨c, w⟩, w_property⟩
    cases w_property
    apply
      @cons n _ _ _ ⟨u, (add_left_inj 1).mp u_property⟩ ⟨v, (add_left_inj 1).mp v_property⟩
        ⟨w, (add_left_inj 1).mp w_property⟩
    apply ih
def casesOn {motive : ∀ {n}, Vector α n → Sort*} (v : Vector α m)
    (nil : motive nil)
    (cons : ∀ {n}, (hd : α) → (tl : Vector α n) → motive (Vector.cons hd tl)) :
    motive v :=
  inductionOn (C := motive) v nil @fun _ hd tl _ => cons hd tl
def casesOn₂  {motive : ∀{n}, Vector α n → Vector β n → Sort*} (v₁ : Vector α m) (v₂ : Vector β m)
    (nil : motive nil nil)
    (cons : ∀{n}, (x : α) → (y : β) → (xs : Vector α n) → (ys : Vector β n)
      → motive (x ::ᵥ xs) (y ::ᵥ ys)) :
    motive v₁ v₂ :=
  inductionOn₂ (C := motive) v₁ v₂ nil @fun _ x y xs ys _ => cons x y xs ys
def casesOn₃  {motive : ∀{n}, Vector α n → Vector β n → Vector γ n → Sort*} (v₁ : Vector α m)
    (v₂ : Vector β m) (v₃ : Vector γ m) (nil : motive nil nil nil)
    (cons : ∀{n}, (x : α) → (y : β) → (z : γ) → (xs : Vector α n) → (ys : Vector β n)
      → (zs : Vector γ n) → motive (x ::ᵥ xs) (y ::ᵥ ys) (z ::ᵥ zs)) :
    motive v₁ v₂ v₃ :=
  inductionOn₃ (C := motive) v₁ v₂ v₃ nil @fun _ x y z xs ys zs _ => cons x y z xs ys zs
def toArray : Vector α n → Array α
  | ⟨xs, _⟩ => cast (by rfl) xs.toArray
section InsertIdx
variable {a : α}
def insertIdx (a : α) (i : Fin (n + 1)) (v : Vector α n) : Vector α (n + 1) :=
  ⟨v.1.insertIdx i a, by
    rw [List.length_insertIdx, v.2]
    split <;> omega⟩
@[deprecated (since := "2024-10-21")] alias insertNth := insertIdx
theorem insertIdx_val {i : Fin (n + 1)} {v : Vector α n} :
    (v.insertIdx a i).val = v.val.insertIdx i.1 a :=
  rfl
@[deprecated (since := "2024-10-21")] alias insertNth_val := insertIdx_val
@[simp]
theorem eraseIdx_val {i : Fin n} : ∀ {v : Vector α n}, (eraseIdx i v).val = v.val.eraseIdx i
  | _ => rfl
@[deprecated (since := "2024-10-21")] alias eraseNth_val := eraseIdx_val
@[deprecated (since := "2024-05-04")] alias removeNth_val := eraseIdx_val
theorem eraseIdx_insertIdx {v : Vector α n} {i : Fin (n + 1)} :
    eraseIdx i (insertIdx a i v) = v :=
  Subtype.eq <| List.eraseIdx_insertIdx i.1 v.1
@[deprecated (since := "2024-05-04")] alias eraseIdx_insertNth := eraseIdx_insertIdx
@[deprecated (since := "2024-05-04")] alias removeNth_insertNth := eraseIdx_insertIdx
theorem eraseIdx_insertIdx' {v : Vector α (n + 1)} :
    ∀ {i : Fin (n + 1)} {j : Fin (n + 2)},
      eraseIdx (j.succAbove i) (insertIdx a j v) = insertIdx a (i.predAbove j) (eraseIdx i v)
  | ⟨i, hi⟩, ⟨j, hj⟩ => by
    dsimp [insertIdx, eraseIdx, Fin.succAbove, Fin.predAbove]
    rw [Subtype.mk_eq_mk]
    simp only [Fin.lt_iff_val_lt_val]
    split_ifs with hij
    · rcases Nat.exists_eq_succ_of_ne_zero
        (Nat.pos_iff_ne_zero.1 (lt_of_le_of_lt (Nat.zero_le _) hij)) with ⟨j, rfl⟩
      rw [← List.insertIdx_eraseIdx_of_ge]
      · simp; rfl
      · simpa
      · simpa [Nat.lt_succ_iff] using hij
    · dsimp
      rw [← List.insertIdx_eraseIdx_of_le i j _ _ _]
      · rfl
      · simpa
      · simpa [not_lt] using hij
@[deprecated (since := "2024-05-04")] alias eraseIdx_insertNth' := eraseIdx_insertIdx'
@[deprecated (since := "2024-05-04")] alias removeNth_insertNth' := eraseIdx_insertIdx'
theorem insertIdx_comm (a b : α) (i j : Fin (n + 1)) (h : i ≤ j) :
    ∀ v : Vector α n,
      (v.insertIdx a i).insertIdx b j.succ = (v.insertIdx b j).insertIdx a (Fin.castSucc i)
  | ⟨l, hl⟩ => by
    refine Subtype.eq ?_
    simp only [insertIdx_val, Fin.val_succ, Fin.castSucc, Fin.coe_castAdd]
    apply List.insertIdx_comm
    · assumption
    · rw [hl]
      exact Nat.le_of_succ_le_succ j.2
@[deprecated (since := "2024-10-21")] alias insertNth_comm := insertIdx_comm
end InsertIdx
section Set
def set (v : Vector α n) (i : Fin n) (a : α) : Vector α n :=
  ⟨v.1.set i.1 a, by simp⟩
@[simp]
theorem toList_set (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList = v.toList.set i a :=
  rfl
@[simp]
theorem get_set_same (v : Vector α n) (i : Fin n) (a : α) : (v.set i a).get i = a := by
  cases v; cases i; simp [Vector.set, get_eq_get]
theorem get_set_of_ne {v : Vector α n} {i j : Fin n} (h : i ≠ j) (a : α) :
    (v.set i a).get j = v.get j := by
  cases v; cases i; cases j
  simp only [get_eq_get, toList_set, toList_mk, Fin.cast_mk, List.get_eq_getElem]
  rw [List.getElem_set_of_ne]
  · simpa using h
theorem get_set_eq_if {v : Vector α n} {i j : Fin n} (a : α) :
    (v.set i a).get j = if i = j then a else v.get j := by
  split_ifs <;> (try simp [*]); rwa [get_set_of_ne]
@[to_additive]
theorem prod_set [Monoid α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = (v.take i).toList.prod * a * (v.drop (i + 1)).toList.prod := by
  refine (List.prod_set v.toList i a).trans ?_
  simp_all
@[to_additive]
theorem prod_set' [CommGroup α] (v : Vector α n) (i : Fin n) (a : α) :
    (v.set i a).toList.prod = v.toList.prod * (v.get i)⁻¹ * a := by
  refine (List.prod_set' v.toList i a).trans ?_
  simp [get_eq_get, mul_assoc]
end Set
end Vector
namespace Vector
section Traverse
variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]
open Applicative Functor
open List (cons)
open Nat
private def traverseAux {α β : Type u} (f : α → F β) : ∀ x : List α, F (Vector β x.length)
  | [] => pure Vector.nil
  | x :: xs => Vector.cons <$> f x <*> traverseAux f xs
protected def traverse {α β : Type u} (f : α → F β) : Vector α n → F (Vector β n)
  | ⟨v, Hv⟩ => cast (by rw [Hv]) <| traverseAux f v
section
variable {α β : Type u}
@[simp]
protected theorem traverse_def (f : α → F β) (x : α) :
    ∀ xs : Vector α n, (x ::ᵥ xs).traverse f = cons <$> f x <*> xs.traverse f := by
  rintro ⟨xs, rfl⟩; rfl
protected theorem id_traverse : ∀ x : Vector α n, x.traverse (pure : _ → Id _) = x := by
  rintro ⟨x, rfl⟩; dsimp [Vector.traverse, cast]
  induction' x with x xs IH; · rfl
  simp! [IH]; rfl
end
open Function
variable [LawfulApplicative G]
variable {α β γ : Type u}
@[nolint unusedArguments]
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : Vector α n) :
    Vector.traverse (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Vector.traverse f <$> Vector.traverse g x) := by
  induction' x with n x xs ih
  · simp! [cast, *, functor_norm]
    rfl
  · rw [Vector.traverse_def, ih]
    simp [functor_norm, Function.comp_def]
protected theorem traverse_eq_map_id {α β} (f : α → β) :
    ∀ x : Vector α n, x.traverse ((pure : _ → Id _) ∘ f) = (pure : _ → Id _) (map f x) := by
  rintro ⟨x, rfl⟩; simp!; induction x <;> simp! [*, functor_norm] <;> rfl
variable [LawfulApplicative F] (η : ApplicativeTransformation F G)
protected theorem naturality {α β : Type u} (f : α → F β) (x : Vector α n) :
    η (x.traverse f) = x.traverse (@η _ ∘ f) := by
  induction' x with n x xs ih
  · simp! [functor_norm, cast, η.preserves_pure]
  · rw [Vector.traverse_def, Vector.traverse_def, ← ih, η.preserves_seq, η.preserves_map]
    rfl
end Traverse
instance : Traversable.{u} (flip Vector n) where
  traverse := @Vector.traverse n
  map {α β} := @Vector.map.{u, u} α β n
instance : LawfulTraversable.{u} (flip Vector n) where
  id_traverse := @Vector.id_traverse n
  comp_traverse := Vector.comp_traverse
  traverse_eq_map_id := @Vector.traverse_eq_map_id n
  naturality := Vector.naturality
  id_map := by intro _ x; cases x; simp! [(· <$> ·)]
  comp_map := by intro _ _ _ _ _ x; cases x; simp! [(· <$> ·)]
  map_const := rfl
section Simp
variable {x : α} {y : β} {s : σ} (xs : Vector α n)
@[simp]
theorem replicate_succ (val : α) :
    replicate (n+1) val = val ::ᵥ (replicate n val) :=
  rfl
section Append
variable (ys : Vector α m)
@[simp] lemma get_append_cons_zero : get (append (x ::ᵥ xs) ys) ⟨0, by omega⟩ = x := rfl
@[simp]
theorem get_append_cons_succ {i : Fin (n + m)} {h} :
    get (append (x ::ᵥ xs) ys) ⟨i+1, h⟩ = get (append xs ys) i :=
  rfl
@[simp]
theorem append_nil : append xs nil = xs := by
  cases xs; simp [append]
end Append
variable (ys : Vector β n)
@[simp]
theorem get_map₂ (v₁ : Vector α n) (v₂ : Vector β n) (f : α → β → γ) (i : Fin n) :
    get (map₂ f v₁ v₂) i = f (get v₁ i) (get v₂ i) := by
  clear * - v₁ v₂
  induction v₁, v₂ using inductionOn₂ with
  | nil =>
    exact Fin.elim0 i
  | cons ih =>
    rw [map₂_cons]
    cases i using Fin.cases
    · simp only [get_zero, head_cons]
    · simp only [get_cons_succ, ih]
@[simp]
theorem mapAccumr_cons {f : α → σ → σ × β} :
    mapAccumr f (x ::ᵥ xs) s
    = let r := mapAccumr f xs s
      let q := f x r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl
@[simp]
theorem mapAccumr₂_cons {f : α → β → σ → σ × φ} :
    mapAccumr₂ f (x ::ᵥ xs) (y ::ᵥ ys) s
    = let r := mapAccumr₂ f xs ys s
      let q := f x y r.1
      (q.1, q.2 ::ᵥ r.2) :=
  rfl
end Simp
end Vector
end Mathlib