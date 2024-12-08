import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rel
variable {α : Type*} (r : Rel α α)
variable {β : Type*} (s : Rel β β)
structure RelSeries where
  length : ℕ
  toFun : Fin (length + 1) → α
  step : ∀ (i : Fin length), r (toFun (Fin.castSucc i)) (toFun i.succ)
namespace RelSeries
instance : CoeFun (RelSeries r) (fun x ↦ Fin (x.length + 1) → α) :=
{ coe := RelSeries.toFun }
@[simps!] def singleton (a : α) : RelSeries r where
  length := 0
  toFun _ := a
  step := Fin.elim0
instance [IsEmpty α] : IsEmpty (RelSeries r) where
  false x := IsEmpty.false (x 0)
instance [Inhabited α] : Inhabited (RelSeries r) where
  default := singleton r default
instance [Nonempty α] : Nonempty (RelSeries r) :=
  Nonempty.map (singleton r) inferInstance
variable {r}
@[ext (iff := false)]
lemma ext {x y : RelSeries r} (length_eq : x.length = y.length)
    (toFun_eq : x.toFun = y.toFun ∘ Fin.cast (by rw [length_eq])) : x = y := by
  rcases x with ⟨nx, fx⟩
  dsimp only at length_eq toFun_eq
  subst length_eq toFun_eq
  rfl
lemma rel_of_lt [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i < j) :
    r (x i) (x j) :=
  (Fin.liftFun_iff_succ r).mpr x.step h
lemma rel_or_eq_of_le [IsTrans α r] (x : RelSeries r) {i j : Fin (x.length + 1)} (h : i ≤ j) :
    r (x i) (x j) ∨ x i = x j :=
  (Fin.lt_or_eq_of_le h).imp (x.rel_of_lt ·) (by rw [·])
@[simps!]
def ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) : RelSeries s where
  length := x.length
  toFun := x
  step _ := h _ _ <| x.step _
lemma coe_ofLE (x : RelSeries r) {s : Rel α α} (h : r ≤ s) :
    (x.ofLE h : _ → _) = x := rfl
def toList (x : RelSeries r) : List α := List.ofFn x
@[simp]
lemma length_toList (x : RelSeries r) : x.toList.length = x.length + 1 :=
  List.length_ofFn _
lemma toList_chain' (x : RelSeries r) : x.toList.Chain' r := by
  rw [List.chain'_iff_get]
  intros i h
  convert x.step ⟨i, by simpa [toList] using h⟩ <;> apply List.get_ofFn
lemma toList_ne_nil (x : RelSeries r) : x.toList ≠ [] := fun m =>
  List.eq_nil_iff_forall_not_mem.mp m (x 0) <| (List.mem_ofFn _ _).mpr ⟨_, rfl⟩
@[simps]
def fromListChain' (x : List α) (x_ne_nil : x ≠ []) (hx : x.Chain' r) : RelSeries r where
  length := x.length - 1
  toFun i := x[Fin.cast (Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x_ne_nil) i]
  step i := List.chain'_iff_get.mp hx i i.2
protected def Equiv : RelSeries r ≃ {x : List α | x ≠ [] ∧ x.Chain' r} where
  toFun x := ⟨_, x.toList_ne_nil, x.toList_chain'⟩
  invFun x := fromListChain' _ x.2.1 x.2.2
  left_inv x := ext (by simp [toList]) <| by ext; dsimp; apply List.get_ofFn
  right_inv x := by
    refine Subtype.ext (List.ext_get ?_ fun n hn1 _ => by dsimp; apply List.get_ofFn)
    have := Nat.succ_pred_eq_of_pos <| List.length_pos.mpr x.2.1
    simp_all [toList]
lemma toList_injective : Function.Injective (RelSeries.toList (r := r)) :=
  fun _ _ h ↦ (RelSeries.Equiv).injective <| Subtype.ext h
end RelSeries
namespace Rel
class FiniteDimensional : Prop where
  exists_longest_relSeries : ∃ x : RelSeries r, ∀ y : RelSeries r, y.length ≤ x.length
class InfiniteDimensional : Prop where
  exists_relSeries_with_length : ∀ n : ℕ, ∃ x : RelSeries r, x.length = n
end Rel
namespace RelSeries
protected noncomputable def longestOf [r.FiniteDimensional] : RelSeries r :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose
lemma length_le_length_longestOf [r.FiniteDimensional] (x : RelSeries r) :
    x.length ≤ (RelSeries.longestOf r).length :=
  Rel.FiniteDimensional.exists_longest_relSeries.choose_spec _
protected noncomputable def withLength [r.InfiniteDimensional] (n : ℕ) : RelSeries r :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose
@[simp] lemma length_withLength [r.InfiniteDimensional] (n : ℕ) :
    (RelSeries.withLength r n).length = n :=
  (Rel.InfiniteDimensional.exists_relSeries_with_length n).choose_spec
section
variable {r} {s : RelSeries r} {x : α}
lemma nonempty_of_infiniteDimensional [r.InfiniteDimensional] : Nonempty α :=
  ⟨RelSeries.withLength r 0 0⟩
instance membership : Membership α (RelSeries r) :=
  ⟨Function.swap (· ∈ Set.range ·)⟩
theorem mem_def : x ∈ s ↔ x ∈ Set.range s := Iff.rfl
@[simp] theorem mem_toList : x ∈ s.toList ↔ x ∈ s := by
  rw [RelSeries.toList, List.mem_ofFn, RelSeries.mem_def]
theorem subsingleton_of_length_eq_zero (hs : s.length = 0) : {x | x ∈ s}.Subsingleton := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩
  congr!
  exact finCongr (by rw [hs, zero_add]) |>.injective <| Subsingleton.elim (α := Fin 1) _ _
theorem length_ne_zero_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : s.length ≠ 0 :=
  fun hs ↦ h.not_subsingleton <| subsingleton_of_length_eq_zero hs
theorem length_pos_of_nontrivial (h : {x | x ∈ s}.Nontrivial) : 0 < s.length :=
  Nat.pos_iff_ne_zero.mpr <| length_ne_zero_of_nontrivial h
theorem length_ne_zero (irrefl : Irreflexive r) : s.length ≠ 0 ↔ {x | x ∈ s}.Nontrivial := by
  refine ⟨fun h ↦ ⟨s 0, by simp [mem_def], s 1, by simp [mem_def], fun rid ↦ irrefl (s 0) ?_⟩,
    length_ne_zero_of_nontrivial⟩
  nth_rw 2 [rid]
  convert s.step ⟨0, by omega⟩
  ext
  simpa [Nat.pos_iff_ne_zero]
theorem length_pos (irrefl : Irreflexive r) : 0 < s.length ↔ {x | x ∈ s}.Nontrivial :=
  Nat.pos_iff_ne_zero.trans <| length_ne_zero irrefl
lemma length_eq_zero (irrefl : Irreflexive r) : s.length = 0 ↔ {x | x ∈ s}.Subsingleton := by
  rw [← not_ne_iff, length_ne_zero irrefl, Set.not_nontrivial_iff]
def head (x : RelSeries r) : α := x 0
def last (x : RelSeries r) : α := x <| Fin.last _
lemma apply_last (x : RelSeries r) : x (Fin.last <| x.length) = x.last := rfl
lemma head_mem (x : RelSeries r) : x.head ∈ x := ⟨_, rfl⟩
lemma last_mem (x : RelSeries r) : x.last ∈ x := ⟨_, rfl⟩
@[simp]
lemma head_singleton {r : Rel α α} (x : α) : (singleton r x).head = x := by simp [singleton, head]
@[simp]
lemma last_singleton {r : Rel α α} (x : α) : (singleton r x).last = x := by simp [singleton, last]
end
variable {r s}
@[simps length]
def append (p q : RelSeries r) (connect : r p.last q.head) : RelSeries r where
  length := p.length + q.length + 1
  toFun := Fin.append p q ∘ Fin.cast (by omega)
  step i := by
    obtain hi | rfl | hi :=
      lt_trichotomy i (Fin.castLE (by omega) (Fin.last _ : Fin (p.length + 1)))
    · convert p.step ⟨i.1, hi⟩ <;> convert Fin.append_left p q _ <;> rfl
    · convert connect
      · convert Fin.append_left p q _
      · convert Fin.append_right p q _; rfl
    · set x := _; set y := _
      change r (Fin.append p q x) (Fin.append p q y)
      have hx : x = Fin.natAdd _ ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
          i.2.trans <| by omega⟩ := by
        ext; dsimp [x, y]; rw [Nat.add_sub_cancel']; exact hi
      have hy : y = Fin.natAdd _ ⟨i - p.length, Nat.sub_lt_left_of_lt_add (le_of_lt hi)
          (by exact i.2)⟩ := by
        ext
        dsimp
        conv_rhs => rw [Nat.add_comm p.length 1, add_assoc,
          Nat.add_sub_cancel' <| le_of_lt (show p.length < i.1 from hi), add_comm]
        rfl
      rw [hx, Fin.append_right, hy, Fin.append_right]
      convert q.step ⟨i - (p.length + 1), Nat.sub_lt_left_of_lt_add hi <|
        by convert i.2 using 1; exact Nat.add_right_comm ..⟩
      rw [Fin.succ_mk, Nat.sub_eq_iff_eq_add (le_of_lt hi : p.length ≤ i),
        Nat.add_assoc _ 1, add_comm 1, Nat.sub_add_cancel]
      exact hi
lemma append_apply_left (p q : RelSeries r) (connect : r p.last q.head)
    (i : Fin (p.length + 1)) :
    p.append q connect ((i.castAdd (q.length + 1)).cast (by dsimp; omega)) = p i := by
  delta append
  simp only [Function.comp_apply]
  convert Fin.append_left _ _ _
lemma append_apply_right (p q : RelSeries r) (connect : r p.last q.head)
    (i : Fin (q.length + 1)) :
    p.append q connect (i.natAdd p.length + 1) = q i := by
  delta append
  simp only [Fin.coe_natAdd, Nat.cast_add, Function.comp_apply]
  convert Fin.append_right _ _ _
  ext
  simp only [Fin.coe_cast, Fin.coe_natAdd]
  conv_rhs => rw [add_assoc, add_comm 1, ← add_assoc]
  change _ % _ = _
  simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.one_mod, Nat.mod_succ_eq_iff_lt]
  omega
@[simp] lemma head_append (p q : RelSeries r) (connect : r p.last q.head) :
    (p.append q connect).head = p.head :=
  append_apply_left p q connect 0
@[simp] lemma last_append (p q : RelSeries r) (connect : r p.last q.head) :
    (p.append q connect).last = q.last := by
  delta last
  convert append_apply_right p q connect (Fin.last _)
  ext
  change _ = _ % _
  simp only [append_length, Fin.val_last, Fin.natAdd_last, Nat.one_mod, Nat.mod_add_mod,
    Nat.mod_succ]
@[simps length]
def map (p : RelSeries r) (f : r →r s) : RelSeries s where
  length := p.length
  toFun := f.1.comp p
  step := (f.2 <| p.step ·)
@[simp] lemma map_apply (p : RelSeries r) (f : r →r s) (i : Fin (p.length + 1)) :
    p.map f i = f (p i) := rfl
@[simp] lemma head_map (p : RelSeries r) (f : r →r s) : (p.map f).head = f p.head := rfl
@[simp] lemma last_map (p : RelSeries r) (f : r →r s) : (p.map f).last = f p.last := rfl
@[simps]
def insertNth (p : RelSeries r) (i : Fin p.length) (a : α)
    (prev_connect : r (p (Fin.castSucc i)) a) (connect_next : r a (p i.succ)) : RelSeries r where
  toFun := (Fin.castSucc i.succ).insertNth a p
  step m := by
    set x := _; set y := _; change r x y
    obtain hm | hm | hm := lt_trichotomy m.1 i.1
    · convert p.step ⟨m, hm.trans i.2⟩
      · show Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · exact hm.trans (lt_add_one _)
        simp
      · show Fin.insertNth _ _ _ _ = _
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · change m.1 + 1 < i.1 + 1; rwa [add_lt_add_iff_right]
        simp; rfl
    · rw [show x = p m from show Fin.insertNth _ _ _ _ = _ by
        rw [Fin.insertNth_apply_below]
        pick_goal 2
        · show m.1 < i.1 + 1; exact hm ▸ lt_add_one _
        simp]
      convert prev_connect
      · ext; exact hm
      · change Fin.insertNth _ _ _ _ = _
        rw [show m.succ = i.succ.castSucc by ext; change _ + 1 = _ + 1; rw [hm],
          Fin.insertNth_apply_same]
    · rw [Nat.lt_iff_add_one_le, le_iff_lt_or_eq] at hm
      obtain hm | hm := hm
      · convert p.step ⟨m.1 - 1, Nat.sub_lt_right_of_lt_add (by omega) m.2⟩
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above (h := hm)]
          aesop
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · exact hm.trans (lt_add_one _)
          simp only [Fin.val_succ, Fin.pred_succ, eq_rec_constant, Fin.succ_mk]
          congr
          exact Fin.ext <| Eq.symm <| Nat.succ_pred_eq_of_pos (lt_trans (Nat.zero_lt_succ _) hm)
      · convert connect_next
        · change Fin.insertNth _ _ _ _ = _
          rw [show m.castSucc = i.succ.castSucc from Fin.ext hm.symm, Fin.insertNth_apply_same]
        · change Fin.insertNth _ _ _ _ = _
          rw [Fin.insertNth_apply_above]
          swap
          · change i.1 + 1 < m.1 + 1; rw [hm]; exact lt_add_one _
          simp only [Fin.pred_succ, eq_rec_constant]
          congr; ext; exact hm.symm
@[simps length]
def reverse (p : RelSeries r) : RelSeries (fun (a b : α) ↦ r b a) where
  length := p.length
  toFun := p ∘ Fin.rev
  step i := by
    rw [Function.comp_apply, Function.comp_apply]
    have hi : i.1 + 1 ≤ p.length := by omega
    convert p.step ⟨p.length - (i.1 + 1), Nat.sub_lt_self (by omega) hi⟩
    · ext; simp
    · ext
      simp only [Fin.val_rev, Fin.coe_castSucc, Nat.succ_sub_succ_eq_sub, Fin.val_succ]
      rw [Nat.sub_eq_iff_eq_add, add_assoc, add_comm 1 i.1, Nat.sub_add_cancel] <;>
      omega
@[simp] lemma reverse_apply (p : RelSeries r) (i : Fin (p.length + 1)) :
    p.reverse i = p i.rev := rfl
@[simp] lemma last_reverse (p : RelSeries r) : p.reverse.last = p.head := by
  simp [RelSeries.last, RelSeries.head]
@[simp] lemma head_reverse (p : RelSeries r) : p.reverse.head = p.last := by
  simp [RelSeries.last, RelSeries.head]
@[simp] lemma reverse_reverse {r : Rel α α} (p : RelSeries r) : p.reverse.reverse = p := by
  ext <;> simp
@[simps! length]
def cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) : RelSeries r :=
  (singleton r newHead).append p rel
@[simp] lemma head_cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) :
    (p.cons newHead rel).head = newHead := rfl
@[simp] lemma last_cons (p : RelSeries r) (newHead : α) (rel : r newHead p.head) :
    (p.cons newHead rel).last = p.last := by
  delta cons
  rw [last_append]
@[simps! length]
def snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) : RelSeries r :=
  p.append (singleton r newLast) rel
@[simp] lemma head_snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    (p.snoc newLast rel).head = p.head := by
  delta snoc; rw [head_append]
@[simp] lemma last_snoc (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    (p.snoc newLast rel).last = newLast := last_append _ _ _
@[simp] lemma last_snoc' (p : RelSeries r) (newLast : α) (rel : r p.last newLast) :
    p.snoc newLast rel (Fin.last (p.length + 1)) = newLast := last_append _ _ _
@[simp] lemma snoc_castSucc (s : RelSeries r) (a : α) (connect : r s.last a)
    (i : Fin (s.length + 1)) : snoc s a connect (Fin.castSucc i) = s i :=
  Fin.append_left _ _ i
lemma mem_snoc {p : RelSeries r} {newLast : α} {rel : r p.last newLast} {x : α} :
    x ∈ p.snoc newLast rel ↔ x ∈ p ∨ x = newLast := by
  simp only [snoc, append, singleton_length, Nat.add_zero, Nat.reduceAdd, Fin.cast_refl,
    Function.comp_id, mem_def, id_eq, Set.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact Fin.lastCases (Or.inr <| Fin.append_right _ _ 0) (fun i => Or.inl ⟨⟨i.1, i.2⟩,
      (Fin.append_left _ _ _).symm⟩) i
  · intro h
    rcases h with (⟨i, rfl⟩ | rfl)
    · exact ⟨i.castSucc, Fin.append_left _ _ _⟩
    · exact ⟨Fin.last _, Fin.append_right _ _ 0⟩
@[simps]
def tail (p : RelSeries r) (len_pos : p.length ≠ 0) : RelSeries r where
  length := p.length - 1
  toFun := Fin.tail p ∘ (Fin.cast <| Nat.succ_pred_eq_of_pos <| Nat.pos_of_ne_zero len_pos)
  step i := p.step ⟨i.1 + 1, Nat.lt_pred_iff.mp i.2⟩
@[simp] lemma head_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).head = p 1 := by
  show p (Fin.succ _) = p 1
  congr
  ext
  show (1 : ℕ) = (1 : ℕ) % _
  rw [Nat.mod_eq_of_lt]
  simpa only [lt_add_iff_pos_left, Nat.pos_iff_ne_zero]
@[simp] lemma last_tail (p : RelSeries r) (len_pos : p.length ≠ 0) :
    (p.tail len_pos).last = p.last := by
  show p _ = p _
  congr
  ext
  simp only [tail_length, Fin.val_succ, Fin.coe_cast, Fin.val_last]
  exact Nat.succ_pred_eq_of_pos (by simpa [Nat.pos_iff_ne_zero] using len_pos)
@[simps]
def eraseLast (p : RelSeries r) : RelSeries r where
  length := p.length - 1
  toFun i := p ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ tsub_le_self)⟩
  step i := p.step ⟨i, lt_of_lt_of_le i.2 tsub_le_self⟩
@[simp] lemma head_eraseLast (p : RelSeries r) : p.eraseLast.head = p.head := rfl
@[simp] lemma last_eraseLast (p : RelSeries r) :
    p.eraseLast.last = p ⟨p.length.pred, Nat.lt_succ_iff.2 (Nat.pred_le _)⟩ := rfl
lemma eraseLast_last_rel_last (p : RelSeries r) (h : p.length ≠ 0) :
    r p.eraseLast.last p.last := by
  simp only [last, Fin.last, eraseLast_length, eraseLast_toFun]
  convert p.step ⟨p.length - 1, by omega⟩
  simp only [Nat.succ_eq_add_one, Fin.succ_mk]; omega
@[simps]
def smash (p q : RelSeries r) (connect : p.last = q.head) : RelSeries r where
  length := p.length + q.length
  toFun i :=
    if H : i.1 < p.length
    then p ⟨i.1, H.trans (lt_add_one _)⟩
    else q ⟨i.1 - p.length,
      Nat.sub_lt_left_of_lt_add (by rwa [not_lt] at H) (by rw [← add_assoc]; exact i.2)⟩
  step i := by
    dsimp only
    by_cases h₂ : i.1 + 1 < p.length
    · have h₁ : i.1 < p.length := lt_trans (lt_add_one _) h₂
      erw [dif_pos h₁, dif_pos h₂]
      convert p.step ⟨i, h₁⟩ using 1
    · erw [dif_neg h₂]
      by_cases h₁ : i.1 < p.length
      · erw [dif_pos h₁]
        have h₃ : p.length = i.1 + 1 := by omega
        convert p.step ⟨i, h₁⟩ using 1
        convert connect.symm
        · aesop
        · congr; aesop
      · erw [dif_neg h₁]
        convert q.step ⟨i.1 - p.length, _⟩ using 1
        · congr
          change (i.1 + 1) - _ = _
          rw [Nat.sub_add_comm]
          rwa [not_lt] at h₁
        · refine Nat.sub_lt_left_of_lt_add ?_ i.2
          rwa [not_lt] at h₁
lemma smash_castAdd {p q : RelSeries r} (connect : p.last = q.head) (i : Fin p.length) :
    p.smash q connect (Fin.castSucc <| i.castAdd q.length) = p (Fin.castSucc i) := by
  unfold smash
  dsimp
  rw [dif_pos i.2]
  rfl
lemma smash_succ_castAdd {p q : RelSeries r} (h : p.last = q.head)
    (i : Fin p.length) : p.smash q h (i.castAdd q.length).succ = p i.succ := by
  rw [smash_toFun]
  split_ifs with H
  · congr
  · simp only [Fin.val_succ, Fin.coe_castAdd] at H
    convert h.symm
    · congr
      simp only [Fin.val_succ, Fin.coe_castAdd, Nat.zero_mod, tsub_eq_zero_iff_le]
      omega
    · congr
      ext
      change i.1 + 1 = p.length
      omega
lemma smash_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (Fin.castSucc <| i.natAdd p.length) = q (Fin.castSucc i) := by
  rw [smash_toFun, dif_neg (by simp)]
  congr
  exact Nat.add_sub_self_left _ _
lemma smash_succ_natAdd {p q : RelSeries r} (h : p.last = q.head) (i : Fin q.length) :
    smash p q h (i.natAdd p.length).succ = q i.succ := by
  rw [smash_toFun]
  split_ifs with H
  · have H' : p.length < p.length + (i.1 + 1) := by omega
    exact (lt_irrefl _ (H.trans H')).elim
  · congr
    simp only [Fin.val_succ, Fin.coe_natAdd]
    rw [add_assoc, Nat.add_sub_cancel_left]
@[simp] lemma head_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).head = p.head := by
  delta head smash
  simp only [Fin.val_zero, Fin.zero_eta, zero_le, tsub_eq_zero_of_le, dite_eq_ite,
    ite_eq_left_iff, not_lt, nonpos_iff_eq_zero]
  intro H; convert h.symm; congr; aesop
@[simp] lemma last_smash {p q : RelSeries r} (h : p.last = q.head) :
    (smash p q h).last = q.last := by
  delta smash last; aesop
@[simps! length]
def take {r : Rel α α} (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j, by omega⟩
  step := fun ⟨j, h⟩ => p.step ⟨j, by omega⟩
@[simp]
lemma head_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).head = p.head := by simp [take, head]
@[simp]
lemma last_take (p : RelSeries r) (i : Fin (p.length + 1)) :
    (p.take i).last = p i := by simp [take, last, Fin.last]
@[simps! length]
def drop (p : RelSeries r) (i : Fin (p.length + 1)) : RelSeries r where
  length := p.length - i
  toFun := fun ⟨j, h⟩ => p.toFun ⟨j+i, by omega⟩
  step := fun ⟨j, h⟩ => by
    convert p.step ⟨j+i.1, by omega⟩
    simp only [Nat.succ_eq_add_one, Fin.succ_mk]; omega
@[simp]
lemma head_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).head = p.toFun i := by
  simp [drop, head]
@[simp]
lemma last_drop (p : RelSeries r) (i : Fin (p.length + 1)) : (p.drop i).last = p.last := by
  simp only [last, drop, Fin.last]
  congr
  omega
end RelSeries
abbrev FiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.FiniteDimensional ((· < ·) : γ → γ → Prop)
instance FiniteDimensionalOrder.ofUnique (γ : Type*) [Preorder γ] [Unique γ] :
    FiniteDimensionalOrder γ where
  exists_longest_relSeries := ⟨.singleton _ default, fun x ↦ by
    by_contra! r
    exact (ne_of_lt <| x.step ⟨0, by omega⟩) <| Subsingleton.elim _ _⟩
abbrev InfiniteDimensionalOrder (γ : Type*) [Preorder γ] :=
  Rel.InfiniteDimensional ((· < ·) : γ → γ → Prop)
section LTSeries
variable (α) [Preorder α] [Preorder β]
abbrev LTSeries := RelSeries ((· < ·) : Rel α α)
namespace LTSeries
protected noncomputable def longestOf [FiniteDimensionalOrder α] : LTSeries α :=
  RelSeries.longestOf _
protected noncomputable def withLength [InfiniteDimensionalOrder α] (n : ℕ) : LTSeries α :=
  RelSeries.withLength _ n
@[simp] lemma length_withLength [InfiniteDimensionalOrder α] (n : ℕ) :
    (LTSeries.withLength α n).length = n :=
  RelSeries.length_withLength _ _
lemma nonempty_of_infiniteDimensionalType [InfiniteDimensionalOrder α] : Nonempty α :=
  ⟨LTSeries.withLength α 0 0⟩
variable {α}
lemma longestOf_is_longest [FiniteDimensionalOrder α] (x : LTSeries α) :
    x.length ≤ (LTSeries.longestOf α).length :=
  RelSeries.length_le_length_longestOf _ _
lemma longestOf_len_unique [FiniteDimensionalOrder α] (p : LTSeries α)
    (is_longest : ∀ (q : LTSeries α), q.length ≤ p.length) :
    p.length = (LTSeries.longestOf α).length :=
  le_antisymm (longestOf_is_longest _) (is_longest _)
lemma strictMono (x : LTSeries α) : StrictMono x :=
  fun _ _ h => x.rel_of_lt h
lemma monotone (x : LTSeries α) : Monotone x :=
  x.strictMono.monotone
lemma head_le_last (x : LTSeries α) : x.head ≤ x.last :=
  LTSeries.monotone x (Fin.zero_le _)
@[simps]
def mk (length : ℕ) (toFun : Fin (length + 1) → α) (strictMono : StrictMono toFun) :
    LTSeries α where
  toFun := toFun
  step i := strictMono <| lt_add_one i.1
def injStrictMono (n : ℕ) :
    {f : (l : Fin n) × (Fin (l + 1) → α) // StrictMono f.2} ↪ LTSeries α where
  toFun f := mk f.1.1 f.1.2 f.2
  inj' f g e := by
    obtain ⟨⟨lf, f⟩, mf⟩ := f
    obtain ⟨⟨lg, g⟩, mg⟩ := g
    dsimp only at mf mg e
    have leq := congr($(e).length)
    rw [mk_length lf f mf, mk_length lg g mg, Fin.val_eq_val] at leq
    subst leq
    simp_rw [Subtype.mk_eq_mk, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    have feq := fun i ↦ congr($(e).toFun i)
    simp_rw [mk_toFun lf f mf, mk_toFun lf g mg, mk_length lf f mf] at feq
    rwa [funext_iff]
@[simps!]
def map (p : LTSeries α) (f : α → β) (hf : StrictMono f) : LTSeries β :=
  LTSeries.mk p.length (f.comp p) (hf.comp p.strictMono)
@[simp] lemma head_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
  (p.map f hf).head = f p.head := rfl
@[simp] lemma last_map (p : LTSeries α) (f : α → β) (hf : StrictMono f) :
  (p.map f hf).last = f p.last := rfl
@[simps!]
noncomputable def comap (p : LTSeries β) (f : α → β)
  (comap : ∀ ⦃x y⦄, f x < f y → x < y)
  (surjective : Function.Surjective f) :
  LTSeries α := mk p.length (fun i ↦ (surjective (p i)).choose)
    (fun i j h ↦ comap (by simpa only [(surjective _).choose_spec] using p.strictMono h))
def range (n : ℕ) : LTSeries ℕ where
  length := n
  toFun := fun i => i
  step i := Nat.lt_add_one i
@[simp] lemma length_range (n : ℕ) : (range n).length = n := rfl
@[simp] lemma range_apply (n : ℕ) (i : Fin (n+1)) : (range n) i = i := rfl
@[simp] lemma head_range (n : ℕ) : (range n).head = 0 := rfl
@[simp] lemma last_range (n : ℕ) : (range n).last = n := rfl
lemma apply_add_index_le_apply_add_index_nat (p : LTSeries ℕ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩ := p.step ⟨j, by omega⟩
    norm_cast at *; omega
lemma apply_add_index_le_apply_add_index_int (p : LTSeries ℤ) (i j : Fin (p.length + 1))
    (hij : i ≤ j) : p i + j ≤ p j + i := by
  have ⟨i, hi⟩ := i
  have ⟨j, hj⟩ := j
  simp only [Fin.mk_le_mk] at hij
  simp only at *
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _hij ih =>
    specialize ih (Nat.lt_of_succ_lt hj)
    have step : p ⟨j, _⟩ < p ⟨j + 1, _⟩:= p.step ⟨j, by omega⟩
    norm_cast at *; omega
lemma head_add_length_le_nat (p : LTSeries ℕ) : p.head + p.length ≤ p.last :=
  LTSeries.apply_add_index_le_apply_add_index_nat _ _ (Fin.last _) (Fin.zero_le _)
lemma head_add_length_le_int (p : LTSeries ℤ) : p.head + p.length ≤ p.last := by
  simpa using LTSeries.apply_add_index_le_apply_add_index_int _ _ (Fin.last _) (Fin.zero_le _)
section Fintype
variable [Fintype α]
lemma length_lt_card (s : LTSeries α) : s.length < Fintype.card α := by
  by_contra! h
  obtain ⟨i, j, hn, he⟩ := Fintype.exists_ne_map_eq_of_card_lt s (by rw [Fintype.card_fin]; omega)
  wlog hl : i < j generalizing i j
  · exact this j i hn.symm he.symm (by omega)
  exact absurd he (s.strictMono hl).ne
instance [DecidableRel ((· < ·) : α → α → Prop)] : Fintype (LTSeries α) where
  elems := Finset.univ.map (injStrictMono (Fintype.card α))
  complete s := by
    have bl := s.length_lt_card
    obtain ⟨l, f, mf⟩ := s
    simp_rw [Finset.mem_map, Finset.mem_univ, true_and, Subtype.exists]
    use ⟨⟨l, bl⟩, f⟩, Fin.strictMono_iff_lt_succ.mpr mf; rfl
end Fintype
end LTSeries
end LTSeries
lemma infiniteDimensionalOrder_of_strictMono [Preorder α] [Preorder β]
    (f : α → β) (hf : StrictMono f) [InfiniteDimensionalOrder α] :
    InfiniteDimensionalOrder β :=
  ⟨fun n ↦ ⟨(LTSeries.withLength _ n).map f hf, LTSeries.length_withLength α n⟩⟩