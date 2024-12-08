import Mathlib.Data.Fin.Basic
import Mathlib.Order.Hom.Set
assert_not_exists Monoid
open Function Nat Set
namespace Fin
variable {m n : ℕ}
instance instLinearOrder : LinearOrder (Fin n) :=
  @LinearOrder.liftWithOrd (Fin n) _ _ ⟨fun x y => ⟨max x y, max_rec' (· < n) x.2 y.2⟩⟩
    ⟨fun x y => ⟨min x y, min_rec' (· < n) x.2 y.2⟩⟩ _ Fin.val Fin.val_injective (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
instance instBoundedOrder [NeZero n] : BoundedOrder (Fin n) where
  top := rev 0
  le_top i := Nat.le_pred_of_lt i.is_lt
  bot := 0
  bot_le := Fin.zero_le'
instance instPartialOrder : PartialOrder (Fin n) := inferInstance
instance instLattice      : Lattice (Fin n)      := inferInstance
lemma top_eq_last (n : ℕ) : ⊤ = Fin.last n := rfl
lemma bot_eq_zero (n : ℕ) : ⊥ = (0 : Fin (n + 1)) := rfl
@[simp] theorem rev_bot [NeZero n] : rev (⊥ : Fin n) = ⊤ := rfl
@[simp] theorem rev_top [NeZero n] : rev (⊤ : Fin n) = ⊥ := rev_rev _
theorem rev_zero_eq_top (n : ℕ) [NeZero n] : rev (0 : Fin n) = ⊤ := rfl
theorem rev_last_eq_bot (n : ℕ) : rev (last n) = ⊥ := by rw [rev_last, bot_eq_zero]
section ToFin
variable {α : Type*} [Preorder α] {f : α → Fin (n + 1)}
lemma strictMono_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : StrictMono f) :
    StrictMono (fun a => pred (f a) (hf a)) := fun _ _ h => pred_lt_pred_iff.2 (hf₂ h)
lemma monotone_pred_comp (hf : ∀ a, f a ≠ 0) (hf₂ : Monotone f) :
    Monotone (fun a => pred (f a) (hf a)) := fun _ _ h => pred_le_pred_iff.2 (hf₂ h)
lemma strictMono_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : StrictMono f) :
    StrictMono (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_lt_castPred_iff.2 (hf₂ h)
lemma monotone_castPred_comp (hf : ∀ a, f a ≠ last n) (hf₂ : Monotone f) :
    Monotone (fun a => castPred (f a) (hf a)) := fun _ _ h => castPred_le_castPred_iff.2 (hf₂ h)
end ToFin
section FromFin
variable {α : Type*} [Preorder α] {f : Fin (n + 1) → α}
lemma strictMono_iff_lt_succ : StrictMono f ↔ ∀ i : Fin n, f (castSucc i) < f i.succ :=
  liftFun_iff_succ (· < ·)
lemma monotone_iff_le_succ : Monotone f ↔ ∀ i : Fin n, f (castSucc i) ≤ f i.succ :=
  monotone_iff_forall_lt.trans <| liftFun_iff_succ (· ≤ ·)
lemma strictAnti_iff_succ_lt : StrictAnti f ↔ ∀ i : Fin n, f i.succ < f (castSucc i) :=
  liftFun_iff_succ (· > ·)
lemma antitone_iff_succ_le : Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f (castSucc i) :=
  antitone_iff_forall_lt.trans <| liftFun_iff_succ (· ≥ ·)
end FromFin
lemma val_strictMono : StrictMono (val : Fin n → ℕ) := fun _ _ ↦ id
lemma cast_strictMono {k l : ℕ} (h : k = l) : StrictMono (cast h) := fun {_ _} h ↦ h
lemma strictMono_succ : StrictMono (succ : Fin n → Fin (n + 1)) := fun _ _ ↦ succ_lt_succ
lemma strictMono_castLE (h : n ≤ m) : StrictMono (castLE h : Fin n → Fin m) := fun _ _ ↦ id
lemma strictMono_castAdd (m) : StrictMono (castAdd m : Fin n → Fin (n + m)) := strictMono_castLE _
lemma strictMono_castSucc : StrictMono (castSucc : Fin n → Fin (n + 1)) := strictMono_castAdd _
lemma strictMono_natAdd (n) : StrictMono (natAdd n : Fin m → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_left (show i.val < j.val from h) _
lemma strictMono_addNat (m) : StrictMono ((addNat · m) : Fin n → Fin (n + m)) :=
  fun i j h ↦ Nat.add_lt_add_right (show i.val < j.val from h) _
lemma strictMono_succAbove (p : Fin (n + 1)) : StrictMono (succAbove p) :=
  strictMono_castSucc.ite strictMono_succ
    (fun _ _ hij hj => (castSucc_lt_castSucc_iff.mpr hij).trans hj) fun i =>
    (castSucc_lt_succ i).le
variable {p : Fin (n + 1)} {i j : Fin n}
lemma succAbove_lt_succAbove_iff : succAbove p i < succAbove p j ↔ i < j :=
  (strictMono_succAbove p).lt_iff_lt
lemma succAbove_le_succAbove_iff : succAbove p i ≤ succAbove p j ↔ i ≤ j :=
  (strictMono_succAbove p).le_iff_le
lemma predAbove_right_monotone (p : Fin n) : Monotone p.predAbove := fun a b H => by
  dsimp [predAbove]
  split_ifs with ha hb hb
  all_goals simp only [le_iff_val_le_val, coe_pred]
  · exact pred_le_pred H
  · calc
      _ ≤ _ := Nat.pred_le _
      _ ≤ _ := H
  · exact le_pred_of_lt ((not_lt.mp ha).trans_lt hb)
  · exact H
lemma predAbove_left_monotone (i : Fin (n + 1)) : Monotone fun p ↦ predAbove p i := fun a b H ↦ by
  dsimp [predAbove]
  split_ifs with ha hb hb
  · rfl
  · exact pred_le _
  · have : b < a := castSucc_lt_castSucc_iff.mpr (hb.trans_le (le_of_not_gt ha))
    exact absurd H this.not_le
  · rfl
@[simps!] def predAboveOrderHom (p : Fin n) : Fin (n + 1) →o Fin n :=
  ⟨p.predAbove, p.predAbove_right_monotone⟩
@[simps! apply symm_apply]
def orderIsoSubtype : Fin n ≃o {i // i < n} :=
  equivSubtype.toOrderIso (by simp [Monotone]) (by simp [Monotone])
@[simps]
def castOrderIso (eq : n = m) : Fin n ≃o Fin m where
  toEquiv := ⟨cast eq, cast eq.symm, leftInverse_cast eq, rightInverse_cast eq⟩
  map_rel_iff' := cast_le_cast eq
@[deprecated (since := "2024-05-23")] alias castIso := castOrderIso
@[simp]
lemma symm_castOrderIso (h : n = m) : (castOrderIso h).symm = castOrderIso h.symm := by subst h; rfl
@[deprecated (since := "2024-05-23")] alias symm_castIso := symm_castOrderIso
@[simp]
lemma castOrderIso_refl (h : n = n := rfl) : castOrderIso h = OrderIso.refl (Fin n) := by ext; simp
@[deprecated (since := "2024-05-23")] alias castIso_refl := castOrderIso_refl
lemma castOrderIso_toEquiv (h : n = m) : (castOrderIso h).toEquiv = Equiv.cast (h ▸ rfl) := by
  subst h; rfl
@[deprecated (since := "2024-05-23")] alias castIso_to_equiv := castOrderIso_toEquiv
@[simps! apply toEquiv]
def revOrderIso : (Fin n)ᵒᵈ ≃o Fin n := ⟨OrderDual.ofDual.trans revPerm, rev_le_rev⟩
@[simp]
lemma revOrderIso_symm_apply (i : Fin n) : revOrderIso.symm i = OrderDual.toDual (rev i) := rfl
@[simps! apply]
def valOrderEmb (n) : Fin n ↪o ℕ := ⟨valEmbedding, Iff.rfl⟩
instance Lt.isWellOrder (n) : IsWellOrder (Fin n) (· < ·) := (valOrderEmb n).isWellOrder
def succOrderEmb (n : ℕ) : Fin n ↪o Fin (n + 1) := .ofStrictMono succ strictMono_succ
@[simp, norm_cast] lemma coe_succOrderEmb : ⇑(succOrderEmb n) = Fin.succ := rfl
@[simps! apply toEmbedding]
def castLEOrderEmb (h : n ≤ m) : Fin n ↪o Fin m := .ofStrictMono (castLE h) (strictMono_castLE h)
@[simps! apply toEmbedding]
def castAddOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (castAdd m) (strictMono_castAdd m)
@[simps! apply toEmbedding]
def castSuccOrderEmb : Fin n ↪o Fin (n + 1) := .ofStrictMono castSucc strictMono_castSucc
@[simps! apply toEmbedding]
def addNatOrderEmb (m) : Fin n ↪o Fin (n + m) := .ofStrictMono (addNat · m) (strictMono_addNat m)
@[simps! apply toEmbedding]
def natAddOrderEmb (n) : Fin m ↪o Fin (n + m) := .ofStrictMono (natAdd n) (strictMono_natAdd n)
@[simps! apply toEmbedding]
def succAboveOrderEmb (p : Fin (n + 1)) : Fin n ↪o Fin (n + 1) :=
  OrderEmbedding.ofStrictMono (succAbove p) (strictMono_succAbove p)
variable {α : Type*} [Preorder α]
@[simp] lemma coe_orderIso_apply (e : Fin n ≃o Fin m) (i : Fin n) : (e i : ℕ) = i := by
  rcases i with ⟨i, hi⟩
  dsimp only
  induction' i using Nat.strong_induction_on with i h
  refine le_antisymm (forall_lt_iff_le.1 fun j hj => ?_) (forall_lt_iff_le.1 fun j hj => ?_)
  · have := e.symm.lt_iff_lt.2 (mk_lt_of_lt_val hj)
    rw [e.symm_apply_apply] at this
    have : _ < i := this
    convert this
    simpa using h _ this (e.symm _).is_lt
  · rwa [← h j hj (hj.trans hi), ← lt_iff_val_lt_val, e.lt_iff_lt]
@[deprecated StrictMono.range_inj (since := "2024-09-17")]
lemma strictMono_unique {f g : Fin n → α} (hf : StrictMono f) (hg : StrictMono g)
    (h : range f = range g) : f = g :=
  (hf.range_inj hg).1 h
@[deprecated OrderEmbedding.range_inj (since := "2024-09-17")]
lemma orderEmbedding_eq {f g : Fin n ↪o α} (h : range f = range g) : f = g :=
  OrderEmbedding.range_inj.1 h
end Fin