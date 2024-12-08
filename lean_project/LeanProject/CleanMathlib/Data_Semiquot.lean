import Mathlib.Data.Set.Lattice
structure Semiquot (α : Type*) where mk' ::
  s : Set α
  val : Trunc s
namespace Semiquot
variable {α : Type*} {β : Type*}
instance : Membership α (Semiquot α) :=
  ⟨fun q a => a ∈ q.s⟩
def mk {a : α} {s : Set α} (h : a ∈ s) : Semiquot α :=
  ⟨s, Trunc.mk ⟨a, h⟩⟩
theorem ext_s {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ q₁.s = q₂.s := by
  refine ⟨congr_arg _, fun h => ?_⟩
  cases' q₁ with _ v₁; cases' q₂ with _ v₂; congr
  exact Subsingleton.helim (congrArg Trunc (congrArg Set.Elem h)) v₁ v₂
theorem ext {q₁ q₂ : Semiquot α} : q₁ = q₂ ↔ ∀ a, a ∈ q₁ ↔ a ∈ q₂ :=
  ext_s.trans Set.ext_iff
theorem exists_mem (q : Semiquot α) : ∃ a, a ∈ q :=
  let ⟨⟨a, h⟩, _⟩ := q.2.exists_rep
  ⟨a, h⟩
theorem eq_mk_of_mem {q : Semiquot α} {a : α} (h : a ∈ q) : q = @mk _ a q.1 h :=
  ext_s.2 rfl
theorem nonempty (q : Semiquot α) : q.s.Nonempty :=
  q.exists_mem
protected def pure (a : α) : Semiquot α :=
  mk (Set.mem_singleton a)
@[simp]
theorem mem_pure' {a b : α} : a ∈ Semiquot.pure b ↔ a = b :=
  Set.mem_singleton_iff
def blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) : Semiquot α :=
  ⟨s, Trunc.lift (fun a : q.s => Trunc.mk ⟨a.1, h a.2⟩) (fun _ _ => Trunc.eq _ _) q.2⟩
def blur (s : Set α) (q : Semiquot α) : Semiquot α :=
  blur' q (s.subset_union_right (t := q.s))
theorem blur_eq_blur' (q : Semiquot α) (s : Set α) (h : q.s ⊆ s) : blur s q = blur' q h := by
  unfold blur; congr; exact Set.union_eq_self_of_subset_right h
@[simp]
theorem mem_blur' (q : Semiquot α) {s : Set α} (h : q.s ⊆ s) {a : α} : a ∈ blur' q h ↔ a ∈ s :=
  Iff.rfl
def ofTrunc (q : Trunc α) : Semiquot α :=
  ⟨Set.univ, q.map fun a => ⟨a, trivial⟩⟩
def toTrunc (q : Semiquot α) : Trunc α :=
  q.2.map Subtype.val
def liftOn (q : Semiquot α) (f : α → β) (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) : β :=
  Trunc.liftOn q.2 (fun x => f x.1) fun x y => h _ x.2 _ y.2
theorem liftOn_ofMem (q : Semiquot α) (f : α → β)
    (h : ∀ a ∈ q, ∀ b ∈ q, f a = f b) (a : α) (aq : a ∈ q) : liftOn q f h = f a := by
  revert h; rw [eq_mk_of_mem aq]; intro; rfl
def map (f : α → β) (q : Semiquot α) : Semiquot β :=
  ⟨f '' q.1, q.2.map fun x => ⟨f x.1, Set.mem_image_of_mem _ x.2⟩⟩
@[simp]
theorem mem_map (f : α → β) (q : Semiquot α) (b : β) : b ∈ map f q ↔ ∃ a, a ∈ q ∧ f a = b :=
  Set.mem_image _ _ _
def bind (q : Semiquot α) (f : α → Semiquot β) : Semiquot β :=
  ⟨⋃ a ∈ q.1, (f a).1, q.2.bind fun a => (f a.1).2.map fun b => ⟨b.1, Set.mem_biUnion a.2 b.2⟩⟩
@[simp]
theorem mem_bind (q : Semiquot α) (f : α → Semiquot β) (b : β) :
    b ∈ bind q f ↔ ∃ a ∈ q, b ∈ f a := by simp_rw [← exists_prop]; exact Set.mem_iUnion₂
instance : Monad Semiquot where
  pure := @Semiquot.pure
  map := @Semiquot.map
  bind := @Semiquot.bind
@[simp]
theorem map_def {β} : ((· <$> ·) : (α → β) → Semiquot α → Semiquot β) = map :=
  rfl
@[simp]
theorem bind_def {β} : ((· >>= ·) : Semiquot α → (α → Semiquot β) → Semiquot β) = bind :=
  rfl
@[simp]
theorem mem_pure {a b : α} : a ∈ (pure b : Semiquot α) ↔ a = b :=
  Set.mem_singleton_iff
theorem mem_pure_self (a : α) : a ∈ (pure a : Semiquot α) :=
  Set.mem_singleton a
@[simp]
theorem pure_inj {a b : α} : (pure a : Semiquot α) = pure b ↔ a = b :=
  ext_s.trans Set.singleton_eq_singleton_iff
instance : LawfulMonad Semiquot := LawfulMonad.mk'
  (pure_bind := fun {α β} x f => ext.2 <| by simp)
  (bind_assoc := fun {α β} γ s f g =>
    ext.2 <| by
    simp only [bind_def, mem_bind]
    exact fun c => ⟨fun ⟨b, ⟨a, as, bf⟩, cg⟩ => ⟨a, as, b, bf, cg⟩,
      fun ⟨a, as, b, bf, cg⟩ => ⟨b, ⟨a, as, bf⟩, cg⟩⟩)
  (id_map := fun {α} q => ext.2 <| by simp)
  (bind_pure_comp := fun {α β} f s => ext.2 <| by simp [eq_comm])
instance : LE (Semiquot α) :=
  ⟨fun s t => s.s ⊆ t.s⟩
instance partialOrder : PartialOrder (Semiquot α) where
  le s t := ∀ ⦃x⦄, x ∈ s → x ∈ t
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h₁ h₂ := ext_s.2 (Set.Subset.antisymm h₁ h₂)
instance : SemilatticeSup (Semiquot α) :=
  { Semiquot.partialOrder with
    sup := fun s => blur s.s
    le_sup_left := fun _ _ => Set.subset_union_left
    le_sup_right := fun _ _ => Set.subset_union_right
    sup_le := fun _ _ _ => Set.union_subset }
@[simp]
theorem pure_le {a : α} {s : Semiquot α} : pure a ≤ s ↔ a ∈ s :=
  Set.singleton_subset_iff
def IsPure (q : Semiquot α) : Prop :=
  ∀ a ∈ q, ∀ b ∈ q, a = b
def get (q : Semiquot α) (h : q.IsPure) : α :=
  liftOn q id h
theorem get_mem {q : Semiquot α} (p) : get q p ∈ q := by
  let ⟨a, h⟩ := exists_mem q
  unfold get; rw [liftOn_ofMem q _ _ a h]; exact h
theorem eq_pure {q : Semiquot α} (p) : q = pure (get q p) :=
  ext.2 fun a => by simpa using ⟨fun h => p _ h _ (get_mem _), fun e => e.symm ▸ get_mem _⟩
@[simp]
theorem pure_isPure (a : α) : IsPure (pure a)
  | b, ab, c, ac => by
    rw [mem_pure] at ab ac
    rwa [← ac] at ab
theorem isPure_iff {s : Semiquot α} : IsPure s ↔ ∃ a, s = pure a :=
  ⟨fun h => ⟨_, eq_pure h⟩, fun ⟨_, e⟩ => e.symm ▸ pure_isPure _⟩
theorem IsPure.mono {s t : Semiquot α} (st : s ≤ t) (h : IsPure t) : IsPure s
  | _, as, _, bs => h _ (st as) _ (st bs)
theorem IsPure.min {s t : Semiquot α} (h : IsPure t) : s ≤ t ↔ s = t :=
  ⟨fun st =>
    le_antisymm st <| by
      rw [eq_pure h, eq_pure (h.mono st)]; simpa using h _ (get_mem _) _ (st <| get_mem _),
    le_of_eq⟩
theorem isPure_of_subsingleton [Subsingleton α] (q : Semiquot α) : IsPure q
  | _, _, _, _ => Subsingleton.elim _ _
def univ [Inhabited α] : Semiquot α :=
  mk <| Set.mem_univ default
instance [Inhabited α] : Inhabited (Semiquot α) :=
  ⟨univ⟩
@[simp]
theorem mem_univ [Inhabited α] : ∀ a, a ∈ @univ α _ :=
  @Set.mem_univ α
@[congr]
theorem univ_unique (I J : Inhabited α) : @univ _ I = @univ _ J :=
  ext.2 fun a => refl (a ∈ univ)
@[simp]
theorem isPure_univ [Inhabited α] : @IsPure α univ ↔ Subsingleton α :=
  ⟨fun h => ⟨fun a b => h a trivial b trivial⟩, fun ⟨h⟩ a _ b _ => h a b⟩
instance [Inhabited α] : OrderTop (Semiquot α) where
  top := univ
  le_top _ := Set.subset_univ _
end Semiquot