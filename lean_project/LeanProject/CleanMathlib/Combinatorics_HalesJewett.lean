import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Shrink
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Finite.Prod
open Function
open scoped Classical
universe u v
variable {η α ι κ : Type*}
namespace Combinatorics
@[ext]
structure Subspace (η α ι : Type*) where
  idxFun : ι → α ⊕ η
  proper : ∀ e, ∃ i, idxFun i = Sum.inr e
namespace Subspace
variable {η α ι κ : Type*} {l : Subspace η α ι} {x : η → α} {i : ι} {a : α} {e : η}
instance : Inhabited (Subspace ι α ι) := ⟨⟨Sum.inr, fun i ↦ ⟨i, rfl⟩⟩⟩
@[coe] def toFun (l : Subspace η α ι) (x : η → α) (i : ι) : α := (l.idxFun i).elim id x
instance instCoeFun : CoeFun (Subspace η α ι) (fun _ ↦ (η → α) → ι → α) := ⟨toFun⟩
lemma coe_apply (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Subspace η α ι → (η → α) → ι → α) := by
  rintro l m hlm
  ext i
  simp only [funext_iff] at hlm
  cases hl : idxFun l i with
  | inl a =>
    obtain ⟨b, hba⟩ := exists_ne a
    cases hm : idxFun m i <;> simpa [hl, hm, hba.symm, coe_apply] using hlm (const _ b) i
  | inr e =>
    cases hm : idxFun m i with
    | inl a =>
      obtain ⟨b, hba⟩ := exists_ne a
      simpa [hl, hm, hba, coe_apply] using hlm (const _ b) i
    | inr f =>
      obtain ⟨a, b, hab⟩ := exists_pair_ne α
      simp only [Sum.inr.injEq]
      by_contra! hef
      simpa [hl, hm, hef, hab, coe_apply] using hlm (Function.update (const _ a) f b) i
lemma apply_def (l : Subspace η α ι) (x : η → α) (i : ι) : l x i = (l.idxFun i).elim id x := rfl
lemma apply_inl (h : l.idxFun i = Sum.inl a) : l x i = a := by simp [apply_def, h]
lemma apply_inr (h : l.idxFun i = Sum.inr e) : l x i = x e := by simp [apply_def, h]
def IsMono (C : (ι → α) → κ) (l : Subspace η α ι) : Prop := ∃ c, ∀ x, C (l x) = c
variable {η' α' ι' : Type*}
def reindex (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : Subspace η' α' ι' where
  idxFun i := (l.idxFun <| eι.symm i).map eα eη
  proper e := (eι.exists_congr fun i ↦ by cases h : idxFun l i <;>
    simp [*, funext_iff, Equiv.eq_symm_apply]).1 <| l.proper <| eη.symm e
@[simp] lemma reindex_apply (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') (x i) :
    l.reindex eη eα eι x i = eα (l (eα.symm ∘ x ∘ eη) <| eι.symm i) := by
  cases h : l.idxFun (eι.symm i) <;> simp [h, reindex, coe_apply]
@[simp] lemma reindex_isMono {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι' → α') → κ} :
    (l.reindex eη eα eι).IsMono C ↔ l.IsMono fun x ↦ C <| eα ∘ x ∘ eι.symm := by
  simp only [IsMono, funext (reindex_apply _ _ _ _ _), coe_apply]
  exact exists_congr fun c ↦ (eη.arrowCongr eα).symm.forall_congr <| by aesop
protected lemma IsMono.reindex {eη : η ≃ η'} {eα : α ≃ α'} {eι : ι ≃ ι'} {C : (ι → α) → κ}
    (hl : l.IsMono C) : (l.reindex eη eα eι).IsMono fun x ↦ C <| eα.symm ∘ x ∘ eι := by
  simp [reindex_isMono, Function.comp_assoc]; simpa [← Function.comp_assoc]
end Subspace
@[ext]
structure Line (α ι : Type*) where
  idxFun : ι → Option α
  proper : ∃ i, idxFun i = none
namespace Line
variable {l : Line α ι} {i : ι} {a x : α}
@[coe] def toFun (l : Line α ι) (x : α) (i : ι) : α := (l.idxFun i).getD x
instance instCoeFun : CoeFun (Line α ι) fun _ => α → ι → α :=
  ⟨fun l x i => (l.idxFun i).getD x⟩
lemma coe_apply (l : Line α ι) (x : α) (i : ι) : l x i = (l.idxFun i).getD x := rfl
lemma coe_injective [Nontrivial α] : Injective ((⇑) : Line α ι → α → ι → α) := by
  rintro l m hlm
  ext i a
  obtain ⟨b, hba⟩ := exists_ne a
  simp only [Option.mem_def, funext_iff] at hlm ⊢
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases hi : idxFun m i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i
  · cases hi : idxFun l i <;> simpa [@eq_comm _ a, hi, h, hba] using hlm b i
def IsMono {α ι κ} (C : (ι → α) → κ) (l : Line α ι) : Prop :=
  ∃ c, ∀ x, C (l x) = c
def toSubspaceUnit (l : Line α ι) : Subspace Unit α ι where
  idxFun i := (l.idxFun i).elim (.inr ()) .inl
  proper _ := l.proper.imp fun i hi ↦ by simp [hi]
@[simp] lemma toSubspaceUnit_apply (l : Line α ι) (a) : ⇑l.toSubspaceUnit a = l (a ()) := by
  ext i; cases h : l.idxFun i <;> simp [toSubspaceUnit, h, Subspace.coe_apply]
@[simp] lemma toSubspaceUnit_isMono {C : (ι → α) → κ} : l.toSubspaceUnit.IsMono C ↔ l.IsMono C := by
  simp only [Subspace.IsMono, toSubspaceUnit_apply, IsMono]
  exact exists_congr fun c ↦ ⟨fun h a ↦ h fun _ ↦ a, fun h a ↦ h _⟩
protected alias ⟨_, IsMono.toSubspaceUnit⟩ := toSubspaceUnit_isMono
def toSubspace (l : Line (η → α) ι) : Subspace η α (ι × η) where
  idxFun ie := (l.idxFun ie.1).elim (.inr ie.2) (fun f ↦ .inl <| f ie.2)
  proper e := let ⟨i, hi⟩ := l.proper; ⟨(i, e), by simp [hi]⟩
@[simp] lemma toSubspace_apply (l : Line (η → α) ι) (a ie) :
    ⇑l.toSubspace a ie = l a ie.1 ie.2 := by
  cases h : l.idxFun ie.1 <;> simp [toSubspace, h, coe_apply, Subspace.coe_apply]
@[simp] lemma toSubspace_isMono {l : Line (η → α) ι} {C : (ι × η → α) → κ} :
    l.toSubspace.IsMono C ↔ l.IsMono fun x : ι → η → α  ↦ C fun (i, e) ↦ x i e := by
  simp [Subspace.IsMono, IsMono, funext (toSubspace_apply _ _)]
protected alias ⟨_, IsMono.toSubspace⟩ := toSubspace_isMono
def diagonal (α ι) [Nonempty ι] : Line α ι where
  idxFun _ := none
  proper := ⟨Classical.arbitrary ι, rfl⟩
instance (α ι) [Nonempty ι] : Inhabited (Line α ι) :=
  ⟨diagonal α ι⟩
structure AlmostMono {α ι κ : Type*} (C : (ι → Option α) → κ) where
  line : Line (Option α) ι
  color : κ
  has_color : ∀ x : α, C (line (some x)) = color
instance {α ι κ : Type*} [Nonempty ι] [Inhabited κ] :
    Inhabited (AlmostMono fun _ : ι → Option α => (default : κ)) :=
  ⟨{  line := default
      color := default
      has_color := fun _ ↦ rfl}⟩
structure ColorFocused {α ι κ : Type*} (C : (ι → Option α) → κ) where
  lines : Multiset (AlmostMono C)
  focus : ι → Option α
  is_focused : ∀ p ∈ lines, p.line none = focus
  distinct_colors : (lines.map AlmostMono.color).Nodup
instance {α ι κ} (C : (ι → Option α) → κ) : Inhabited (ColorFocused C) := by
  refine ⟨⟨0, fun _ => none, fun h => ?_, Multiset.nodup_zero⟩⟩
  simp only [Multiset.not_mem_zero, IsEmpty.forall_iff]
def map {α α' ι} (f : α → α') (l : Line α ι) : Line α' ι where
  idxFun i := (l.idxFun i).map f
  proper := ⟨l.proper.choose, by simp only [l.proper.choose_spec, Option.map_none']⟩
def vertical {α ι ι'} (v : ι → α) (l : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim (some ∘ v) l.idxFun
  proper := ⟨Sum.inr l.proper.choose, l.proper.choose_spec⟩
def horizontal {α ι ι'} (l : Line α ι) (v : ι' → α) : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun (some ∘ v)
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩
def prod {α ι ι'} (l : Line α ι) (l' : Line α ι') : Line α (ι ⊕ ι') where
  idxFun := Sum.elim l.idxFun l'.idxFun
  proper := ⟨Sum.inl l.proper.choose, l.proper.choose_spec⟩
theorem apply_def (l : Line α ι) (x : α) : l x = fun i => (l.idxFun i).getD x := rfl
theorem apply_none {α ι} (l : Line α ι) (x : α) (i : ι) (h : l.idxFun i = none) : l x i = x := by
  simp only [Option.getD_none, h, l.apply_def]
lemma apply_some (h : l.idxFun i = some a) : l x i = a := by simp [l.apply_def, h]
@[simp]
theorem map_apply {α α' ι} (f : α → α') (l : Line α ι) (x : α) : l.map f (f x) = f ∘ l x := by
  simp only [Line.apply_def, Line.map, Option.getD_map, comp_def]
@[simp]
theorem vertical_apply {α ι ι'} (v : ι → α) (l : Line α ι') (x : α) :
    l.vertical v x = Sum.elim v (l x) := by
  funext i
  cases i <;> rfl
@[simp]
theorem horizontal_apply {α ι ι'} (l : Line α ι) (v : ι' → α) (x : α) :
    l.horizontal v x = Sum.elim (l x) v := by
  funext i
  cases i <;> rfl
@[simp]
theorem prod_apply {α ι ι'} (l : Line α ι) (l' : Line α ι') (x : α) :
    l.prod l' x = Sum.elim (l x) (l' x) := by
  funext i
  cases i <;> rfl
@[simp]
theorem diagonal_apply {α ι} [Nonempty ι] (x : α) : Line.diagonal α ι x = fun _ => x := by
  simp_rw [Line.diagonal, Option.getD_none]
private theorem exists_mono_in_high_dimension' :
    ∀ (α : Type u) [Finite α] (κ : Type max v u) [Finite κ],
      ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  Finite.induction_empty_option
  (
  fun {α α'} e =>
    forall_imp fun κ =>
      forall_imp fun _ =>
        Exists.imp fun ι =>
          Exists.imp fun _ h C =>
            let ⟨l, c, lc⟩ := h fun v => C (e ∘ v)
            ⟨l.map e, c, e.forall_congr_right.mp fun x => by rw [← lc x, Line.map_apply]⟩)
  (by
    intro κ _
    by_cases h : Nonempty κ
    · refine ⟨Unit, inferInstance, fun C => ⟨default, Classical.arbitrary _, PEmpty.rec⟩⟩
    · exact ⟨Empty, inferInstance, fun C => (h ⟨C (Empty.rec)⟩).elim⟩)
  (by
    intro α _ ihα κ _
    cases nonempty_fintype κ
    by_cases h : Nonempty α
    case neg =>
      refine ⟨Unit, inferInstance, fun C => ⟨diagonal _ Unit, C fun _ => none, ?_⟩⟩
      rintro (_ | ⟨a⟩)
      · rfl
      · exact (h ⟨a⟩).elim
    suffices key :
      ∀ r : ℕ,
        ∃ (ι : Type) (_ : Fintype ι),
          ∀ C : (ι → Option α) → κ,
            (∃ s : ColorFocused C, Multiset.card s.lines = r) ∨ ∃ l, IsMono C l by
      obtain ⟨ι, _inst, hι⟩ := key (Fintype.card κ + 1)
      refine ⟨ι, _inst, fun C => (hι C).resolve_left ?_⟩
      rintro ⟨s, sr⟩
      apply Nat.not_succ_le_self (Fintype.card κ)
      rw [← Nat.add_one, ← sr, ← Multiset.card_map, ← Finset.card_mk]
      exact Finset.card_le_univ ⟨_, s.distinct_colors⟩
    intro r
    induction' r with r ihr
    · exact ⟨Empty, inferInstance, fun C => Or.inl ⟨default, Multiset.card_zero⟩⟩
    obtain ⟨ι, _inst, hι⟩ := ihr
    specialize ihα ((ι → Option α) → κ)
    obtain ⟨ι', _inst, hι'⟩ := ihα
    refine ⟨ι ⊕ ι', inferInstance, ?_⟩
    intro C
    specialize hι' fun v' v => C (Sum.elim v (some ∘ v'))
    obtain ⟨l', C', hl'⟩ := hι'
    have mono_of_mono : (∃ l, IsMono C' l) → ∃ l, IsMono C l := by
      rintro ⟨l, c, hl⟩
      refine ⟨l.horizontal (some ∘ l' (Classical.arbitrary α)), c, fun x => ?_⟩
      rw [Line.horizontal_apply, ← hl, ← hl']
    specialize hι C'
    rcases hι with (⟨s, sr⟩ | h)
    on_goal 2 => exact Or.inr (mono_of_mono h)
    by_cases h : ∃ p ∈ s.lines, (p : AlmostMono _).color = C' s.focus
    · obtain ⟨p, p_mem, hp⟩ := h
      refine Or.inr (mono_of_mono ⟨p.line, p.color, ?_⟩)
      rintro (_ | _)
      · rw [hp, s.is_focused p p_mem]
      · apply p.has_color
    refine Or.inl ⟨⟨(s.lines.map ?_).cons ⟨(l'.map some).vertical s.focus, C' s.focus, fun x => ?_⟩,
            Sum.elim s.focus (l'.map some none), ?_, ?_⟩, ?_⟩
    · refine fun p => ⟨p.line.prod (l'.map some), p.color, fun x => ?_⟩
      rw [Line.prod_apply, Line.map_apply, ← p.has_color, ← congr_fun (hl' x)]
    · rw [vertical_apply, ← congr_fun (hl' x), Line.map_apply]
    · simp_rw [Multiset.mem_cons, Multiset.mem_map]
      rintro _ (rfl | ⟨q, hq, rfl⟩)
      · simp only [vertical_apply]
      · simp only [prod_apply, s.is_focused q hq]
    · rw [Multiset.map_cons, Multiset.map_map, Multiset.nodup_cons, Multiset.mem_map]
      exact ⟨fun ⟨q, hq, he⟩ => h ⟨q, hq, he⟩, s.distinct_colors⟩
    · rw [Multiset.card_cons, Multiset.card_map, sr])
theorem exists_mono_in_high_dimension (α : Type u) [Finite α] (κ : Type v) [Finite κ] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Line α ι, l.IsMono C :=
  let ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension'.{u,v} α (ULift.{u,v} κ)
  ⟨ι, ιfin, fun C =>
    let ⟨l, c, hc⟩ := hι (ULift.up ∘ C)
    ⟨l, c.down, fun x => by rw [← hc x, Function.comp_apply]⟩⟩
end Line
theorem exists_mono_homothetic_copy {M κ : Type*} [AddCommMonoid M] (S : Finset M) [Finite κ]
    (C : M → κ) : ∃ a > 0, ∃ (b : M) (c : κ), ∀ s ∈ S, C (a • s + b) = c := by
  obtain ⟨ι, _inst, hι⟩ := Line.exists_mono_in_high_dimension S κ
  specialize hι fun v => C <| ∑ i, v i
  obtain ⟨l, c, hl⟩ := hι
  set s : Finset ι := Finset.univ.filter (fun i => l.idxFun i = none) with hs
  refine
    ⟨s.card, Finset.card_pos.mpr ⟨l.proper.choose, ?_⟩, ∑ i ∈ sᶜ, ((l.idxFun i).map ?_).getD 0,
      c, ?_⟩
  · rw [hs, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, l.proper.choose_spec⟩
  · exact fun m => m
  intro x xs
  rw [← hl ⟨x, xs⟩]
  clear hl; congr
  rw [← Finset.sum_add_sum_compl s]
  congr 1
  · rw [← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right, Subtype.coe_mk]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [hs, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
    simp_rw [← hy, Option.map_some', Option.getD]
namespace Subspace
theorem exists_mono_in_high_dimension (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ (ι : Type) (_ : Fintype ι), ∀ C : (ι → α) → κ, ∃ l : Subspace η α ι, l.IsMono C := by
  cases nonempty_fintype η
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Shrink.{0} η → α) κ
  refine ⟨ι × Shrink η, inferInstance, fun C ↦ ?_⟩
  obtain ⟨l, hl⟩ := hι fun x ↦ C fun (i, e) ↦ x i e
  refine ⟨l.toSubspace.reindex (equivShrink.{0} η).symm (Equiv.refl _) (Equiv.refl _), ?_⟩
  convert hl.toSubspace.reindex
  simp
theorem exists_mono_in_high_dimension_fin (α κ η) [Finite α] [Finite κ] [Finite η] :
    ∃ n, ∀ C : (Fin n → α) → κ, ∃ l : Subspace η α (Fin n), l.IsMono C := by
  obtain ⟨ι, ιfin, hι⟩ := exists_mono_in_high_dimension α κ η
  refine ⟨Fintype.card ι, fun C ↦ ?_⟩
  obtain ⟨l, c, cl⟩ := hι fun v ↦ C (v ∘ (Fintype.equivFin _).symm)
  refine ⟨⟨l.idxFun ∘ (Fintype.equivFin _).symm, fun e ↦ ?_⟩, c, cl⟩
  obtain ⟨i, hi⟩ := l.proper e
  use Fintype.equivFin _ i
  simpa using hi
end Subspace
end Combinatorics