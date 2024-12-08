import Mathlib.Algebra.Module.Submodule.Lattice
assert_not_exists Field
variable {R R₂ K M M₂ V S : Type*}
namespace Submodule
open Function Set
open Pointwise
section AddCommMonoid
variable [Semiring R] [AddCommMonoid M] [Module R M]
variable {x : M} (p p' : Submodule R M)
variable [Semiring R₂] {σ₁₂ : R →+* R₂}
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]
section
variable (R)
def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }
variable {R}
@[mk_iff]
class IsPrincipal (S : Submodule R M) : Prop where
  principal' : ∃ a, S = span R {a}
theorem IsPrincipal.principal (S : Submodule R M) [S.IsPrincipal] :
    ∃ a, S = span R {a} :=
  Submodule.IsPrincipal.principal'
end
variable {s t : Set M}
theorem mem_span : x ∈ span R s ↔ ∀ p : Submodule R M, s ⊆ p → x ∈ p :=
  mem_iInter₂
@[aesop safe 20 apply (rule_sets := [SetLike])]
theorem subset_span : s ⊆ span R s := fun _ h => mem_span.2 fun _ hp => hp h
theorem span_le {p} : span R s ≤ p ↔ s ⊆ p :=
  ⟨Subset.trans subset_span, fun ss _ h => mem_span.1 h _ ss⟩
@[gcongr] theorem span_mono (h : s ⊆ t) : span R s ≤ span R t :=
  span_le.2 <| Subset.trans h subset_span
theorem span_monotone : Monotone (span R : Set M → Submodule R M) := fun _ _ => span_mono
theorem span_eq_of_le (h₁ : s ⊆ p) (h₂ : p ≤ span R s) : span R s = p :=
  le_antisymm (span_le.2 h₁) h₂
theorem span_eq : span R (p : Set M) = p :=
  span_eq_of_le _ (Subset.refl _) subset_span
theorem span_eq_span (hs : s ⊆ span R t) (ht : t ⊆ span R s) : span R s = span R t :=
  le_antisymm (span_le.2 hs) (span_le.2 ht)
lemma coe_span_eq_self [SetLike S M] [AddSubmonoidClass S M] [SMulMemClass S R M] (s : S) :
    (span R (s : Set M) : Set M) = s := by
  refine le_antisymm ?_ subset_span
  let s' : Submodule R M :=
    { carrier := s
      add_mem' := add_mem
      zero_mem' := zero_mem _
      smul_mem' := SMulMemClass.smul_mem }
  exact span_le (p := s') |>.mpr le_rfl
@[simp]
theorem span_insert_zero : span R (insert (0 : M) s) = span R s := by
  refine le_antisymm ?_ (Submodule.span_mono (Set.subset_insert 0 s))
  rw [span_le, Set.insert_subset_iff]
  exact ⟨by simp only [SetLike.mem_coe, Submodule.zero_mem], Submodule.subset_span⟩
theorem closure_subset_span {s : Set M} : (AddSubmonoid.closure s : Set M) ⊆ span R s :=
  (@AddSubmonoid.closure_le _ _ _ (span R s).toAddSubmonoid).mpr subset_span
theorem closure_le_toAddSubmonoid_span {s : Set M} :
    AddSubmonoid.closure s ≤ (span R s).toAddSubmonoid :=
  closure_subset_span
@[simp]
theorem span_closure {s : Set M} : span R (AddSubmonoid.closure s : Set M) = span R s :=
  le_antisymm (span_le.mpr closure_subset_span) (span_mono AddSubmonoid.subset_closure)
@[elab_as_elim]
theorem span_induction {p : (x : M) → x ∈ span R s → Prop}
    (mem : ∀ (x) (h : x ∈ s), p x (subset_span h))
    (zero : p 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›))
    (smul : ∀ (a : R) (x hx), p x hx → p (a • x) (Submodule.smul_mem _ _ ‹_›)) {x}
    (hx : x ∈ span R s) : p x hx := by
  let p : Submodule R M :=
    { carrier := { x | ∃ hx, p x hx }
      add_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, add _ _ _ _ hpx hpy⟩
      zero_mem' := ⟨_, zero⟩
      smul_mem' := fun r ↦ fun ⟨_, hpx⟩ ↦ ⟨_, smul r _ _ hpx⟩ }
  exact span_le (p := p) |>.mpr (fun y hy ↦ ⟨subset_span hy, mem y hy⟩) hx |>.elim fun _ ↦ id
@[deprecated span_induction (since := "2024-10-10")]
alias span_induction' := span_induction
theorem span_induction₂ {p : (x y : M) → x ∈ span R s → y ∈ span R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_span hx) (subset_span hy))
    (zero_left : ∀ y hy, p 0 y (zero_mem _) hy) (zero_right : ∀ x hx, p x 0 hx (zero_mem _))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (smul_left : ∀ (r : R) x y hx hy, p x y hx hy → p (r • x) y (smul_mem _ r hx) hy)
    (smul_right : ∀ (r : R) x y hx hy, p x y hx hy → p x (r • y) hx (smul_mem _ r hy))
    {a b : M} (ha : a ∈ Submodule.span R s)
    (hb : b ∈ Submodule.span R s) : p a b ha hb := by
  induction hb using span_induction with
  | mem z hz => induction ha using span_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | zero => exact zero_left _ _
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
    | smul _ _ _ h => exact smul_left _ _ _ _ _ h
  | zero => exact zero_right a ha
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂
  | smul _ _ _ h => exact smul_right _ _ _ _ _ h
open AddSubmonoid in
theorem span_eq_closure {s : Set M} : (span R s).toAddSubmonoid = closure (@univ R • s) := by
  refine le_antisymm (fun x (hx : x ∈ span R s) ↦ ?of_mem_span) (fun x hx ↦ ?of_mem_closure)
  case of_mem_span =>
    induction hx using span_induction with
    | mem x hx => exact subset_closure ⟨1, trivial, x, hx, one_smul R x⟩
    | zero => exact zero_mem _
    | add _ _ _ _ h₁ h₂ => exact add_mem h₁ h₂
    | smul r₁ y _h hy =>
      clear _h
      induction hy using AddSubmonoid.closure_induction with
      | mem _ h =>
        obtain ⟨r₂, -, x, hx, rfl⟩ := h
        exact subset_closure ⟨r₁ * r₂, trivial, x, hx, mul_smul ..⟩
      | one => simpa only [smul_zero] using zero_mem _
      | mul _ _ _ _ h₁ h₂ => simpa only [smul_add] using add_mem h₁ h₂
  case of_mem_closure =>
    refine closure_le.2 ?_ hx
    rintro - ⟨r, -, x, hx, rfl⟩
    exact smul_mem _ _ (subset_span hx)
open AddSubmonoid in
@[elab_as_elim]
theorem closure_induction {p : (x : M) → x ∈ span R s → Prop}
    (zero : p 0 (Submodule.zero_mem _))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (Submodule.add_mem _ ‹_› ‹_›))
    (smul_mem : ∀ (r x) (h : x ∈ s), p (r • x) (Submodule.smul_mem _ _ <| subset_span h)) {x}
    (hx : x ∈ span R s) : p x hx := by
  have key {v} : v ∈ span R s ↔ v ∈ closure (@univ R • s) := by simp [← span_eq_closure]
  refine AddSubmonoid.closure_induction (p := fun x hx ↦ p x (key.mpr hx))
    ?_ zero (by simpa only [key] using add) (key.mp hx)
  rintro - ⟨r, -, x, hx, rfl⟩
  exact smul_mem r x hx
@[deprecated closure_induction (since := "2024-10-10")]
alias closure_induction' := closure_induction
@[simp]
theorem span_span_coe_preimage : span R (((↑) : span R s → M) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    span_induction (fun _ h ↦ subset_span h) (zero_mem _) (fun _ _ _ _ ↦ add_mem)
      (fun _ _ _ ↦ smul_mem _ _) hx'
@[simp]
lemma span_setOf_mem_eq_top :
    span R {x : span R s | (x : M) ∈ s} = ⊤ :=
  span_span_coe_preimage
theorem span_nat_eq_addSubmonoid_closure (s : Set M) :
    (span ℕ s).toAddSubmonoid = AddSubmonoid.closure s := by
  refine Eq.symm (AddSubmonoid.closure_eq_of_le subset_span ?_)
  apply (OrderIso.to_galoisConnection (AddSubmonoid.toNatSubmodule (M := M)).symm).l_le
     (a := span ℕ s) (b := AddSubmonoid.closure s)
  rw [span_le]
  exact AddSubmonoid.subset_closure
@[simp]
theorem span_nat_eq (s : AddSubmonoid M) : (span ℕ (s : Set M)).toAddSubmonoid = s := by
  rw [span_nat_eq_addSubmonoid_closure, s.closure_eq]
theorem span_int_eq_addSubgroup_closure {M : Type*} [AddCommGroup M] (s : Set M) :
    (span ℤ s).toAddSubgroup = AddSubgroup.closure s :=
  Eq.symm <|
    AddSubgroup.closure_eq_of_le _ subset_span fun _ hx =>
      span_induction (fun _ hx => AddSubgroup.subset_closure hx) (AddSubgroup.zero_mem _)
        (fun _ _ _ _ => AddSubgroup.add_mem _) (fun _ _ _ _ => AddSubgroup.zsmul_mem _ ‹_› _) hx
@[simp]
theorem span_int_eq {M : Type*} [AddCommGroup M] (s : AddSubgroup M) :
    (span ℤ (s : Set M)).toAddSubgroup = s := by rw [span_int_eq_addSubgroup_closure, s.closure_eq]
section
variable (R M)
protected def gi : GaloisInsertion (@span R M _ _ _) (↑) where
  choice s _ := span R s
  gc _ _ := span_le
  le_l_u _ := subset_span
  choice_eq _ _ := rfl
end
@[simp]
theorem span_empty : span R (∅ : Set M) = ⊥ :=
  (Submodule.gi R M).gc.l_bot
@[simp]
theorem span_univ : span R (univ : Set M) = ⊤ :=
  eq_top_iff.2 <| SetLike.le_def.2 <| subset_span
theorem span_union (s t : Set M) : span R (s ∪ t) = span R s ⊔ span R t :=
  (Submodule.gi R M).gc.l_sup
theorem span_iUnion {ι} (s : ι → Set M) : span R (⋃ i, s i) = ⨆ i, span R (s i) :=
  (Submodule.gi R M).gc.l_iSup
theorem span_iUnion₂ {ι} {κ : ι → Sort*} (s : ∀ i, κ i → Set M) :
    span R (⋃ (i) (j), s i j) = ⨆ (i) (j), span R (s i j) :=
  (Submodule.gi R M).gc.l_iSup₂
theorem span_attach_biUnion [DecidableEq M] {α : Type*} (s : Finset α) (f : s → Finset M) :
    span R (s.attach.biUnion f : Set M) = ⨆ x, span R (f x) := by simp [span_iUnion]
theorem sup_span : p ⊔ span R s = span R (p ∪ s) := by rw [Submodule.span_union, p.span_eq]
theorem span_sup : span R s ⊔ p = span R (s ∪ p) := by rw [Submodule.span_union, p.span_eq]
notation:1000
R " ∙ " x => span R (singleton x)
theorem span_eq_iSup_of_singleton_spans (s : Set M) : span R s = ⨆ x ∈ s, R ∙ x := by
  simp only [← span_iUnion, Set.biUnion_of_singleton s]
theorem span_range_eq_iSup {ι : Sort*} {v : ι → M} : span R (range v) = ⨆ i, R ∙ v i := by
  rw [span_eq_iSup_of_singleton_spans, iSup_range]
theorem span_smul_le (s : Set M) (r : R) : span R (r • s) ≤ span R s := by
  rw [span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact smul_mem (span R s) r (subset_span hx)
theorem subset_span_trans {U V W : Set M} (hUV : U ⊆ Submodule.span R V)
    (hVW : V ⊆ Submodule.span R W) : U ⊆ Submodule.span R W :=
  (Submodule.gi R M).gc.le_u_l_trans hUV hVW
@[simp]
theorem coe_iSup_of_directed {ι} [Nonempty ι] (S : ι → Submodule R M)
    (H : Directed (· ≤ ·) S) : ((iSup S : Submodule R M) : Set M) = ⋃ i, S i :=
  let s : Submodule R M :=
    { __ := AddSubmonoid.copy _ _ (AddSubmonoid.coe_iSup_of_directed H).symm
      smul_mem' := fun r _ hx ↦ have ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        Set.mem_iUnion.mpr ⟨i, (S i).smul_mem' r hi⟩ }
  have : iSup S = s := le_antisymm
    (iSup_le fun i ↦ le_iSup (fun i ↦ (S i : Set M)) i) (Set.iUnion_subset fun _ ↦ le_iSup S _)
  this.symm ▸ rfl
@[simp]
theorem mem_iSup_of_directed {ι} [Nonempty ι] (S : ι → Submodule R M) (H : Directed (· ≤ ·) S) {x} :
    x ∈ iSup S ↔ ∃ i, x ∈ S i := by
  rw [← SetLike.mem_coe, coe_iSup_of_directed S H, mem_iUnion]
  rfl
theorem mem_sSup_of_directed {s : Set (Submodule R M)} {z} (hs : s.Nonempty)
    (hdir : DirectedOn (· ≤ ·) s) : z ∈ sSup s ↔ ∃ y ∈ s, z ∈ y := by
  have : Nonempty s := hs.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed _ hdir.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
@[norm_cast, simp]
theorem coe_iSup_of_chain (a : ℕ →o Submodule R M) : (↑(⨆ k, a k) : Set M) = ⋃ k, (a k : Set M) :=
  coe_iSup_of_directed a a.monotone.directed_le
@[simp]
theorem mem_iSup_of_chain (a : ℕ →o Submodule R M) (m : M) : (m ∈ ⨆ k, a k) ↔ ∃ k, m ∈ a k :=
  mem_iSup_of_directed a a.monotone.directed_le
section
variable {p p'}
theorem mem_sup : x ∈ p ⊔ p' ↔ ∃ y ∈ p, ∃ z ∈ p', y + z = x :=
  ⟨fun h => by
    rw [← span_eq p, ← span_eq p', ← span_union] at h
    refine span_induction ?_ ?_ ?_ ?_ h
    · rintro y (h | h)
      · exact ⟨y, h, 0, by simp, by simp⟩
      · exact ⟨0, by simp, y, h, by simp⟩
    · exact ⟨0, by simp, 0, by simp⟩
    · rintro _ _ - - ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨_, add_mem hy₁ hy₂, _, add_mem hz₁ hz₂, by
        rw [add_assoc, add_assoc, ← add_assoc y₂, ← add_assoc z₁, add_comm y₂]⟩
    · rintro a - _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨_, smul_mem _ a hy, _, smul_mem _ a hz, by simp [smul_add]⟩, by
    rintro ⟨y, hy, z, hz, rfl⟩
    exact add_mem ((le_sup_left : p ≤ p ⊔ p') hy) ((le_sup_right : p' ≤ p ⊔ p') hz)⟩
theorem mem_sup' : x ∈ p ⊔ p' ↔ ∃ (y : p) (z : p'), (y : M) + z = x :=
  mem_sup.trans <| by simp only [Subtype.exists, exists_prop]
lemma exists_add_eq_of_codisjoint (h : Codisjoint p p') (x : M) :
    ∃ y ∈ p, ∃ z ∈ p', y + z = x := by
  suffices x ∈ p ⊔ p' by exact Submodule.mem_sup.mp this
  simpa only [h.eq_top] using Submodule.mem_top
variable (p p')
theorem coe_sup : ↑(p ⊔ p') = (p + p' : Set M) := by
  ext
  rw [SetLike.mem_coe, mem_sup, Set.mem_add]
  simp
theorem sup_toAddSubmonoid : (p ⊔ p').toAddSubmonoid = p.toAddSubmonoid ⊔ p'.toAddSubmonoid := by
  ext x
  rw [mem_toAddSubmonoid, mem_sup, AddSubmonoid.mem_sup]
  rfl
theorem sup_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p p' : Submodule R M) : (p ⊔ p').toAddSubgroup = p.toAddSubgroup ⊔ p'.toAddSubgroup := by
  ext x
  rw [mem_toAddSubgroup, mem_sup, AddSubgroup.mem_sup]
  rfl
end
theorem mem_span_singleton_self (x : M) : x ∈ R ∙ x :=
  subset_span rfl
theorem nontrivial_span_singleton {x : M} (h : x ≠ 0) : Nontrivial (R ∙ x) :=
  ⟨by
    use 0, ⟨x, Submodule.mem_span_singleton_self x⟩
    intro H
    rw [eq_comm, Submodule.mk_eq_zero] at H
    exact h H⟩
theorem mem_span_singleton {y : M} : (x ∈ R ∙ y) ↔ ∃ a : R, a • y = x :=
  ⟨fun h => by
    refine span_induction ?_ ?_ ?_ ?_ h
    · rintro y (rfl | ⟨⟨_⟩⟩)
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩
    · rintro _ _ - - ⟨a, rfl⟩ ⟨b, rfl⟩
      exact ⟨a + b, by simp [add_smul]⟩
    · rintro a _ - ⟨b, rfl⟩
      exact ⟨a * b, by simp [smul_smul]⟩, by
    rintro ⟨a, y, rfl⟩; exact smul_mem _ _ (subset_span <| by simp)⟩
theorem le_span_singleton_iff {s : Submodule R M} {v₀ : M} :
    (s ≤ R ∙ v₀) ↔ ∀ v ∈ s, ∃ r : R, r • v₀ = v := by simp_rw [SetLike.le_def, mem_span_singleton]
variable (R)
theorem span_singleton_eq_top_iff (x : M) : (R ∙ x) = ⊤ ↔ ∀ v, ∃ r : R, r • x = v := by
  rw [eq_top_iff, le_span_singleton_iff]
  tauto
@[simp]
theorem span_zero_singleton : (R ∙ (0 : M)) = ⊥ := by
  ext
  simp [mem_span_singleton, eq_comm]
theorem span_singleton_eq_range (y : M) : ↑(R ∙ y) = range ((· • y) : R → M) :=
  Set.ext fun _ => mem_span_singleton
theorem span_singleton_smul_le {S} [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (r : S) (x : M) : (R ∙ r • x) ≤ R ∙ x := by
  rw [span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  exact smul_of_tower_mem _ _ (mem_span_singleton_self _)
theorem span_singleton_group_smul_eq {G} [Group G] [SMul G R] [MulAction G M] [IsScalarTower G R M]
    (g : G) (x : M) : (R ∙ g • x) = R ∙ x := by
  refine le_antisymm (span_singleton_smul_le R g x) ?_
  convert span_singleton_smul_le R g⁻¹ (g • x)
  exact (inv_smul_smul g x).symm
variable {R}
theorem span_singleton_smul_eq {r : R} (hr : IsUnit r) (x : M) : (R ∙ r • x) = R ∙ x := by
  lift r to Rˣ using hr
  rw [← Units.smul_def]
  exact span_singleton_group_smul_eq R r x
theorem mem_span_singleton_trans {x y z : M} (hxy : x ∈ R ∙ y) (hyz : y ∈ R ∙ z) : x ∈ R ∙ z := by
  rw [← SetLike.mem_coe, ← singleton_subset_iff] at *
  exact Submodule.subset_span_trans hxy hyz
theorem span_insert (x) (s : Set M) : span R (insert x s) = (R ∙ x) ⊔ span R s := by
  rw [insert_eq, span_union]
theorem span_insert_eq_span (h : x ∈ span R s) : span R (insert x s) = span R s :=
  span_eq_of_le _ (Set.insert_subset_iff.mpr ⟨h, subset_span⟩) (span_mono <| subset_insert _ _)
theorem span_span : span R (span R s : Set M) = span R s :=
  span_eq _
theorem mem_span_insert {y} :
    x ∈ span R (insert y s) ↔ ∃ a : R, ∃ z ∈ span R s, x = a • y + z := by
  simp [span_insert, mem_sup, mem_span_singleton, eq_comm (a := x)]
theorem mem_span_pair {x y z : M} :
    z ∈ span R ({x, y} : Set M) ↔ ∃ a b : R, a • x + b • y = z := by
  simp_rw [mem_span_insert, mem_span_singleton, exists_exists_eq_and, eq_comm]
theorem span_eq_bot : span R (s : Set M) = ⊥ ↔ ∀ x ∈ s, (x : M) = 0 :=
  eq_bot_iff.trans
    ⟨fun H _ h => (mem_bot R).1 <| H <| subset_span h, fun H =>
      span_le.2 fun x h => (mem_bot R).2 <| H x h⟩
@[simp]
theorem span_singleton_eq_bot : (R ∙ x) = ⊥ ↔ x = 0 :=
  span_eq_bot.trans <| by simp
@[simp]
theorem span_zero : span R (0 : Set M) = ⊥ := by rw [← singleton_zero, span_singleton_eq_bot]
@[simp]
theorem span_singleton_le_iff_mem (m : M) (p : Submodule R M) : (R ∙ m) ≤ p ↔ m ∈ p := by
  rw [span_le, singleton_subset_iff, SetLike.mem_coe]
theorem iSup_span {ι : Sort*} (p : ι → Set M) : ⨆ i, span R (p i) = span R (⋃ i, p i) :=
  le_antisymm (iSup_le fun i => span_mono <| subset_iUnion _ i) <|
    span_le.mpr <| iUnion_subset fun i _ hm => mem_iSup_of_mem i <| subset_span hm
theorem iSup_eq_span {ι : Sort*} (p : ι → Submodule R M) : ⨆ i, p i = span R (⋃ i, ↑(p i)) := by
  simp_rw [← iSup_span, span_eq]
theorem submodule_eq_sSup_le_nonzero_spans (p : Submodule R M) :
    p = sSup { T : Submodule R M | ∃ m ∈ p, m ≠ 0 ∧ T = span R {m} } := by
  let S := { T : Submodule R M | ∃ m ∈ p, m ≠ 0 ∧ T = span R {m} }
  apply le_antisymm
  · intro m hm
    by_cases h : m = 0
    · rw [h]
      simp
    · exact @le_sSup _ _ S _ ⟨m, ⟨hm, ⟨h, rfl⟩⟩⟩ m (mem_span_singleton_self m)
  · rw [sSup_le_iff]
    rintro S ⟨_, ⟨_, ⟨_, rfl⟩⟩⟩
    rwa [span_singleton_le_iff_mem]
theorem lt_sup_iff_not_mem {I : Submodule R M} {a : M} : (I < I ⊔ R ∙ a) ↔ a ∉ I := by simp
theorem mem_iSup {ι : Sort*} (p : ι → Submodule R M) {m : M} :
    (m ∈ ⨆ i, p i) ↔ ∀ N, (∀ i, p i ≤ N) → m ∈ N := by
  rw [← span_singleton_le_iff_mem, le_iSup_iff]
  simp only [span_singleton_le_iff_mem]
theorem mem_sSup {s : Set (Submodule R M)} {m : M} :
    (m ∈ sSup s) ↔ ∀ N, (∀ p ∈ s, p ≤ N) → m ∈ N := by
  simp_rw [sSup_eq_iSup, Submodule.mem_iSup, iSup_le_iff]
section
theorem mem_span_finite_of_mem_span {S : Set M} {x : M} (hx : x ∈ span R S) :
    ∃ T : Finset M, ↑T ⊆ S ∧ x ∈ span R (T : Set M) := by
  classical
  refine span_induction (fun x hx => ?_) ?_ ?_ ?_ hx
  · refine ⟨{x}, ?_, ?_⟩
    · rwa [Finset.coe_singleton, Set.singleton_subset_iff]
    · rw [Finset.coe_singleton]
      exact Submodule.mem_span_singleton_self x
  · use ∅
    simp
  · rintro x y - - ⟨X, hX, hxX⟩ ⟨Y, hY, hyY⟩
    refine ⟨X ∪ Y, ?_, ?_⟩
    · rw [Finset.coe_union]
      exact Set.union_subset hX hY
    rw [Finset.coe_union, span_union, mem_sup]
    exact ⟨x, hxX, y, hyY, rfl⟩
  · rintro a x - ⟨T, hT, h2⟩
    exact ⟨T, hT, smul_mem _ _ h2⟩
end
end AddCommMonoid
section AddCommGroup
variable [Ring R] [AddCommGroup M] [Module R M]
theorem mem_span_insert' {x y} {s : Set M} :
    x ∈ span R (insert y s) ↔ ∃ a : R, x + a • y ∈ span R s := by
  rw [mem_span_insert]; constructor
  · rintro ⟨a, z, hz, rfl⟩
    exact ⟨-a, by simp [hz, add_assoc]⟩
  · rintro ⟨a, h⟩
    exact ⟨-a, _, h, by simp [add_comm, add_left_comm]⟩
end AddCommGroup
end Submodule