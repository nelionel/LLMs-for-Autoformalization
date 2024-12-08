import Mathlib.Algebra.Group.Submonoid.Operations
import Mathlib.Algebra.Group.Subgroup.Defs
assert_not_exists OrderedAddCommMonoid
assert_not_exists Multiset
assert_not_exists Ring
open Function
open scoped Int
variable {G : Type*} [Group G]
section mul_add
variable {A : Type*} [AddGroup A]
@[simps!]
def Subgroup.toAddSubgroup : Subgroup G ≃o AddSubgroup (Additive G) where
  toFun S := { Submonoid.toAddSubmonoid S.toSubmonoid with neg_mem' := S.inv_mem' }
  invFun S := { AddSubmonoid.toSubmonoid S.toAddSubmonoid with inv_mem' := S.neg_mem' }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
abbrev AddSubgroup.toSubgroup' : AddSubgroup (Additive G) ≃o Subgroup G :=
  Subgroup.toAddSubgroup.symm
@[simps!]
def AddSubgroup.toSubgroup : AddSubgroup A ≃o Subgroup (Multiplicative A) where
  toFun S := { AddSubmonoid.toSubmonoid S.toAddSubmonoid with inv_mem' := S.neg_mem' }
  invFun S := { Submonoid.toAddSubmonoid S.toSubmonoid with neg_mem' := S.inv_mem' }
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_rel_iff' := Iff.rfl
abbrev Subgroup.toAddSubgroup' : Subgroup (Multiplicative A) ≃o AddSubgroup A :=
  AddSubgroup.toSubgroup.symm
end mul_add
namespace Subgroup
variable (H K : Subgroup G)
@[to_additive "The `AddSubgroup G` of the `AddGroup G`."]
instance : Top (Subgroup G) :=
  ⟨{ (⊤ : Submonoid G) with inv_mem' := fun _ => Set.mem_univ _ }⟩
@[to_additive (attr := simps!)
      "The top additive subgroup is isomorphic to the additive group.
      This is the additive group version of `AddSubmonoid.topEquiv`."]
def topEquiv : (⊤ : Subgroup G) ≃* G :=
  Submonoid.topEquiv
@[to_additive "The trivial `AddSubgroup` `{0}` of an `AddGroup` `G`."]
instance : Bot (Subgroup G) :=
  ⟨{ (⊥ : Submonoid G) with inv_mem' := by simp}⟩
@[to_additive]
instance : Inhabited (Subgroup G) :=
  ⟨⊥⟩
@[to_additive (attr := simp)]
theorem mem_bot {x : G} : x ∈ (⊥ : Subgroup G) ↔ x = 1 :=
  Iff.rfl
@[to_additive (attr := simp)]
theorem mem_top (x : G) : x ∈ (⊤ : Subgroup G) :=
  Set.mem_univ x
@[to_additive (attr := simp)]
theorem coe_top : ((⊤ : Subgroup G) : Set G) = Set.univ :=
  rfl
@[to_additive (attr := simp)]
theorem coe_bot : ((⊥ : Subgroup G) : Set G) = {1} :=
  rfl
@[to_additive]
instance : Unique (⊥ : Subgroup G) :=
  ⟨⟨1⟩, fun g => Subtype.ext g.2⟩
@[to_additive (attr := simp)]
theorem top_toSubmonoid : (⊤ : Subgroup G).toSubmonoid = ⊤ :=
  rfl
@[to_additive (attr := simp)]
theorem bot_toSubmonoid : (⊥ : Subgroup G).toSubmonoid = ⊥ :=
  rfl
@[to_additive]
theorem eq_bot_iff_forall : H = ⊥ ↔ ∀ x ∈ H, x = (1 : G) :=
  toSubmonoid_injective.eq_iff.symm.trans <| Submonoid.eq_bot_iff_forall _
@[to_additive]
theorem eq_bot_of_subsingleton [Subsingleton H] : H = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rw [← Subgroup.coe_mk H y hy, Subsingleton.elim (⟨y, hy⟩ : H) 1, Subgroup.coe_one]
@[to_additive (attr := simp, norm_cast)]
theorem coe_eq_univ {H : Subgroup G} : (H : Set G) = Set.univ ↔ H = ⊤ :=
  (SetLike.ext'_iff.trans (by rfl)).symm
@[to_additive]
theorem coe_eq_singleton {H : Subgroup G} : (∃ g : G, (H : Set G) = {g}) ↔ H = ⊥ :=
  ⟨fun ⟨g, hg⟩ =>
    haveI : Subsingleton (H : Set G) := by
      rw [hg]
      infer_instance
    H.eq_bot_of_subsingleton,
    fun h => ⟨1, SetLike.ext'_iff.mp h⟩⟩
@[to_additive]
theorem nontrivial_iff_exists_ne_one (H : Subgroup G) : Nontrivial H ↔ ∃ x ∈ H, x ≠ (1 : G) := by
  rw [Subtype.nontrivial_iff_exists_ne (fun x => x ∈ H) (1 : H)]
  simp
@[to_additive]
theorem exists_ne_one_of_nontrivial (H : Subgroup G) [Nontrivial H] :
    ∃ x ∈ H, x ≠ 1 := by
  rwa [← Subgroup.nontrivial_iff_exists_ne_one]
@[to_additive]
theorem nontrivial_iff_ne_bot (H : Subgroup G) : Nontrivial H ↔ H ≠ ⊥ := by
  rw [nontrivial_iff_exists_ne_one, ne_eq, eq_bot_iff_forall]
  simp only [ne_eq, not_forall, exists_prop]
@[to_additive "A subgroup is either the trivial subgroup or nontrivial."]
theorem bot_or_nontrivial (H : Subgroup G) : H = ⊥ ∨ Nontrivial H := by
  have := nontrivial_iff_ne_bot H
  tauto
@[to_additive "A subgroup is either the trivial subgroup or contains a nonzero element."]
theorem bot_or_exists_ne_one (H : Subgroup G) : H = ⊥ ∨ ∃ x ∈ H, x ≠ (1 : G) := by
  convert H.bot_or_nontrivial
  rw [nontrivial_iff_exists_ne_one]
@[to_additive]
lemma ne_bot_iff_exists_ne_one {H : Subgroup G} : H ≠ ⊥ ↔ ∃ a : ↥H, a ≠ 1 := by
  rw [← nontrivial_iff_ne_bot, nontrivial_iff_exists_ne_one]
  simp only [ne_eq, Subtype.exists, mk_eq_one, exists_prop]
@[to_additive "The inf of two `AddSubgroup`s is their intersection."]
instance : Min (Subgroup G) :=
  ⟨fun H₁ H₂ =>
    { H₁.toSubmonoid ⊓ H₂.toSubmonoid with
      inv_mem' := fun ⟨hx, hx'⟩ => ⟨H₁.inv_mem hx, H₂.inv_mem hx'⟩ }⟩
@[to_additive (attr := simp)]
theorem coe_inf (p p' : Subgroup G) : ((p ⊓ p' : Subgroup G) : Set G) = (p : Set G) ∩ p' :=
  rfl
@[to_additive (attr := simp)]
theorem mem_inf {p p' : Subgroup G} {x : G} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' :=
  Iff.rfl
@[to_additive]
instance : InfSet (Subgroup G) :=
  ⟨fun s =>
    { (⨅ S ∈ s, Subgroup.toSubmonoid S).copy (⋂ S ∈ s, ↑S) (by simp) with
      inv_mem' := fun {x} hx =>
        Set.mem_biInter fun i h => i.inv_mem (by apply Set.mem_iInter₂.1 hx i h) }⟩
@[to_additive (attr := simp, norm_cast)]
theorem coe_sInf (H : Set (Subgroup G)) : ((sInf H : Subgroup G) : Set G) = ⋂ s ∈ H, ↑s :=
  rfl
@[to_additive (attr := simp)]
theorem mem_sInf {S : Set (Subgroup G)} {x : G} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
@[to_additive]
theorem mem_iInf {ι : Sort*} {S : ι → Subgroup G} {x : G} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]
@[to_additive (attr := simp, norm_cast)]
theorem coe_iInf {ι : Sort*} {S : ι → Subgroup G} : (↑(⨅ i, S i) : Set G) = ⋂ i, S i := by
  simp only [iInf, coe_sInf, Set.biInter_range]
@[to_additive "The `AddSubgroup`s of an `AddGroup` form a complete lattice."]
instance : CompleteLattice (Subgroup G) :=
  { completeLatticeOfInf (Subgroup G) fun _s =>
      IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf with
    bot := ⊥
    bot_le := fun S _x hx => (mem_bot.1 hx).symm ▸ S.one_mem
    top := ⊤
    le_top := fun _S x _hx => mem_top x
    inf := (· ⊓ ·)
    le_inf := fun _a _b _c ha hb _x hx => ⟨ha hx, hb hx⟩
    inf_le_left := fun _a _b _x => And.left
    inf_le_right := fun _a _b _x => And.right }
@[to_additive]
theorem mem_sup_left {S T : Subgroup G} : ∀ {x : G}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; fun h ↦ this h
@[to_additive]
theorem mem_sup_right {S T : Subgroup G} : ∀ {x : G}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; fun h ↦ this h
@[to_additive]
theorem mul_mem_sup {S T : Subgroup G} {x y : G} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
@[to_additive]
theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Subgroup G} (i : ι) :
    ∀ {x : G}, x ∈ S i → x ∈ iSup S :=
  have : S i ≤ iSup S := le_iSup _ _; fun h ↦ this h
@[to_additive]
theorem mem_sSup_of_mem {S : Set (Subgroup G)} {s : Subgroup G} (hs : s ∈ S) :
    ∀ {x : G}, x ∈ s → x ∈ sSup S :=
  have : s ≤ sSup S := le_sSup hs; fun h ↦ this h
@[to_additive (attr := simp)]
theorem subsingleton_iff : Subsingleton (Subgroup G) ↔ Subsingleton G :=
  ⟨fun _ =>
    ⟨fun x y =>
      have : ∀ i : G, i = 1 := fun i =>
        mem_bot.mp <| Subsingleton.elim (⊤ : Subgroup G) ⊥ ▸ mem_top i
      (this x).trans (this y).symm⟩,
    fun _ => ⟨fun x y => Subgroup.ext fun i => Subsingleton.elim 1 i ▸ by simp [Subgroup.one_mem]⟩⟩
@[to_additive (attr := simp)]
theorem nontrivial_iff : Nontrivial (Subgroup G) ↔ Nontrivial G :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans subsingleton_iff).trans
      not_nontrivial_iff_subsingleton.symm)
@[to_additive]
instance [Subsingleton G] : Unique (Subgroup G) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ (subsingleton_iff.mpr ‹_›) a _⟩
@[to_additive]
instance [Nontrivial G] : Nontrivial (Subgroup G) :=
  nontrivial_iff.mpr ‹_›
@[to_additive]
theorem eq_top_iff' : H = ⊤ ↔ ∀ x : G, x ∈ H :=
  eq_top_iff.trans ⟨fun h m => h <| mem_top m, fun h m _ => h m⟩
@[to_additive "The `AddSubgroup` generated by a set"]
def closure (k : Set G) : Subgroup G :=
  sInf { K | k ⊆ K }
variable {k : Set G}
@[to_additive]
theorem mem_closure {x : G} : x ∈ closure k ↔ ∀ K : Subgroup G, k ⊆ K → x ∈ K :=
  mem_sInf
@[to_additive (attr := simp, aesop safe 20 apply (rule_sets := [SetLike]))
  "The `AddSubgroup` generated by a set includes the set."]
theorem subset_closure : k ⊆ closure k := fun _ hx => mem_closure.2 fun _ hK => hK hx
@[to_additive]
theorem not_mem_of_not_mem_closure {P : G} (hP : P ∉ closure k) : P ∉ k := fun h =>
  hP (subset_closure h)
open Set
@[to_additive (attr := simp)
  "An additive subgroup `K` includes `closure k` if and only if it includes `k`"]
theorem closure_le : closure k ≤ K ↔ k ⊆ K :=
  ⟨Subset.trans subset_closure, fun h => sInf_le h⟩
@[to_additive]
theorem closure_eq_of_le (h₁ : k ⊆ K) (h₂ : K ≤ closure k) : closure k = K :=
  le_antisymm ((closure_le <| K).2 h₁) h₂
@[to_additive (attr := elab_as_elim)
      "An induction principle for additive closure membership. If `p`
      holds for `0` and all elements of `k`, and is preserved under addition and inverses, then `p`
      holds for all elements of the additive closure of `k`.
      See also `AddSubgroup.closure_induction_left` and `AddSubgroup.closure_induction_left` for
      versions that only require showing `p` is preserved by addition by elements in `k`."]
theorem closure_induction {p : (g : G) → g ∈ closure k → Prop}
    (mem : ∀ x (hx : x ∈ k), p x (subset_closure hx)) (one : p 1 (one_mem _))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (inv : ∀ x hx, p x hx → p x⁻¹ (inv_mem hx)) {x} (hx : x ∈ closure k) : p x hx :=
  let K : Subgroup G :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := fun ⟨_, ha⟩ ⟨_, hb⟩ ↦ ⟨_, mul _ _ _ _ ha hb⟩
      one_mem' := ⟨_, one⟩
      inv_mem' := fun ⟨_, hb⟩ ↦ ⟨_, inv _ _ hb⟩ }
  closure_le (K := K) |>.mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id
@[deprecated closure_induction (since := "2024-10-10")]
alias closure_induction' := closure_induction
@[to_additive (attr := elab_as_elim)
      "An induction principle for additive closure membership, for
      predicates with two arguments."]
theorem closure_induction₂ {p : (x y : G) → x ∈ closure k → y ∈ closure k → Prop}
    (mem : ∀ (x) (y) (hx : x ∈ k) (hy : y ∈ k), p x y (subset_closure hx) (subset_closure hy))
    (one_left : ∀ x hx, p 1 x (one_mem _) hx) (one_right : ∀ x hx, p x 1 hx (one_mem _))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ y z x hy hz hx, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    (inv_left : ∀ x y hx hy, p x y hx hy → p x⁻¹ y (inv_mem hx) hy)
    (inv_right : ∀ x y hx hy, p x y hx hy → p x y⁻¹ hx (inv_mem hy))
    {x y : G} (hx : x ∈ closure k) (hy : y ∈ closure k) : p x y hx hy := by
  induction hy using closure_induction with
  | mem z hz => induction hx using closure_induction with
    | mem _ h => exact mem _ _ h hz
    | one => exact one_left _ (subset_closure hz)
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | inv _ _ h => exact inv_left _ _ _ _ h
  | one => exact one_right x hx
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ hx h₁ h₂
  | inv _ _ h => exact inv_right _ _ _ _ h
@[to_additive (attr := simp)]
theorem closure_closure_coe_preimage {k : Set G} : closure (((↑) : closure k → G) ⁻¹' k) = ⊤ :=
  eq_top_iff.2 fun x _ ↦ Subtype.recOn x fun _ hx' ↦
    closure_induction (fun _ h ↦ subset_closure h) (one_mem _) (fun _ _ _ _ ↦ mul_mem)
      (fun _ _ ↦ inv_mem) hx'
variable (G)
@[to_additive "`closure` forms a Galois insertion with the coercion to set."]
protected def gi : GaloisInsertion (@closure G _) (↑) where
  choice s _ := closure s
  gc s t := @closure_le _ _ t s
  le_l_u _s := subset_closure
  choice_eq _s _h := rfl
variable {G}
@[to_additive (attr := gcongr)
      "Additive subgroup closure of a set is monotone in its argument: if `h ⊆ k`,
      then `closure h ≤ closure k`"]
theorem closure_mono ⦃h k : Set G⦄ (h' : h ⊆ k) : closure h ≤ closure k :=
  (Subgroup.gi G).gc.monotone_l h'
@[to_additive (attr := simp) "Additive closure of an additive subgroup `K` equals `K`"]
theorem closure_eq : closure (K : Set G) = K :=
  (Subgroup.gi G).l_u_eq K
@[to_additive (attr := simp)]
theorem closure_empty : closure (∅ : Set G) = ⊥ :=
  (Subgroup.gi G).gc.l_bot
@[to_additive (attr := simp)]
theorem closure_univ : closure (univ : Set G) = ⊤ :=
  @coe_top G _ ▸ closure_eq ⊤
@[to_additive]
theorem closure_union (s t : Set G) : closure (s ∪ t) = closure s ⊔ closure t :=
  (Subgroup.gi G).gc.l_sup
@[to_additive]
theorem sup_eq_closure (H H' : Subgroup G) : H ⊔ H' = closure ((H : Set G) ∪ (H' : Set G)) := by
  simp_rw [closure_union, closure_eq]
@[to_additive]
theorem closure_iUnion {ι} (s : ι → Set G) : closure (⋃ i, s i) = ⨆ i, closure (s i) :=
  (Subgroup.gi G).gc.l_iSup
@[to_additive (attr := simp)]
theorem closure_eq_bot_iff : closure k = ⊥ ↔ k ⊆ {1} := le_bot_iff.symm.trans <| closure_le _
@[to_additive]
theorem iSup_eq_closure {ι : Sort*} (p : ι → Subgroup G) :
    ⨆ i, p i = closure (⋃ i, (p i : Set G)) := by simp_rw [closure_iUnion, closure_eq]
@[to_additive
      "The `AddSubgroup` generated by an element of an `AddGroup` equals the set of
      natural number multiples of the element."]
theorem mem_closure_singleton {x y : G} : y ∈ closure ({x} : Set G) ↔ ∃ n : ℤ, x ^ n = y := by
  refine
    ⟨fun hy => closure_induction ?_ ?_ ?_ ?_ hy, fun ⟨n, hn⟩ =>
      hn ▸ zpow_mem (subset_closure <| mem_singleton x) n⟩
  · intro y hy
    rw [eq_of_mem_singleton hy]
    exact ⟨1, zpow_one x⟩
  · exact ⟨0, zpow_zero x⟩
  · rintro _ _ _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    exact ⟨n + m, zpow_add x n m⟩
  rintro _ _ ⟨n, rfl⟩
  exact ⟨-n, zpow_neg x n⟩
@[to_additive]
theorem closure_singleton_one : closure ({1} : Set G) = ⊥ := by
  simp [eq_bot_iff_forall, mem_closure_singleton]
@[to_additive (attr := simp)]
lemma mem_closure_singleton_self (x : G) : x ∈ closure ({x} : Set G) := by
  simpa [-subset_closure] using subset_closure (k := {x})
@[to_additive]
theorem le_closure_toSubmonoid (S : Set G) : Submonoid.closure S ≤ (closure S).toSubmonoid :=
  Submonoid.closure_le.2 subset_closure
@[to_additive]
theorem closure_eq_top_of_mclosure_eq_top {S : Set G} (h : Submonoid.closure S = ⊤) :
    closure S = ⊤ :=
  (eq_top_iff' _).2 fun _ => le_closure_toSubmonoid _ <| h.symm ▸ trivial
@[to_additive]
theorem mem_iSup_of_directed {ι} [hι : Nonempty ι] {K : ι → Subgroup G} (hK : Directed (· ≤ ·) K)
    {x : G} : x ∈ (iSup K : Subgroup G) ↔ ∃ i, x ∈ K i := by
  refine ⟨?_, fun ⟨i, hi⟩ ↦ le_iSup K i hi⟩
  suffices x ∈ closure (⋃ i, (K i : Set G)) → ∃ i, x ∈ K i by
    simpa only [closure_iUnion, closure_eq (K _)] using this
  refine fun hx ↦ closure_induction (fun _ ↦ mem_iUnion.1) ?_ ?_ ?_ hx
  · exact hι.elim fun i ↦ ⟨i, (K i).one_mem⟩
  · rintro x y _ _ ⟨i, hi⟩ ⟨j, hj⟩
    rcases hK i j with ⟨k, hki, hkj⟩
    exact ⟨k, mul_mem (hki hi) (hkj hj)⟩
  · rintro _ _ ⟨i, hi⟩
    exact ⟨i, inv_mem hi⟩
@[to_additive]
theorem coe_iSup_of_directed {ι} [Nonempty ι] {S : ι → Subgroup G} (hS : Directed (· ≤ ·) S) :
    ((⨆ i, S i : Subgroup G) : Set G) = ⋃ i, S i :=
  Set.ext fun x ↦ by simp [mem_iSup_of_directed hS]
@[to_additive]
theorem mem_sSup_of_directedOn {K : Set (Subgroup G)} (Kne : K.Nonempty) (hK : DirectedOn (· ≤ ·) K)
    {x : G} : x ∈ sSup K ↔ ∃ s ∈ K, x ∈ s := by
  haveI : Nonempty K := Kne.to_subtype
  simp only [sSup_eq_iSup', mem_iSup_of_directed hK.directed_val, SetCoe.exists, Subtype.coe_mk,
    exists_prop]
variable {C : Type*} [CommGroup C] {s t : Subgroup C} {x : C}
@[to_additive]
theorem mem_sup : x ∈ s ⊔ t ↔ ∃ y ∈ s, ∃ z ∈ t, y * z = x :=
  ⟨fun h => by
    rw [sup_eq_closure] at h
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ h
    · rintro y (h | h)
      · exact ⟨y, h, 1, t.one_mem, by simp⟩
      · exact ⟨1, s.one_mem, y, h, by simp⟩
    · exact ⟨1, s.one_mem, 1, ⟨t.one_mem, mul_one 1⟩⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨_, mul_mem hy₁ hy₂, _, mul_mem hz₁ hz₂, by simp [mul_assoc, mul_left_comm]⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨_, inv_mem hy, _, inv_mem hz, mul_comm z y ▸ (mul_inv_rev z y).symm⟩, by
    rintro ⟨y, hy, z, hz, rfl⟩; exact mul_mem_sup hy hz⟩
@[to_additive]
theorem mem_sup' : x ∈ s ⊔ t ↔ ∃ (y : s) (z : t), (y : C) * z = x :=
  mem_sup.trans <| by simp only [SetLike.exists, coe_mk, exists_prop]
@[to_additive]
theorem mem_closure_pair {x y z : C} :
    z ∈ closure ({x, y} : Set C) ↔ ∃ m n : ℤ, x ^ m * y ^ n = z := by
  rw [← Set.singleton_union, Subgroup.closure_union, mem_sup]
  simp_rw [mem_closure_singleton, exists_exists_eq_and]
@[to_additive]
theorem disjoint_def {H₁ H₂ : Subgroup G} : Disjoint H₁ H₂ ↔ ∀ {x : G}, x ∈ H₁ → x ∈ H₂ → x = 1 :=
  disjoint_iff_inf_le.trans <| by simp only [Disjoint, SetLike.le_def, mem_inf, mem_bot, and_imp]
@[to_additive]
theorem disjoint_def' {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x = y → x = 1 :=
  disjoint_def.trans ⟨fun h _x _y hx hy hxy ↦ h hx <| hxy.symm ▸ hy, fun h _x hx hx' ↦ h hx hx' rfl⟩
@[to_additive]
theorem disjoint_iff_mul_eq_one {H₁ H₂ : Subgroup G} :
    Disjoint H₁ H₂ ↔ ∀ {x y : G}, x ∈ H₁ → y ∈ H₂ → x * y = 1 → x = 1 ∧ y = 1 :=
  disjoint_def'.trans
    ⟨fun h x y hx hy hxy =>
      let hx1 : x = 1 := h hx (H₂.inv_mem hy) (eq_inv_iff_mul_eq_one.mpr hxy)
      ⟨hx1, by simpa [hx1] using hxy⟩,
      fun h _ _ hx hy hxy => (h hx (H₂.inv_mem hy) (mul_inv_eq_one.mpr hxy)).1⟩
@[to_additive]
theorem mul_injective_of_disjoint {H₁ H₂ : Subgroup G} (h : Disjoint H₁ H₂) :
    Function.Injective (fun g => g.1 * g.2 : H₁ × H₂ → G) := by
  intro x y hxy
  rw [← inv_mul_eq_iff_eq_mul, ← mul_assoc, ← mul_inv_eq_one, mul_assoc] at hxy
  replace hxy := disjoint_iff_mul_eq_one.mp h (y.1⁻¹ * x.1).prop (x.2 * y.2⁻¹).prop hxy
  rwa [coe_mul, coe_mul, coe_inv, coe_inv, inv_mul_eq_one, mul_inv_eq_one, ← Subtype.ext_iff, ←
    Subtype.ext_iff, eq_comm, ← Prod.ext_iff] at hxy
end Subgroup