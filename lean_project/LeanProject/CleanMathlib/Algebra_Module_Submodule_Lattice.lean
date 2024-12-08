import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.PUnitInstances.Module
import Mathlib.Data.Set.Subsingleton
import Mathlib.Order.ConditionallyCompleteLattice.Basic
universe v
variable {R S M : Type*}
section AddCommMonoid
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
variable [SMul S R] [IsScalarTower S R M]
variable {p q : Submodule R M}
namespace Submodule
instance : Bot (Submodule R M) :=
  ⟨{ (⊥ : AddSubmonoid M) with
      carrier := {0}
      smul_mem' := by simp }⟩
instance inhabited' : Inhabited (Submodule R M) :=
  ⟨⊥⟩
@[simp]
theorem bot_coe : ((⊥ : Submodule R M) : Set M) = {0} :=
  rfl
@[simp]
theorem bot_toAddSubmonoid : (⊥ : Submodule R M).toAddSubmonoid = ⊥ :=
  rfl
@[simp]
lemma bot_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊥ : Submodule R M).toAddSubgroup = ⊥ := rfl
variable (R) in
@[simp]
theorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=
  Set.mem_singleton_iff
instance uniqueBot : Unique (⊥ : Submodule R M) :=
  ⟨inferInstance, fun x ↦ Subtype.ext <| (mem_bot R).1 x.mem⟩
instance : OrderBot (Submodule R M) where
  bot := ⊥
  bot_le p x := by simp +contextual [zero_mem]
protected theorem eq_bot_iff (p : Submodule R M) : p = ⊥ ↔ ∀ x ∈ p, x = (0 : M) :=
  ⟨fun h ↦ h.symm ▸ fun _ hx ↦ (mem_bot R).mp hx,
    fun h ↦ eq_bot_iff.mpr fun x hx ↦ (mem_bot R).mpr (h x hx)⟩
@[ext high]
protected theorem bot_ext (x y : (⊥ : Submodule R M)) : x = y := by
  rcases x with ⟨x, xm⟩; rcases y with ⟨y, ym⟩; congr
  rw [(Submodule.eq_bot_iff _).mp rfl x xm]
  rw [(Submodule.eq_bot_iff _).mp rfl y ym]
protected theorem ne_bot_iff (p : Submodule R M) : p ≠ ⊥ ↔ ∃ x ∈ p, x ≠ (0 : M) := by
  simp only [ne_eq, p.eq_bot_iff, not_forall, exists_prop]
theorem nonzero_mem_of_bot_lt {p : Submodule R M} (bot_lt : ⊥ < p) : ∃ a : p, a ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp bot_lt.ne'
  ⟨⟨b, hb₁⟩, hb₂ ∘ congr_arg Subtype.val⟩
theorem exists_mem_ne_zero_of_ne_bot {p : Submodule R M} (h : p ≠ ⊥) : ∃ b : M, b ∈ p ∧ b ≠ 0 :=
  let ⟨b, hb₁, hb₂⟩ := p.ne_bot_iff.mp h
  ⟨b, hb₁, hb₂⟩
@[simps]
def botEquivPUnit : (⊥ : Submodule R M) ≃ₗ[R] PUnit.{v+1} where
  toFun _ := PUnit.unit
  invFun _ := 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := rfl
theorem subsingleton_iff_eq_bot : Subsingleton p ↔ p = ⊥ := by
  rw [subsingleton_iff, Submodule.eq_bot_iff]
  refine ⟨fun h x hx ↦ by simpa using h ⟨x, hx⟩ ⟨0, p.zero_mem⟩,
    fun h ⟨x, hx⟩ ⟨y, hy⟩ ↦ by simp [h x hx, h y hy]⟩
theorem eq_bot_of_subsingleton [Subsingleton p] : p = ⊥ :=
  subsingleton_iff_eq_bot.mp inferInstance
theorem nontrivial_iff_ne_bot : Nontrivial p ↔ p ≠ ⊥ := by
  rw [iff_not_comm, not_nontrivial_iff_subsingleton, subsingleton_iff_eq_bot]
instance : Top (Submodule R M) :=
  ⟨{ (⊤ : AddSubmonoid M) with
      carrier := Set.univ
      smul_mem' := fun _ _ _ ↦ trivial }⟩
@[simp]
theorem top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ :=
  rfl
@[simp]
theorem top_toAddSubmonoid : (⊤ : Submodule R M).toAddSubmonoid = ⊤ :=
  rfl
@[simp]
lemma top_toAddSubgroup {R M} [Ring R] [AddCommGroup M] [Module R M] :
    (⊤ : Submodule R M).toAddSubgroup = ⊤ := rfl
@[simp]
theorem mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=
  trivial
instance : OrderTop (Submodule R M) where
  top := ⊤
  le_top _ _ _ := trivial
theorem eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ ∀ x, x ∈ p :=
  eq_top_iff.trans ⟨fun h _ ↦ h trivial, fun h x _ ↦ h x⟩
@[simps]
def topEquiv : (⊤ : Submodule R M) ≃ₗ[R] M where
  toFun x := x
  invFun x := ⟨x, mem_top⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
instance : InfSet (Submodule R M) :=
  ⟨fun S ↦
    { carrier := ⋂ s ∈ S, (s : Set M)
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩
private theorem sInf_le' {S : Set (Submodule R M)} {p} : p ∈ S → sInf S ≤ p :=
  Set.biInter_subset_of_mem
private theorem le_sInf' {S : Set (Submodule R M)} {p} : (∀ q ∈ S, p ≤ q) → p ≤ sInf S :=
  Set.subset_iInter₂
instance : Min (Submodule R M) :=
  ⟨fun p q ↦
    { carrier := p ∩ q
      zero_mem' := by simp [zero_mem]
      add_mem' := by simp +contextual [add_mem]
      smul_mem' := by simp +contextual [smul_mem] }⟩
instance completeLattice : CompleteLattice (Submodule R M) :=
  { (inferInstance : OrderTop (Submodule R M)),
    (inferInstance : OrderBot (Submodule R M)) with
    sup := fun a b ↦ sInf { x | a ≤ x ∧ b ≤ x }
    le_sup_left := fun _ _ ↦ le_sInf' fun _ ⟨h, _⟩ ↦ h
    le_sup_right := fun _ _ ↦ le_sInf' fun _ ⟨_, h⟩ ↦ h
    sup_le := fun _ _ _ h₁ h₂ ↦ sInf_le' ⟨h₁, h₂⟩
    inf := (· ⊓ ·)
    le_inf := fun _ _ _ ↦ Set.subset_inter
    inf_le_left := fun _ _ ↦ Set.inter_subset_left
    inf_le_right := fun _ _ ↦ Set.inter_subset_right
    le_sSup := fun _ _ hs ↦ le_sInf' fun _ hq ↦ by exact hq _ hs
    sSup_le := fun _ _ hs ↦ sInf_le' hs
    le_sInf := fun _ _ ↦ le_sInf'
    sInf_le := fun _ _ ↦ sInf_le' }
@[simp]
theorem inf_coe : ↑(p ⊓ q) = (p ∩ q : Set M) :=
  rfl
@[simp]
theorem mem_inf {p q : Submodule R M} {x : M} : x ∈ p ⊓ q ↔ x ∈ p ∧ x ∈ q :=
  Iff.rfl
@[simp]
theorem sInf_coe (P : Set (Submodule R M)) : (↑(sInf P) : Set M) = ⋂ p ∈ P, ↑p :=
  rfl
@[simp]
theorem finset_inf_coe {ι} (s : Finset ι) (p : ι → Submodule R M) :
    (↑(s.inf p) : Set M) = ⋂ i ∈ s, ↑(p i) := by
  letI := Classical.decEq ι
  refine s.induction_on ?_ fun i s _ ih ↦ ?_
  · simp
  · rw [Finset.inf_insert, inf_coe, ih]
    simp
@[simp]
theorem iInf_coe {ι} (p : ι → Submodule R M) : (↑(⨅ i, p i) : Set M) = ⋂ i, ↑(p i) := by
  rw [iInf, sInf_coe]; simp only [Set.mem_range, Set.iInter_exists, Set.iInter_iInter_eq']
@[simp]
theorem mem_sInf {S : Set (Submodule R M)} {x : M} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p :=
  Set.mem_iInter₂
@[simp]
theorem mem_iInf {ι} (p : ι → Submodule R M) {x} : (x ∈ ⨅ i, p i) ↔ ∀ i, x ∈ p i := by
  rw [← SetLike.mem_coe, iInf_coe, Set.mem_iInter]; rfl
@[simp]
theorem mem_finset_inf {ι} {s : Finset ι} {p : ι → Submodule R M} {x : M} :
    x ∈ s.inf p ↔ ∀ i ∈ s, x ∈ p i := by
  simp only [← SetLike.mem_coe, finset_inf_coe, Set.mem_iInter]
lemma inf_iInf {ι : Type*} [Nonempty ι] {p : ι → Submodule R M} (q : Submodule R M) :
    q ⊓ ⨅ i, p i = ⨅ i, q ⊓ p i :=
  SetLike.coe_injective <| by simpa only [inf_coe, iInf_coe] using Set.inter_iInter _ _
theorem mem_sup_left {S T : Submodule R M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T := by
  have : S ≤ S ⊔ T := le_sup_left
  rw [LE.le] at this
  exact this
theorem mem_sup_right {S T : Submodule R M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T := by
  have : T ≤ S ⊔ T := le_sup_right
  rw [LE.le] at this
  exact this
theorem add_mem_sup {S T : Submodule R M} {s t : M} (hs : s ∈ S) (ht : t ∈ T) : s + t ∈ S ⊔ T :=
  add_mem (mem_sup_left hs) (mem_sup_right ht)
theorem sub_mem_sup {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M']
    {S T : Submodule R' M'} {s t : M'} (hs : s ∈ S) (ht : t ∈ T) : s - t ∈ S ⊔ T := by
  rw [sub_eq_add_neg]
  exact add_mem_sup hs (neg_mem ht)
theorem mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι → Submodule R M} (i : ι) (h : b ∈ p i) :
    b ∈ ⨆ i, p i :=
  (le_iSup p i) h
theorem sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i, f i ∈ p i) : (∑ i, f i) ∈ ⨆ i, p i :=
  sum_mem fun i _ ↦ mem_iSup_of_mem i (h i)
theorem sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι → M} {p : ι → Submodule R M}
    (h : ∀ i ∈ s, f i ∈ p i) : (∑ i ∈ s, f i) ∈ ⨆ i ∈ s, p i :=
  sum_mem fun i hi ↦ mem_iSup_of_mem i <| mem_iSup_of_mem hi (h i hi)
theorem mem_sSup_of_mem {S : Set (Submodule R M)} {s : Submodule R M} (hs : s ∈ S) :
    ∀ {x : M}, x ∈ s → x ∈ sSup S := by
  have := le_sSup hs
  rw [LE.le] at this
  exact this
@[simp]
theorem toAddSubmonoid_sSup (s : Set (Submodule R M)) :
    (sSup s).toAddSubmonoid = sSup (toAddSubmonoid '' s) := by
  let p : Submodule R M :=
    { toAddSubmonoid := sSup (toAddSubmonoid '' s)
      smul_mem' := fun t {m} h ↦ by
        simp_rw [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, sSup_eq_iSup'] at h ⊢
        refine AddSubmonoid.iSup_induction' _
          (C := fun x _ ↦ t • x ∈ ⨆ p : toAddSubmonoid '' s, (p : AddSubmonoid M)) ?_ ?_
          (fun x y _ _ ↦ ?_) h
        · rintro ⟨-, ⟨p : Submodule R M, hp : p ∈ s, rfl⟩⟩ x (hx : x ∈ p)
          suffices p.toAddSubmonoid ≤ ⨆ q : toAddSubmonoid '' s, (q : AddSubmonoid M) by
            exact this (smul_mem p t hx)
          apply le_sSup
          rw [Subtype.range_coe_subtype]
          exact ⟨p, hp, rfl⟩
        · simpa only [smul_zero] using zero_mem _
        · simp_rw [smul_add]; exact add_mem }
  refine le_antisymm (?_ : sSup s ≤ p) ?_
  · exact sSup_le fun q hq ↦ le_sSup <| Set.mem_image_of_mem toAddSubmonoid hq
  · exact sSup_le fun _ ⟨q, hq, hq'⟩ ↦ hq'.symm ▸ le_sSup hq
variable (R)
@[simp]
theorem subsingleton_iff : Subsingleton (Submodule R M) ↔ Subsingleton M :=
  have h : Subsingleton (Submodule R M) ↔ Subsingleton (AddSubmonoid M) := by
    rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← toAddSubmonoid_eq,
      bot_toAddSubmonoid, top_toAddSubmonoid]
  h.trans AddSubmonoid.subsingleton_iff
@[simp]
theorem nontrivial_iff : Nontrivial (Submodule R M) ↔ Nontrivial M :=
  not_iff_not.mp
    ((not_nontrivial_iff_subsingleton.trans <| subsingleton_iff R).trans
      not_nontrivial_iff_subsingleton.symm)
variable {R}
instance [Subsingleton M] : Unique (Submodule R M) :=
  ⟨⟨⊥⟩, fun a => @Subsingleton.elim _ ((subsingleton_iff R).mpr ‹_›) a _⟩
instance unique' [Subsingleton R] : Unique (Submodule R M) := by
  haveI := Module.subsingleton R M; infer_instance
instance [Nontrivial M] : Nontrivial (Submodule R M) :=
  (nontrivial_iff R).mpr ‹_›
theorem disjoint_def {p p' : Submodule R M} : Disjoint p p' ↔ ∀ x ∈ p, x ∈ p' → x = (0 : M) :=
  disjoint_iff_inf_le.trans <| show (∀ x, x ∈ p ∧ x ∈ p' → x ∈ ({0} : Set M)) ↔ _ by simp
theorem disjoint_def' {p p' : Submodule R M} :
    Disjoint p p' ↔ ∀ x ∈ p, ∀ y ∈ p', x = y → x = (0 : M) :=
  disjoint_def.trans
    ⟨fun h x hx _ hy hxy ↦ h x hx <| hxy.symm ▸ hy, fun h x hx hx' ↦ h _ hx x hx' rfl⟩
theorem eq_zero_of_coe_mem_of_disjoint (hpq : Disjoint p q) {a : p} (ha : (a : M) ∈ q) : a = 0 :=
  mod_cast disjoint_def.mp hpq a (coe_mem a) ha
theorem mem_right_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p} :
    (x : M) ∈ p' ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x x.2 hx, fun h => h.symm ▸ p'.zero_mem⟩
theorem mem_left_iff_eq_zero_of_disjoint {p p' : Submodule R M} (h : Disjoint p p') {x : p'} :
    (x : M) ∈ p ↔ x = 0 :=
  ⟨fun hx => coe_eq_zero.1 <| disjoint_def.1 h x hx x.2, fun h => h.symm ▸ p.zero_mem⟩
end Submodule
section NatSubmodule
def AddSubmonoid.toNatSubmodule : AddSubmonoid M ≃o Submodule ℕ M where
  toFun S := { S with smul_mem' := fun r s hs ↦ show r • s ∈ S from nsmul_mem hs _ }
  invFun := Submodule.toAddSubmonoid
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
@[simp]
theorem AddSubmonoid.toNatSubmodule_symm :
    ⇑(AddSubmonoid.toNatSubmodule.symm : _ ≃o AddSubmonoid M) = Submodule.toAddSubmonoid :=
  rfl
@[simp]
theorem AddSubmonoid.coe_toNatSubmodule (S : AddSubmonoid M) :
    (AddSubmonoid.toNatSubmodule S : Set M) = S :=
  rfl
@[simp]
theorem AddSubmonoid.toNatSubmodule_toAddSubmonoid (S : AddSubmonoid M) :
    S.toNatSubmodule.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.symm_apply_apply S
@[simp]
theorem Submodule.toAddSubmonoid_toNatSubmodule (S : Submodule ℕ M) :
    AddSubmonoid.toNatSubmodule S.toAddSubmonoid = S :=
  AddSubmonoid.toNatSubmodule.apply_symm_apply S
end NatSubmodule
end AddCommMonoid
section IntSubmodule
variable [AddCommGroup M]
def AddSubgroup.toIntSubmodule : AddSubgroup M ≃o Submodule ℤ M where
  toFun S := { S with smul_mem' := fun _ _ hs ↦ S.zsmul_mem hs _ }
  invFun := Submodule.toAddSubgroup
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
@[simp]
theorem AddSubgroup.toIntSubmodule_symm :
    ⇑(AddSubgroup.toIntSubmodule.symm : _ ≃o AddSubgroup M) = Submodule.toAddSubgroup :=
  rfl
@[simp]
theorem AddSubgroup.coe_toIntSubmodule (S : AddSubgroup M) :
    (AddSubgroup.toIntSubmodule S : Set M) = S :=
  rfl
@[simp]
theorem AddSubgroup.toIntSubmodule_toAddSubgroup (S : AddSubgroup M) :
    S.toIntSubmodule.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.symm_apply_apply S
@[simp]
theorem Submodule.toAddSubgroup_toIntSubmodule (S : Submodule ℤ M) :
    AddSubgroup.toIntSubmodule S.toAddSubgroup = S :=
  AddSubgroup.toIntSubmodule.apply_symm_apply S
end IntSubmodule