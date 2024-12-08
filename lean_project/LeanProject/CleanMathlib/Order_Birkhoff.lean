import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Irreducible
import Mathlib.Order.UpperLower.Basic
open Finset Function OrderDual UpperSet LowerSet
variable {α : Type*}
section PartialOrder
variable [PartialOrder α]
namespace UpperSet
variable {s : UpperSet α}
@[simp] lemma infIrred_Ici (a : α) : InfIrred (Ici a) := by
  refine ⟨fun h ↦ Ici_ne_top h.eq_top, fun s t hst ↦ ?_⟩
  have := mem_Ici_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_left) fun ha ↦
      le_antisymm (le_Ici.2 ha) <| hst.ge.trans inf_le_right
variable [Finite α]
@[simp] lemma infIrred_iff_of_finite : InfIrred s ↔ ∃ a, Ici a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_minimal_wrt id _ (coe_nonempty.2 hs.ne_top)
    exact ⟨a, (hs.2 <| erase_inf_Ici ha <| by simpa [eq_comm] using has).resolve_left
      (lt_erase.2 ha).ne'⟩
  · rintro ⟨a, rfl⟩
    exact infIrred_Ici _
end UpperSet
namespace LowerSet
variable {s : LowerSet α}
@[simp] lemma supIrred_Iic (a : α) : SupIrred (Iic a) := by
  refine ⟨fun h ↦ Iic_ne_bot h.eq_bot, fun s t hst ↦ ?_⟩
  have := mem_Iic_iff.2 (le_refl a)
  rw [← hst] at this
  exact this.imp (fun ha ↦ (le_sup_left.trans_eq hst).antisymm <| Iic_le.2 ha) fun ha ↦
    (le_sup_right.trans_eq hst).antisymm <| Iic_le.2 ha
variable [Finite α]
@[simp] lemma supIrred_iff_of_finite : SupIrred s ↔ ∃ a, Iic a = s := by
  refine ⟨fun hs ↦ ?_, ?_⟩
  · obtain ⟨a, ha, has⟩ := (s : Set α).toFinite.exists_maximal_wrt id _ (coe_nonempty.2 hs.ne_bot)
    exact ⟨a, (hs.2 <| erase_sup_Iic ha <| by simpa [eq_comm] using has).resolve_left
      (erase_lt.2 ha).ne⟩
  · rintro ⟨a, rfl⟩
    exact supIrred_Iic _
end LowerSet
namespace OrderEmbedding
def supIrredLowerSet : α ↪o {s : LowerSet α // SupIrred s} where
  toFun a := ⟨Iic a, supIrred_Iic _⟩
  inj' _ := by simp
  map_rel_iff' := by simp
def infIrredUpperSet : α ↪o {s : UpperSet α // InfIrred s} where
  toFun a := ⟨Ici a, infIrred_Ici _⟩
  inj' _ := by simp
  map_rel_iff' := by simp
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl
variable [Finite α]
lemma supIrredLowerSet_surjective : Surjective (supIrredLowerSet (α := α)) := by
  aesop (add simp Surjective)
lemma infIrredUpperSet_surjective : Surjective (infIrredUpperSet (α := α)) := by
  aesop (add simp Surjective)
end OrderEmbedding
namespace OrderIso
variable [Finite α]
noncomputable def supIrredLowerSet : α ≃o {s : LowerSet α // SupIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.supIrredLowerSet_surjective
noncomputable def infIrredUpperSet : α ≃o {s : UpperSet α // InfIrred s} :=
  RelIso.ofSurjective _ OrderEmbedding.infIrredUpperSet_surjective
@[simp] lemma supIrredLowerSet_apply (a : α) : supIrredLowerSet a = ⟨Iic a, supIrred_Iic _⟩ := rfl
@[simp] lemma infIrredUpperSet_apply (a : α) : infIrredUpperSet a = ⟨Ici a, infIrred_Ici _⟩ := rfl
end OrderIso
end PartialOrder
namespace OrderIso
section SemilatticeSup
variable [SemilatticeSup α] [OrderBot α] [Finite α]
@[simp] lemma supIrredLowerSet_symm_apply (s : {s : LowerSet α // SupIrred s}) [Fintype s] :
    supIrredLowerSet.symm s = (s.1 : Set α).toFinset.sup id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := supIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]
end SemilatticeSup
section SemilatticeInf
variable [SemilatticeInf α] [OrderTop α] [Finite α]
@[simp] lemma infIrredUpperSet_symm_apply (s : {s : UpperSet α // InfIrred s}) [Fintype s] :
    infIrredUpperSet.symm s = (s.1 : Set α).toFinset.inf id := by
  classical
  obtain ⟨s, hs⟩ := s
  obtain ⟨a, rfl⟩ := infIrred_iff_of_finite.1 hs
  cases nonempty_fintype α
  have : LocallyFiniteOrder α := Fintype.toLocallyFiniteOrder
  simp [symm_apply_eq]
end SemilatticeInf
end OrderIso
section DistribLattice
variable [DistribLattice α] [Fintype α] [@DecidablePred α SupIrred]
open Classical in
noncomputable def OrderIso.lowerSetSupIrred [OrderBot α] : α ≃o LowerSet {a : α // SupIrred a} :=
  Equiv.toOrderIso
    { toFun := fun a ↦ ⟨{b | ↑b ≤ a}, fun _ _ hcb hba ↦ hba.trans' hcb⟩
      invFun := fun s ↦ (s : Set {a : α // SupIrred a}).toFinset.sup (↑)
      left_inv := fun a ↦ by
        refine le_antisymm (Finset.sup_le fun b ↦ Set.mem_toFinset.1) ?_
        obtain ⟨s, rfl, hs⟩ := exists_supIrred_decomposition a
        exact Finset.sup_le fun i hi ↦
          le_sup_of_le (b := ⟨i, hs hi⟩) (Set.mem_toFinset.2 <| le_sup (f := id) hi) le_rfl
      right_inv := fun s ↦ by
        ext a
        dsimp
        refine ⟨fun ha ↦ ?_, fun ha ↦ ?_⟩
        · obtain ⟨i, hi, ha⟩ := a.2.supPrime.le_finset_sup.1 ha
          exact s.lower ha (Set.mem_toFinset.1 hi)
        · dsimp
          exact le_sup (Set.mem_toFinset.2 ha) }
    (fun _ _ hbc _ ↦ le_trans' hbc) fun _ _ hst ↦ Finset.sup_mono <| Set.toFinset_mono hst
namespace OrderEmbedding
noncomputable def birkhoffSet : α ↪o Set {a : α // SupIrred a} := by
  by_cases h : IsEmpty α
  · exact OrderEmbedding.ofIsEmpty
  rw [not_isEmpty_iff] at h
  have := Fintype.toOrderBot α
  exact OrderIso.lowerSetSupIrred.toOrderEmbedding.trans ⟨⟨_, SetLike.coe_injective⟩, Iff.rfl⟩
noncomputable def birkhoffFinset : α ↪o Finset {a : α // SupIrred a} := by
  exact birkhoffSet.trans Fintype.finsetOrderIsoSet.symm.toOrderEmbedding
@[simp] lemma coe_birkhoffFinset (a : α) : birkhoffFinset a = birkhoffSet a := by
  classical
  simp [birkhoffFinset]
  rw [OrderIso.coe_toOrderEmbedding, Fintype.coe_finsetOrderIsoSet_symm]
  simp
@[simp] lemma birkhoffSet_sup (a b : α) : birkhoffSet (a ⊔ b) = birkhoffSet a ∪ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
@[simp] lemma birkhoffSet_inf (a b : α) : birkhoffSet (a ⊓ b) = birkhoffSet a ∩ birkhoffSet b := by
  unfold OrderEmbedding.birkhoffSet; split <;> simp [eq_iff_true_of_subsingleton]
@[simp] lemma birkhoffSet_apply [OrderBot α] (a : α) :
    birkhoffSet a = OrderIso.lowerSetSupIrred a := by
  simp [birkhoffSet]; have : Subsingleton (OrderBot α) := inferInstance; convert rfl
variable [DecidableEq α]
@[simp] lemma birkhoffFinset_sup (a b : α) :
    birkhoffFinset (a ⊔ b) = birkhoffFinset a ∪ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_sup, OrderIso.coe_toOrderEmbedding]
  simp
@[simp] lemma birkhoffFinset_inf (a b : α) :
    birkhoffFinset (a ⊓ b) = birkhoffFinset a ∩ birkhoffFinset b := by
  classical
  dsimp [OrderEmbedding.birkhoffFinset]
  rw [birkhoffSet_inf, OrderIso.coe_toOrderEmbedding]
  simp
end OrderEmbedding
namespace LatticeHom
noncomputable def birkhoffSet : LatticeHom α (Set {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffSet
  map_sup' := OrderEmbedding.birkhoffSet_sup
  map_inf' := OrderEmbedding.birkhoffSet_inf
open Classical in
noncomputable def birkhoffFinset : LatticeHom α (Finset {a : α // SupIrred a}) where
  toFun := OrderEmbedding.birkhoffFinset
  map_sup' := OrderEmbedding.birkhoffFinset_sup
  map_inf' := OrderEmbedding.birkhoffFinset_inf
lemma birkhoffFinset_injective : Injective (birkhoffFinset (α := α)) :=
  OrderEmbedding.birkhoffFinset.injective
end LatticeHom
lemma exists_birkhoff_representation.{u} (α : Type u) [Finite α] [DistribLattice α] :
    ∃ (β : Type u) (_ : DecidableEq β) (_ : Fintype β) (f : LatticeHom α (Finset β)),
      Injective f := by
  classical
  cases nonempty_fintype α
  exact ⟨{a : α // SupIrred a}, _, inferInstance, _, LatticeHom.birkhoffFinset_injective⟩
end DistribLattice