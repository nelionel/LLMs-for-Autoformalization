import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Logic.Equiv.Defs
section Fintype
variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)
def Function.Embedding.toEquivRange : α ≃ Set.range f :=
  ⟨fun a => ⟨f a, Set.mem_range_self a⟩, f.invOfMemRange, fun _ => by simp, fun _ => by simp⟩
@[simp]
theorem Function.Embedding.toEquivRange_apply (a : α) :
    f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl
@[simp]
theorem Function.Embedding.toEquivRange_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by simp [Equiv.symm_apply_eq]
theorem Function.Embedding.toEquivRange_eq_ofInjective :
    f.toEquivRange = Equiv.ofInjective f f.injective := by
  ext
  simp
def Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β :=
  e.extendDomain f.toEquivRange
@[simp]
theorem Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) :
    e.viaFintypeEmbedding f (f a) = f (e a) := by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a
theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b ∈ Set.range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype]
  congr
theorem Equiv.Perm.viaFintypeEmbedding_apply_not_mem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]
@[simp]
theorem Equiv.Perm.viaFintypeEmbedding_sign [DecidableEq α] [Fintype β] :
    Equiv.Perm.sign (e.viaFintypeEmbedding f) = Equiv.Perm.sign e := by
  simp [Equiv.Perm.viaFintypeEmbedding]
end Fintype
namespace Equiv
variable {α β : Type*} [Finite α]
noncomputable def toCompl {p q : α → Prop} (e : { x // p x } ≃ { x // q x }) :
    { x // ¬p x } ≃ { x // ¬q x } := by
  apply Classical.choice
  cases nonempty_fintype α
  classical
  exact Fintype.card_eq.mp <| Fintype.card_compl_eq_card_compl _ _ <| Fintype.card_congr e
variable {p q : α → Prop} [DecidablePred p] [DecidablePred q]
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl
theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ := by
  dsimp only [extendSubtype]
  simp only [subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sumCompl_apply_symm_of_pos _ _ hx, Sum.map_inl, sumCompl_apply_inl]
theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) := by
  convert (e ⟨x, hx⟩).2
  rw [e.extendSubtype_apply_of_mem _ hx]
theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  dsimp only [extendSubtype]
  simp only [subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply]
  rw [sumCompl_apply_symm_of_neg _ _ hx, Sum.map_inr, sumCompl_apply_inr]
theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) := by
  convert (e.toCompl ⟨x, hx⟩).2
  rw [e.extendSubtype_apply_of_not_mem _ hx]
end Equiv