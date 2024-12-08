import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Rank
universe u
variable {α : Type u} {r : α → α → Prop}
namespace IsWellFounded
variable {α : Type u} (r : α → α → Prop) [IsWellFounded α r]
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (rank r a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h
instance wellOrderExtension.isWellFounded_lt : IsWellFounded α (wellOrderExtension r).lt :=
  ⟨InvImage.wf (fun a : α => (rank r a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩
instance wellOrderExtension.isWellOrder_lt : IsWellOrder α (wellOrderExtension r).lt where
theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨(wellOrderExtension r).lt, fun _ _ h => Prod.Lex.left _ _ (rank_lt_of_rel h), ⟨⟩⟩
end IsWellFounded
namespace WellFounded
variable (hwf : WellFounded r)
set_option linter.deprecated false in
@[deprecated IsWellFounded.wellOrderExtension (since := "2024-09-07")]
noncomputable def wellOrderExtension : LinearOrder α :=
  @LinearOrder.lift' α (Ordinal ×ₗ Cardinal) _ (fun a : α => (hwf.rank a, embeddingToCardinal a))
    fun _ _ h => embeddingToCardinal.injective <| congr_arg Prod.snd h
set_option linter.deprecated false in
@[deprecated IsWellFounded.wellOrderExtension.isWellFounded_lt (since := "2024-09-07")]
instance wellOrderExtension.isWellFounded_lt : IsWellFounded α hwf.wellOrderExtension.lt :=
  ⟨InvImage.wf (fun a : α => (hwf.rank a, embeddingToCardinal a)) <|
    Ordinal.lt_wf.prod_lex Cardinal.lt_wf⟩
include hwf in
set_option linter.deprecated false in
@[deprecated IsWellFounded.exists_well_order_ge (since := "2024-09-07")]
theorem exists_well_order_ge : ∃ s, r ≤ s ∧ IsWellOrder α s :=
  ⟨hwf.wellOrderExtension.lt, fun _ _ h => Prod.Lex.left _ _ (hwf.rank_lt_of_rel h), ⟨⟩⟩
end WellFounded
def WellOrderExtension (α : Type*) : Type _ := α
instance [Inhabited α] : Inhabited (WellOrderExtension α) := ‹_›
def toWellOrderExtension : α ≃ WellOrderExtension α :=
  Equiv.refl _
noncomputable instance [LT α] [h : WellFoundedLT α] : LinearOrder (WellOrderExtension α) :=
  h.wellOrderExtension
instance WellOrderExtension.wellFoundedLT [LT α] [WellFoundedLT α] :
    WellFoundedLT (WellOrderExtension α) :=
  IsWellFounded.wellOrderExtension.isWellFounded_lt (α := α) (· < ·)
theorem toWellOrderExtension_strictMono [Preorder α] [WellFoundedLT α] :
    StrictMono (toWellOrderExtension : α → WellOrderExtension α) := fun _ _ h =>
  Prod.Lex.left _ _ <| IsWellFounded.rank_lt_of_rel h