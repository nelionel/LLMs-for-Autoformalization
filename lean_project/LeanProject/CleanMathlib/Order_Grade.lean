import Mathlib.Data.Int.SuccPred
import Mathlib.Order.Fin.Basic
open Nat OrderDual
variable {𝕆 ℙ α β : Type*}
class GradeOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] where
  protected grade : α → 𝕆
  grade_strictMono : StrictMono grade
  covBy_grade ⦃a b : α⦄ : a ⋖ b → grade a ⋖ grade b
class GradeMinOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  isMin_grade ⦃a : α⦄ : IsMin a → IsMin (grade a)
class GradeMaxOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeOrder 𝕆 α where
  isMax_grade ⦃a : α⦄ : IsMax a → IsMax (grade a)
class GradeBoundedOrder (𝕆 α : Type*) [Preorder 𝕆] [Preorder α] extends GradeMinOrder 𝕆 α,
  GradeMaxOrder 𝕆 α
section Preorder 
variable [Preorder 𝕆]
section Preorder 
variable [Preorder α]
section GradeOrder
variable (𝕆)
variable [GradeOrder 𝕆 α] {a b : α}
def grade : α → 𝕆 :=
  GradeOrder.grade
protected theorem CovBy.grade (h : a ⋖ b) : grade 𝕆 a ⋖ grade 𝕆 b :=
  GradeOrder.covBy_grade h
variable {𝕆}
theorem grade_strictMono : StrictMono (grade 𝕆 : α → 𝕆) :=
  GradeOrder.grade_strictMono
theorem covBy_iff_lt_covBy_grade : a ⋖ b ↔ a < b ∧ grade 𝕆 a ⋖ grade 𝕆 b :=
  ⟨fun h => ⟨h.1, h.grade _⟩,
    And.imp_right fun h _ ha hb => h.2 (grade_strictMono ha) <| grade_strictMono hb⟩
end GradeOrder
section GradeMinOrder
variable (𝕆)
variable [GradeMinOrder 𝕆 α] {a : α}
protected theorem IsMin.grade (h : IsMin a) : IsMin (grade 𝕆 a) :=
  GradeMinOrder.isMin_grade h
variable {𝕆}
@[simp]
theorem isMin_grade_iff : IsMin (grade 𝕆 a) ↔ IsMin a :=
  ⟨grade_strictMono.isMin_of_apply, IsMin.grade _⟩
end GradeMinOrder
section GradeMaxOrder
variable (𝕆)
variable [GradeMaxOrder 𝕆 α] {a : α}
protected theorem IsMax.grade (h : IsMax a) : IsMax (grade 𝕆 a) :=
  GradeMaxOrder.isMax_grade h
variable {𝕆}
@[simp]
theorem isMax_grade_iff : IsMax (grade 𝕆 a) ↔ IsMax a :=
  ⟨grade_strictMono.isMax_of_apply, IsMax.grade _⟩
end GradeMaxOrder
end Preorder
theorem grade_mono [PartialOrder α] [GradeOrder 𝕆 α] : Monotone (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.monotone
section LinearOrder
variable [LinearOrder α] [GradeOrder 𝕆 α] {a b : α}
theorem grade_injective : Function.Injective (grade 𝕆 : α → 𝕆) :=
  grade_strictMono.injective
@[simp]
theorem grade_le_grade_iff : grade 𝕆 a ≤ grade 𝕆 b ↔ a ≤ b :=
  grade_strictMono.le_iff_le
@[simp]
theorem grade_lt_grade_iff : grade 𝕆 a < grade 𝕆 b ↔ a < b :=
  grade_strictMono.lt_iff_lt
@[simp]
theorem grade_eq_grade_iff : grade 𝕆 a = grade 𝕆 b ↔ a = b :=
  grade_injective.eq_iff
theorem grade_ne_grade_iff : grade 𝕆 a ≠ grade 𝕆 b ↔ a ≠ b :=
  grade_injective.ne_iff
theorem grade_covBy_grade_iff : grade 𝕆 a ⋖ grade 𝕆 b ↔ a ⋖ b :=
  (covBy_iff_lt_covBy_grade.trans <| and_iff_right_of_imp fun h => grade_lt_grade_iff.1 h.1).symm
end LinearOrder
end Preorder
section PartialOrder
variable [PartialOrder 𝕆] [Preorder α]
@[simp]
theorem grade_bot [OrderBot 𝕆] [OrderBot α] [GradeMinOrder 𝕆 α] : grade 𝕆 (⊥ : α) = ⊥ :=
  (isMin_bot.grade _).eq_bot
@[simp]
theorem grade_top [OrderTop 𝕆] [OrderTop α] [GradeMaxOrder 𝕆 α] : grade 𝕆 (⊤ : α) = ⊤ :=
  (isMax_top.grade _).eq_top
end PartialOrder
variable [Preorder 𝕆] [Preorder ℙ] [Preorder α] [Preorder β]
instance Preorder.toGradeBoundedOrder : GradeBoundedOrder α α where
  grade := id
  isMin_grade _ := id
  isMax_grade _ := id
  grade_strictMono := strictMono_id
  covBy_grade _ _ := id
@[simp]
theorem grade_self (a : α) : grade α a = a :=
  rfl
instance OrderDual.gradeOrder [GradeOrder 𝕆 α] : GradeOrder 𝕆ᵒᵈ αᵒᵈ where
  grade := toDual ∘ grade 𝕆 ∘ ofDual
  grade_strictMono := grade_strictMono.dual
  covBy_grade _ _ h := (h.ofDual.grade _).toDual
instance OrderDual.gradeMinOrder [GradeMaxOrder 𝕆 α] : GradeMinOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMin_grade := fun _ => IsMax.grade (α := α) 𝕆 }
instance OrderDual.gradeMaxOrder [GradeMinOrder 𝕆 α] : GradeMaxOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeOrder with isMax_grade := fun _ => IsMin.grade (α := α) 𝕆 }
instance [GradeBoundedOrder 𝕆 α] : GradeBoundedOrder 𝕆ᵒᵈ αᵒᵈ :=
  { OrderDual.gradeMinOrder, OrderDual.gradeMaxOrder with }
@[simp]
theorem grade_toDual [GradeOrder 𝕆 α] (a : α) : grade 𝕆ᵒᵈ (toDual a) = toDual (grade 𝕆 a) :=
  rfl
@[simp]
theorem grade_ofDual [GradeOrder 𝕆 α] (a : αᵒᵈ) : grade 𝕆 (ofDual a) = ofDual (grade 𝕆ᵒᵈ a) :=
  rfl
abbrev GradeOrder.liftLeft [GradeOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder ℙ α where
  grade := f ∘ grade 𝕆
  grade_strictMono := hf.comp grade_strictMono
  covBy_grade _ _ h := hcovBy _ _ <| h.grade _
abbrev GradeMinOrder.liftLeft [GradeMinOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMin_grade := fun _ ha => hmin _ <| ha.grade _ }
abbrev GradeMaxOrder.liftLeft [GradeMaxOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder ℙ α :=
  { GradeOrder.liftLeft f hf hcovBy with isMax_grade := fun _ ha => hmax _ <| ha.grade _ }
abbrev GradeBoundedOrder.liftLeft [GradeBoundedOrder 𝕆 α] (f : 𝕆 → ℙ) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder ℙ α :=
  { GradeMinOrder.liftLeft f hf hcovBy hmin, GradeMaxOrder.liftLeft f hf hcovBy hmax with }
abbrev GradeOrder.liftRight [GradeOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) : GradeOrder 𝕆 α where
  grade := grade 𝕆 ∘ f
  grade_strictMono := grade_strictMono.comp hf
  covBy_grade _ _ h := (hcovBy _ _ h).grade _
abbrev GradeMinOrder.liftRight [GradeMinOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a)) : GradeMinOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMin_grade := fun _ ha => (hmin _ ha).grade _ }
abbrev GradeMaxOrder.liftRight [GradeMaxOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeMaxOrder 𝕆 α :=
  { GradeOrder.liftRight f hf hcovBy with isMax_grade := fun _ ha => (hmax _ ha).grade _ }
abbrev GradeBoundedOrder.liftRight [GradeBoundedOrder 𝕆 β] (f : α → β) (hf : StrictMono f)
    (hcovBy : ∀ a b, a ⋖ b → f a ⋖ f b) (hmin : ∀ a, IsMin a → IsMin (f a))
    (hmax : ∀ a, IsMax a → IsMax (f a)) : GradeBoundedOrder 𝕆 α :=
  { GradeMinOrder.liftRight f hf hcovBy hmin, GradeMaxOrder.liftRight f hf hcovBy hmax with }
abbrev GradeOrder.finToNat (n : ℕ) [GradeOrder (Fin n) α] : GradeOrder ℕ α :=
  (GradeOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono) fun _ _ => CovBy.coe_fin
abbrev GradeMinOrder.finToNat (n : ℕ) [GradeMinOrder (Fin n) α] : GradeMinOrder ℕ α :=
  (GradeMinOrder.liftLeft (_ : Fin n → ℕ) Fin.val_strictMono fun _ _ => CovBy.coe_fin) fun a h => by
    cases n
    · exact a.elim0
    rw [h.eq_bot, Fin.bot_eq_zero]
    exact isMin_bot
instance GradeOrder.natToInt [GradeOrder ℕ α] : GradeOrder ℤ α :=
  (GradeOrder.liftLeft _ Int.natCast_strictMono) fun _ _ => CovBy.intCast
theorem GradeOrder.wellFoundedLT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedLT 𝕆] : WellFoundedLT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedLT
theorem GradeOrder.wellFoundedGT (𝕆 : Type*) [Preorder 𝕆] [GradeOrder 𝕆 α]
    [WellFoundedGT 𝕆] : WellFoundedGT α :=
  (grade_strictMono (𝕆 := 𝕆)).wellFoundedGT
instance [GradeOrder ℕ α] : WellFoundedLT α :=
  GradeOrder.wellFoundedLT ℕ
instance [GradeOrder ℕᵒᵈ α] : WellFoundedGT α :=
  GradeOrder.wellFoundedGT ℕᵒᵈ