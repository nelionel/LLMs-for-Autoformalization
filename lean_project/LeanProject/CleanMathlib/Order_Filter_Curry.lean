import Mathlib.Order.Filter.Prod
namespace Filter
variable {α β γ : Type*} {l : Filter α} {m : Filter β} {s : Set α} {t : Set β}
theorem eventually_curry_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in l.curry m, p x) ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, p (x, y) :=
  Iff.rfl
theorem frequently_curry_iff
    (p : (α × β) → Prop) : (∃ᶠ x in l.curry m, p x) ↔ ∃ᶠ x in l, ∃ᶠ y in m, p (x, y) := by
  simp_rw [Filter.Frequently, not_iff_not, not_not, eventually_curry_iff]
theorem mem_curry_iff {s : Set (α × β)} :
    s ∈ l.curry m ↔ ∀ᶠ x : α in l, ∀ᶠ y : β in m, (x, y) ∈ s := Iff.rfl
theorem curry_le_prod : l.curry m ≤ l ×ˢ m := fun _ => Eventually.curry
theorem Tendsto.curry {f : α → β → γ} {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (h : ∀ᶠ a in la, Tendsto (fun b : β => f a b) lb lc) : Tendsto (↿f) (la.curry lb) lc :=
  fun _s hs => h.mono fun _a ha => ha hs
theorem frequently_curry_prod_iff :
    (∃ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ (∃ᶠ x in l, x ∈ s) ∧ ∃ᶠ y in m, y ∈ t := by
  simp [frequently_curry_iff]
theorem eventually_curry_prod_iff [NeBot l] [NeBot m] :
    (∀ᶠ x in l.curry m, x ∈ s ×ˢ t) ↔ s ∈ l ∧ t ∈ m := by
  simp [eventually_curry_iff]
theorem prod_mem_curry (hs : s ∈ l) (ht : t ∈ m) : s ×ˢ t ∈ l.curry m :=
  curry_le_prod <| prod_mem_prod hs ht
end Filter