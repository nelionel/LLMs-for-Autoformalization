import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Order.Filter.AtTopBot.BigOperators
import Mathlib.Topology.Separation.Basic
noncomputable section
open Filter Function
open scoped Topology
variable {α β γ : Type*}
section HasProd
variable [CommMonoid α] [TopologicalSpace α]
@[to_additive "`HasSum f a` means that the (potentially infinite) sum of the `f b` for `b : β`
converges to `a`.
The `atTop` filter on `Finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.
This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).
For the definition and many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant."]
def HasProd (f : β → α) (a : α) : Prop :=
  Tendsto (fun s : Finset β ↦ ∏ b ∈ s, f b) atTop (𝓝 a)
@[to_additive "`Summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value."]
def Multipliable (f : β → α) : Prop :=
  ∃ a, HasProd f a
open scoped Classical in
@[to_additive "`∑' i, f i` is the sum of `f` if it exists and is unconditionally convergent,
or 0 otherwise."]
noncomputable irreducible_def tprod {β} (f : β → α) :=
  if h : Multipliable f then
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1
@[inherit_doc tprod]
notation3 "∏' "(...)", "r:67:(scoped f => tprod f) => r
@[inherit_doc tsum]
notation3 "∑' "(...)", "r:67:(scoped f => tsum f) => r
variable {f : β → α} {a : α} {s : Finset β}
@[to_additive]
theorem HasProd.multipliable (h : HasProd f a) : Multipliable f :=
  ⟨a, h⟩
@[to_additive]
theorem tprod_eq_one_of_not_multipliable (h : ¬Multipliable f) : ∏' b, f b = 1 := by
  simp [tprod_def, h]
@[to_additive]
theorem Function.Injective.hasProd_iff {g : γ → β} (hg : Injective g)
    (hf : ∀ x, x ∉ Set.range g → f x = 1) : HasProd (f ∘ g) a ↔ HasProd f a := by
  simp only [HasProd, Tendsto, comp_apply, hg.map_atTop_finset_prod_eq hf]
@[to_additive]
theorem hasProd_subtype_iff_of_mulSupport_subset {s : Set β} (hf : mulSupport f ⊆ s) :
    HasProd (f ∘ (↑) : s → α) a ↔ HasProd f a :=
  Subtype.coe_injective.hasProd_iff <| by simpa using mulSupport_subset_iff'.1 hf
@[to_additive]
theorem hasProd_fintype [Fintype β] (f : β → α) : HasProd f (∏ b, f b) :=
  OrderTop.tendsto_atTop_nhds _
@[to_additive]
protected theorem Finset.hasProd (s : Finset β) (f : β → α) :
    HasProd (f ∘ (↑) : (↑s : Set β) → α) (∏ b ∈ s, f b) := by
  rw [← prod_attach]
  exact hasProd_fintype _
@[to_additive "If a function `f` vanishes outside of a finite set `s`, then it `HasSum`
`∑ b ∈ s, f b`."]
theorem hasProd_prod_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) :
    HasProd f (∏ b ∈ s, f b) :=
  (hasProd_subtype_iff_of_mulSupport_subset <| mulSupport_subset_iff'.2 hf).1 <| s.hasProd f
@[to_additive]
theorem multipliable_of_ne_finset_one (hf : ∀ b ∉ s, f b = 1) : Multipliable f :=
  (hasProd_prod_of_ne_finset_one hf).multipliable
@[to_additive]
theorem Multipliable.hasProd (ha : Multipliable f) : HasProd f (∏' b, f b) := by
  simp only [tprod_def, ha, dite_true]
  by_cases H : (mulSupport f).Finite
  · simp [H, hasProd_prod_of_ne_finset_one, finprod_eq_prod]
  · simpa [H] using ha.choose_spec
@[to_additive]
theorem HasProd.unique {a₁ a₂ : α} [T2Space α] : HasProd f a₁ → HasProd f a₂ → a₁ = a₂ := by
  classical exact tendsto_nhds_unique
variable [T2Space α]
@[to_additive]
theorem HasProd.tprod_eq (ha : HasProd f a) : ∏' b, f b = a :=
  (Multipliable.hasProd ⟨a, ha⟩).unique ha
@[to_additive]
theorem Multipliable.hasProd_iff (h : Multipliable f) : HasProd f a ↔ ∏' b, f b = a :=
  Iff.intro HasProd.tprod_eq fun eq ↦ eq ▸ h.hasProd
end HasProd