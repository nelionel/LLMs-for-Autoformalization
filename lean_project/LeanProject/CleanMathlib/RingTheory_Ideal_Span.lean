import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.Tactic.Ring
universe u v w
variable {α : Type u} {β : Type v} {F : Type w}
open Set Function
open Pointwise
@[mk_iff]
class IsPrincipalIdealRing (R : Type u) [Semiring R] : Prop where
  principal : ∀ S : Ideal R, S.IsPrincipal
attribute [instance] IsPrincipalIdealRing.principal
section Semiring
namespace Ideal
variable [Semiring α] (I : Ideal α) {a b : α}
def span (s : Set α) : Ideal α :=
  Submodule.span α s
@[simp]
theorem submodule_span_eq {s : Set α} : Submodule.span α s = Ideal.span s :=
  rfl
@[simp]
theorem span_empty : span (∅ : Set α) = ⊥ :=
  Submodule.span_empty
@[simp]
theorem span_univ : span (Set.univ : Set α) = ⊤ :=
  Submodule.span_univ
theorem span_union (s t : Set α) : span (s ∪ t) = span s ⊔ span t :=
  Submodule.span_union _ _
theorem span_iUnion {ι} (s : ι → Set α) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  Submodule.span_iUnion _
theorem mem_span {s : Set α} (x) : x ∈ span s ↔ ∀ p : Ideal α, s ⊆ p → x ∈ p :=
  mem_iInter₂
theorem subset_span {s : Set α} : s ⊆ span s :=
  Submodule.subset_span
theorem span_le {s : Set α} {I} : span s ≤ I ↔ s ⊆ I :=
  Submodule.span_le
theorem span_mono {s t : Set α} : s ⊆ t → span s ≤ span t :=
  Submodule.span_mono
@[simp]
theorem span_eq : span (I : Set α) = I :=
  Submodule.span_eq _
@[simp]
theorem span_singleton_one : span ({1} : Set α) = ⊤ :=
  (eq_top_iff_one _).2 <| subset_span <| mem_singleton _
theorem isCompactElement_top : CompleteLattice.IsCompactElement (⊤ : Ideal α) := by
  simpa only [← span_singleton_one] using Submodule.singleton_span_isCompactElement 1
theorem mem_span_insert {s : Set α} {x y} :
    x ∈ span (insert y s) ↔ ∃ a, ∃ z ∈ span s, x = a * y + z :=
  Submodule.mem_span_insert
theorem mem_span_singleton' {x y : α} : x ∈ span ({y} : Set α) ↔ ∃ a, a * y = x :=
  Submodule.mem_span_singleton
theorem mem_span_singleton_self (x : α) : x ∈ span ({x} : Set α) :=
  Submodule.mem_span_singleton_self x
theorem span_singleton_le_iff_mem {x : α} : span {x} ≤ I ↔ x ∈ I :=
  Submodule.span_singleton_le_iff_mem _ _
theorem span_singleton_mul_left_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({a * x} : Set α) = span {x} := by
  apply le_antisymm <;> rw [span_singleton_le_iff_mem, mem_span_singleton']
  exacts [⟨a, rfl⟩, ⟨_, h2.unit.inv_mul_cancel_left x⟩]
theorem span_insert (x) (s : Set α) : span (insert x s) = span ({x} : Set α) ⊔ span s :=
  Submodule.span_insert x s
theorem span_eq_bot {s : Set α} : span s = ⊥ ↔ ∀ x ∈ s, (x : α) = 0 :=
  Submodule.span_eq_bot
@[simp]
theorem span_singleton_eq_bot {x} : span ({x} : Set α) = ⊥ ↔ x = 0 :=
  Submodule.span_singleton_eq_bot
theorem span_singleton_ne_top {α : Type*} [CommSemiring α] {x : α} (hx : ¬IsUnit x) :
    Ideal.span ({x} : Set α) ≠ ⊤ :=
  (Ideal.ne_top_iff_one _).mpr fun h1 =>
    let ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h1
    hx ⟨⟨x, y, mul_comm y x ▸ hy, hy⟩, rfl⟩
@[simp]
theorem span_zero : span (0 : Set α) = ⊥ := by rw [← Set.singleton_zero, span_singleton_eq_bot]
@[simp]
theorem span_one : span (1 : Set α) = ⊤ := by rw [← Set.singleton_one, span_singleton_one]
theorem span_eq_top_iff_finite (s : Set α) :
    span s = ⊤ ↔ ∃ s' : Finset α, ↑s' ⊆ s ∧ span (s' : Set α) = ⊤ := by
  simp_rw [eq_top_iff_one]
  exact ⟨Submodule.mem_span_finite_of_mem_span, fun ⟨s', h₁, h₂⟩ => span_mono h₁ h₂⟩
theorem mem_span_singleton_sup {x y : α} {I : Ideal α} :
    x ∈ Ideal.span {y} ⊔ I ↔ ∃ a : α, ∃ b ∈ I, a * y + b = x := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨ya, hya, b, hb, rfl⟩
    obtain ⟨a, rfl⟩ := mem_span_singleton'.mp hya
    exact ⟨a, b, hb, rfl⟩
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨a * y, Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩, b, hb, rfl⟩
def ofRel (r : α → α → Prop) : Ideal α :=
  Submodule.span α { x | ∃ a b, r a b ∧ x + b = a }
theorem zero_ne_one_of_proper {I : Ideal α} (h : I ≠ ⊤) : (0 : α) ≠ 1 := fun hz =>
  I.ne_top_iff_one.1 h <| hz ▸ I.zero_mem
theorem span_pair_comm {x y : α} : (span {x, y} : Ideal α) = span {y, x} := by
  simp only [span_insert, sup_comm]
theorem mem_span_pair {x y z : α} : z ∈ span ({x, y} : Set α) ↔ ∃ a b, a * x + b * y = z :=
  Submodule.mem_span_pair
@[simp]
theorem span_pair_add_mul_left {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x + y * z, y} : Ideal R) = span {x, y} := by
  ext
  rw [mem_span_pair, mem_span_pair]
  exact
    ⟨fun ⟨a, b, h⟩ =>
      ⟨a, b + a * z, by
        rw [← h]
        ring1⟩,
      fun ⟨a, b, h⟩ =>
      ⟨a, b - a * z, by
        rw [← h]
        ring1⟩⟩
@[simp]
theorem span_pair_add_mul_right {R : Type u} [CommRing R] {x y : R} (z : R) :
    (span {x, y + x * z} : Ideal R) = span {x, y} := by
  rw [span_pair_comm, span_pair_add_mul_left, span_pair_comm]
end Ideal
end Semiring
section CommSemiring
variable {a b : α}
namespace Ideal
variable [CommSemiring α] (I : Ideal α)
theorem mem_span_singleton {x y : α} : x ∈ span ({y} : Set α) ↔ y ∣ x :=
  mem_span_singleton'.trans <| exists_congr fun _ => by rw [eq_comm, mul_comm]
theorem span_singleton_le_span_singleton {x y : α} :
    span ({x} : Set α) ≤ span ({y} : Set α) ↔ y ∣ x :=
  span_le.trans <| singleton_subset_iff.trans mem_span_singleton
theorem span_singleton_eq_span_singleton {α : Type u} [CommRing α] [IsDomain α] {x y : α} :
    span ({x} : Set α) = span ({y} : Set α) ↔ Associated x y := by
  rw [← dvd_dvd_iff_associated, le_antisymm_iff, and_comm]
  apply and_congr <;> rw [span_singleton_le_span_singleton]
theorem span_singleton_mul_right_unit {a : α} (h2 : IsUnit a) (x : α) :
    span ({x * a} : Set α) = span {x} := by rw [mul_comm, span_singleton_mul_left_unit h2]
@[simp]
theorem span_singleton_eq_top {x} : span ({x} : Set α) = ⊤ ↔ IsUnit x := by
  rw [isUnit_iff_dvd_one, ← span_singleton_le_span_singleton, span_singleton_one, eq_top_iff]
theorem factors_decreasing [IsDomain α] (b₁ b₂ : α) (h₁ : b₁ ≠ 0) (h₂ : ¬IsUnit b₂) :
    span ({b₁ * b₂} : Set α) < span {b₁} :=
  lt_of_le_not_le
    (Ideal.span_le.2 <| singleton_subset_iff.2 <| Ideal.mem_span_singleton.2 ⟨b₂, rfl⟩) fun h =>
    h₂ <| isUnit_of_dvd_one <|
        (mul_dvd_mul_iff_left h₁).1 <| by rwa [mul_one, ← Ideal.span_singleton_le_span_singleton]
end Ideal
end CommSemiring
section Ring
namespace Ideal
variable [Ring α] (I : Ideal α) {a b : α}
theorem mem_span_insert' {s : Set α} {x y} : x ∈ span (insert y s) ↔ ∃ a, x + a * y ∈ span s :=
  Submodule.mem_span_insert'
@[simp]
theorem span_singleton_neg (x : α) : (span {-x} : Ideal α) = span {x} := by
  ext
  simp only [mem_span_singleton']
  exact ⟨fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_comm y x⟩, fun ⟨y, h⟩ => ⟨-y, h ▸ neg_mul_neg y x⟩⟩
end Ideal
end Ring
namespace IsIdempotentElem
variable {R} [CommRing R] {e : R} (he : IsIdempotentElem e)
include he
theorem ker_toSpanSingleton_eq_span :
    LinearMap.ker (LinearMap.toSpanSingleton R R e) = Ideal.span {1 - e} := SetLike.ext fun x ↦ by
  rw [Ideal.mem_span_singleton']
  refine ⟨fun h ↦ ⟨x, by rw [mul_sub, show x * e = 0 from h, mul_one, sub_zero]⟩, fun h ↦ ?_⟩
  obtain ⟨x, rfl⟩ := h
  show x * (1 - e) * e = 0
  rw [mul_assoc, sub_mul, one_mul, he, sub_self, mul_zero]
theorem ker_toSpanSingleton_one_sub_eq_span :
    LinearMap.ker (LinearMap.toSpanSingleton R R (1 - e)) = Ideal.span {e} := by
  rw [ker_toSpanSingleton_eq_span he.one_sub, sub_sub_cancel]
end IsIdempotentElem