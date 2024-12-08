import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Deprecated.Group
variable {M : Type*} [Monoid M] {s : Set M} {A : Type*} [AddMonoid A]
structure IsAddSubmonoid (s : Set A) : Prop where
  zero_mem : (0 : A) ∈ s
  add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s
@[to_additive]
structure IsSubmonoid (s : Set M) : Prop where
  one_mem : (1 : M) ∈ s
  mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s
theorem Additive.isAddSubmonoid {s : Set M} :
    IsSubmonoid s → @IsAddSubmonoid (Additive M) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
theorem Additive.isAddSubmonoid_iff {s : Set M} :
    @IsAddSubmonoid (Additive M) _ s ↔ IsSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Additive.isAddSubmonoid⟩
theorem Multiplicative.isSubmonoid {s : Set A} :
    IsAddSubmonoid s → @IsSubmonoid (Multiplicative A) _ s
  | ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩
theorem Multiplicative.isSubmonoid_iff {s : Set A} :
    @IsSubmonoid (Multiplicative A) _ s ↔ IsAddSubmonoid s :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, @h₂⟩, Multiplicative.isSubmonoid⟩
@[to_additive
      "The intersection of two `AddSubmonoid`s of an `AddMonoid` `M` is an `AddSubmonoid` of M."]
theorem IsSubmonoid.inter {s₁ s₂ : Set M} (is₁ : IsSubmonoid s₁) (is₂ : IsSubmonoid s₂) :
    IsSubmonoid (s₁ ∩ s₂) :=
  { one_mem := ⟨is₁.one_mem, is₂.one_mem⟩
    mul_mem := @fun _ _ hx hy => ⟨is₁.mul_mem hx.1 hy.1, is₂.mul_mem hx.2 hy.2⟩ }
@[to_additive
      "The intersection of an indexed set of `AddSubmonoid`s of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem IsSubmonoid.iInter {ι : Sort*} {s : ι → Set M} (h : ∀ y : ι, IsSubmonoid (s y)) :
    IsSubmonoid (Set.iInter s) :=
  { one_mem := Set.mem_iInter.2 fun y => (h y).one_mem
    mul_mem := fun h₁ h₂ =>
      Set.mem_iInter.2 fun y => (h y).mul_mem (Set.mem_iInter.1 h₁ y) (Set.mem_iInter.1 h₂ y) }
@[to_additive
      "The union of an indexed, directed, nonempty set of `AddSubmonoid`s of an `AddMonoid` `M`
      is an `AddSubmonoid` of `M`. "]
theorem isSubmonoid_iUnion_of_directed {ι : Type*} [hι : Nonempty ι] {s : ι → Set M}
    (hs : ∀ i, IsSubmonoid (s i)) (Directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) :
    IsSubmonoid (⋃ i, s i) :=
  { one_mem :=
      let ⟨i⟩ := hι
      Set.mem_iUnion.2 ⟨i, (hs i).one_mem⟩
    mul_mem := fun ha hb =>
      let ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      let ⟨j, hj⟩ := Set.mem_iUnion.1 hb
      let ⟨k, hk⟩ := Directed i j
      Set.mem_iUnion.2 ⟨k, (hs k).mul_mem (hk.1 hi) (hk.2 hj)⟩ }
section powers
@[to_additive
      "The set of natural number multiples `0, x, 2x, ...` of an element `x` of an `AddMonoid`."]
def powers (x : M) : Set M :=
  { y | ∃ n : ℕ, x ^ n = y }
@[to_additive "0 is in the set of natural number multiples of an element of an `AddMonoid`."]
theorem powers.one_mem {x : M} : (1 : M) ∈ powers x :=
  ⟨0, pow_zero _⟩
@[to_additive
      "An element of an `AddMonoid` is in the set of that element's natural number multiples."]
theorem powers.self_mem {x : M} : x ∈ powers x :=
  ⟨1, pow_one _⟩
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` is closed under
      addition."]
theorem powers.mul_mem {x y z : M} : y ∈ powers x → z ∈ powers x → y * z ∈ powers x :=
  fun ⟨n₁, h₁⟩ ⟨n₂, h₂⟩ => ⟨n₁ + n₂, by simp only [pow_add, *]⟩
@[to_additive
      "The set of natural number multiples of an element of an `AddMonoid` `M` is
      an `AddSubmonoid` of `M`."]
theorem powers.isSubmonoid (x : M) : IsSubmonoid (powers x) :=
  { one_mem := powers.one_mem
    mul_mem := powers.mul_mem }
@[to_additive "An `AddMonoid` is an `AddSubmonoid` of itself."]
theorem Univ.isSubmonoid : IsSubmonoid (@Set.univ M) := by constructor <;> simp
@[to_additive
      "The preimage of an `AddSubmonoid` under an `AddMonoid` hom is
      an `AddSubmonoid` of the domain."]
theorem IsSubmonoid.preimage {N : Type*} [Monoid N] {f : M → N} (hf : IsMonoidHom f) {s : Set N}
    (hs : IsSubmonoid s) : IsSubmonoid (f ⁻¹' s) :=
  { one_mem := show f 1 ∈ s by (rw [IsMonoidHom.map_one hf]; exact hs.one_mem)
    mul_mem := fun {a b} (ha : f a ∈ s) (hb : f b ∈ s) =>
      show f (a * b) ∈ s by (rw [IsMonoidHom.map_mul' hf]; exact hs.mul_mem ha hb) }
@[to_additive
      "The image of an `AddSubmonoid` under an `AddMonoid` hom is an `AddSubmonoid` of the
      codomain."]
theorem IsSubmonoid.image {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) {s : Set M}
    (hs : IsSubmonoid s) : IsSubmonoid (f '' s) :=
  { one_mem := ⟨1, hs.one_mem, hf.map_one⟩
    mul_mem := @fun a b ⟨x, hx⟩ ⟨y, hy⟩ =>
      ⟨x * y, hs.mul_mem hx.1 hy.1, by rw [hf.map_mul, hx.2, hy.2]⟩ }
@[to_additive "The image of an `AddMonoid` hom is an `AddSubmonoid` of the codomain."]
theorem Range.isSubmonoid {γ : Type*} [Monoid γ] {f : M → γ} (hf : IsMonoidHom f) :
    IsSubmonoid (Set.range f) := by
  rw [← Set.image_univ]
  exact Univ.isSubmonoid.image hf
@[to_additive
      "An `AddSubmonoid` is closed under multiplication by naturals."]
theorem IsSubmonoid.pow_mem {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : ∀ {n : ℕ}, a ^ n ∈ s
  | 0 => by
    rw [pow_zero]
    exact hs.one_mem
  | n + 1 => by
    rw [pow_succ]
    exact hs.mul_mem (IsSubmonoid.pow_mem hs h) h
@[to_additive
      "The set of natural number multiples of an element of an `AddSubmonoid` is a subset of
      the `AddSubmonoid`."]
theorem IsSubmonoid.powers_subset {a : M} (hs : IsSubmonoid s) (h : a ∈ s) : powers a ⊆ s :=
  fun _ ⟨_, hx⟩ => hx ▸ hs.pow_mem h
@[deprecated (since := "2024-02-21")] alias IsSubmonoid.power_subset := IsSubmonoid.powers_subset
end powers
namespace IsSubmonoid
@[to_additive
      "The sum of a list of elements of an `AddSubmonoid` is an element of the `AddSubmonoid`."]
theorem list_prod_mem (hs : IsSubmonoid s) : ∀ {l : List M}, (∀ x ∈ l, x ∈ s) → l.prod ∈ s
  | [], _ => hs.one_mem
  | a :: l, h =>
    suffices a * l.prod ∈ s by simpa
    have : a ∈ s ∧ ∀ x ∈ l, x ∈ s := by simpa using h
    hs.mul_mem this.1 (list_prod_mem hs this.2)
@[to_additive
      "The sum of a multiset of elements of an `AddSubmonoid` of an `AddCommMonoid`
      is an element of the `AddSubmonoid`. "]
theorem multiset_prod_mem {M} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (m : Multiset M) :
    (∀ a ∈ m, a ∈ s) → m.prod ∈ s := by
  refine Quotient.inductionOn m fun l hl => ?_
  rw [Multiset.quot_mk_to_coe, Multiset.prod_coe]
  exact list_prod_mem hs hl
@[to_additive
      "The sum of elements of an `AddSubmonoid` of an `AddCommMonoid` indexed by
      a `Finset` is an element of the `AddSubmonoid`."]
theorem finset_prod_mem {M A} [CommMonoid M] {s : Set M} (hs : IsSubmonoid s) (f : A → M) :
    ∀ t : Finset A, (∀ b ∈ t, f b ∈ s) → (∏ b ∈ t, f b) ∈ s
  | ⟨m, hm⟩, _ => multiset_prod_mem hs _ (by simpa)
end IsSubmonoid
namespace AddMonoid
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → InClosure _ a
  | zero : InClosure _ 0
  | add {a b : A} : InClosure _ a → InClosure _ b → InClosure _ (a + b)
end AddMonoid
namespace Monoid
@[to_additive]
inductive InClosure (s : Set M) : M → Prop
  | basic {a : M} : a ∈ s → InClosure _ a
  | one : InClosure _ 1
  | mul {a b : M} : InClosure _ a → InClosure _ b → InClosure _ (a * b)
@[to_additive
      "The inductively defined `AddSubmonoid` generated by a subset of an `AddMonoid`."]
def Closure (s : Set M) : Set M :=
  { a | InClosure s a }
@[to_additive]
theorem closure.isSubmonoid (s : Set M) : IsSubmonoid (Closure s) :=
  { one_mem := InClosure.one
    mul_mem := InClosure.mul }
@[to_additive
    "A subset of an `AddMonoid` is contained in the `AddSubmonoid` it generates."]
theorem subset_closure {s : Set M} : s ⊆ Closure s := fun _ => InClosure.basic
@[to_additive
      "The `AddSubmonoid` generated by a set is contained in any `AddSubmonoid` that
      contains the set."]
theorem closure_subset {s t : Set M} (ht : IsSubmonoid t) (h : s ⊆ t) : Closure s ⊆ t := fun a ha =>
  by induction ha <;> simp [h _, *, IsSubmonoid.one_mem, IsSubmonoid.mul_mem]
@[to_additive (attr := gcongr)
      "Given subsets `t` and `s` of an `AddMonoid M`, if `s ⊆ t`, the `AddSubmonoid`
      of `M` generated by `s` is contained in the `AddSubmonoid` generated by `t`."]
theorem closure_mono {s t : Set M} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset (closure.isSubmonoid t) <| Set.Subset.trans h subset_closure
@[to_additive
      "The `AddSubmonoid` generated by an element of an `AddMonoid` equals the set of
      natural number multiples of the element."]
theorem closure_singleton {x : M} : Closure ({x} : Set M) = powers x :=
  Set.eq_of_subset_of_subset
      (closure_subset (powers.isSubmonoid x) <| Set.singleton_subset_iff.2 <| powers.self_mem) <|
    IsSubmonoid.powers_subset (closure.isSubmonoid _) <|
      Set.singleton_subset_iff.1 <| subset_closure
@[to_additive
      "The image under an `AddMonoid` hom of the `AddSubmonoid` generated by a set equals
      the `AddSubmonoid` generated by the image of the set under the `AddMonoid` hom."]
theorem image_closure {A : Type*} [Monoid A] {f : M → A} (hf : IsMonoidHom f) (s : Set M) :
    f '' Closure s = Closure (f '' s) :=
  le_antisymm
    (by
      rintro _ ⟨x, hx, rfl⟩
      induction' hx with z hz
      · solve_by_elim [subset_closure, Set.mem_image_of_mem]
      · rw [hf.map_one]
        apply IsSubmonoid.one_mem (closure.isSubmonoid (f '' s))
      · rw [hf.map_mul]
        solve_by_elim [(closure.isSubmonoid _).mul_mem] )
    (closure_subset (IsSubmonoid.image hf (closure.isSubmonoid _)) <|
      Set.image_subset _ subset_closure)
@[to_additive
      "Given an element `a` of the `AddSubmonoid` of an `AddMonoid M` generated by
      a set `s`, there exists a list of elements of `s` whose sum is `a`."]
theorem exists_list_of_mem_closure {s : Set M} {a : M} (h : a ∈ Closure s) :
    ∃ l : List M, (∀ x ∈ l, x ∈ s) ∧ l.prod = a := by
  induction h with
  | @basic a ha => exists [a]; simp [ha]
  | one => exists []; simp
  | mul _ _ ha hb =>
    rcases ha with ⟨la, ha, eqa⟩
    rcases hb with ⟨lb, hb, eqb⟩
    exists la ++ lb
    simp only [List.mem_append, or_imp, List.prod_append, eqa.symm, eqb.symm, and_true]
    exact fun a => ⟨ha a, hb a⟩
@[to_additive
      "Given sets `s, t` of a commutative `AddMonoid M`, `x ∈ M` is in the `AddSubmonoid`
      of `M` generated by `s ∪ t` iff there exists an element of the `AddSubmonoid` generated by `s`
      and an element of the `AddSubmonoid` generated by `t` whose sum is `x`."]
theorem mem_closure_union_iff {M : Type*} [CommMonoid M] {s t : Set M} {x : M} :
    x ∈ Closure (s ∪ t) ↔ ∃ y ∈ Closure s, ∃ z ∈ Closure t, y * z = x :=
  ⟨fun hx =>
    let ⟨L, HL1, HL2⟩ := exists_list_of_mem_closure hx
    HL2 ▸
      List.recOn L
        (fun _ =>
          ⟨1, (closure.isSubmonoid _).one_mem, 1, (closure.isSubmonoid _).one_mem, mul_one _⟩)
        (fun hd tl ih HL1 =>
          let ⟨y, hy, z, hz, hyzx⟩ := ih (List.forall_mem_of_forall_mem_cons HL1)
          Or.casesOn (HL1 hd <| List.mem_cons_self _ _)
            (fun hs =>
              ⟨hd * y, (closure.isSubmonoid _).mul_mem (subset_closure hs) hy, z, hz, by
                rw [mul_assoc, List.prod_cons, ← hyzx]⟩)
            fun ht =>
            ⟨y, hy, z * hd, (closure.isSubmonoid _).mul_mem hz (subset_closure ht), by
              rw [← mul_assoc, List.prod_cons, ← hyzx, mul_comm hd]⟩)
        HL1,
    fun ⟨_, hy, _, hz, hyzx⟩ =>
    hyzx ▸
      (closure.isSubmonoid _).mul_mem (closure_mono Set.subset_union_left hy)
        (closure_mono Set.subset_union_right hz)⟩
end Monoid
@[to_additive "Create a bundled additive submonoid from a set `s` and `[IsAddSubmonoid s]`."]
def Submonoid.of {s : Set M} (h : IsSubmonoid s) : Submonoid M :=
  ⟨⟨s, @fun _ _ => h.2⟩, h.1⟩
@[to_additive]
theorem Submonoid.isSubmonoid (S : Submonoid M) : IsSubmonoid (S : Set M) := by
  exact ⟨S.2, S.1.2⟩