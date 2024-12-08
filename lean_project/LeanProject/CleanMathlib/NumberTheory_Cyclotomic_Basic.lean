import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
open Polynomial Algebra Module Set
universe u v w z
variable (n : ℕ+) (S T : Set ℕ+) (A : Type u) (B : Type v) (K : Type w) (L : Type z)
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Field K] [Field L] [Algebra K L]
noncomputable section
@[mk_iff]
class IsCyclotomicExtension : Prop where
  exists_prim_root {n : ℕ+} (ha : n ∈ S) : ∃ r : B, IsPrimitiveRoot r n
  adjoin_roots : ∀ x : B, x ∈ adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}
namespace IsCyclotomicExtension
section Basic
theorem iff_adjoin_eq_top :
    IsCyclotomicExtension S A B ↔
      (∀ n : ℕ+, n ∈ S → ∃ r : B, IsPrimitiveRoot r n) ∧
        adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} = ⊤ :=
  ⟨fun h => ⟨fun _ => h.exists_prim_root, Algebra.eq_top_iff.2 h.adjoin_roots⟩, fun h =>
    ⟨h.1 _, Algebra.eq_top_iff.1 h.2⟩⟩
theorem iff_singleton :
    IsCyclotomicExtension {n} A B ↔
      (∃ r : B, IsPrimitiveRoot r n) ∧ ∀ x, x ∈ adjoin A {b : B | b ^ (n : ℕ) = 1} := by
  simp [isCyclotomicExtension_iff]
theorem empty [h : IsCyclotomicExtension ∅ A B] : (⊥ : Subalgebra A B) = ⊤ := by
  simpa [Algebra.eq_top_iff, isCyclotomicExtension_iff] using h
theorem singleton_one [h : IsCyclotomicExtension {1} A B] : (⊥ : Subalgebra A B) = ⊤ :=
  Algebra.eq_top_iff.2 fun x => by
    simpa [adjoin_singleton_one] using ((isCyclotomicExtension_iff _ _ _).1 h).2 x
variable {A B}
theorem singleton_zero_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) :
    IsCyclotomicExtension ∅ A B := by
  refine (iff_adjoin_eq_top _ A _).2
    ⟨fun s hs => by simp at hs, _root_.eq_top_iff.2 fun x hx => ?_⟩
  rw [← h] at hx
  simpa using hx
variable (A B)
theorem trans (C : Type w) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [hS : IsCyclotomicExtension S A B] [hT : IsCyclotomicExtension T B C]
    (h : Function.Injective (algebraMap B C)) : IsCyclotomicExtension (S ∪ T) A C := by
  refine ⟨fun hn => ?_, fun x => ?_⟩
  · cases' hn with hn hn
    · obtain ⟨b, hb⟩ := ((isCyclotomicExtension_iff _ _ _).1 hS).1 hn
      refine ⟨algebraMap B C b, ?_⟩
      exact hb.map_of_injective h
    · exact ((isCyclotomicExtension_iff _ _ _).1 hT).1 hn
  · refine adjoin_induction (hx := ((isCyclotomicExtension_iff T B _).1 hT).2 x)
      (fun c ⟨n, hn⟩ => subset_adjoin ⟨n, Or.inr hn.1, hn.2⟩) (fun b => ?_)
      (fun x y _ _ hx hy => Subalgebra.add_mem _ hx hy)
      fun x y _ _ hx hy => Subalgebra.mul_mem _ hx hy
    let f := IsScalarTower.toAlgHom A B C
    have hb : f b ∈ (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}).map f :=
      ⟨b, ((isCyclotomicExtension_iff _ _ _).1 hS).2 b, rfl⟩
    rw [IsScalarTower.toAlgHom_apply, ← adjoin_image] at hb
    refine adjoin_mono (fun y hy => ?_) hb
    obtain ⟨b₁, ⟨⟨n, hn⟩, h₁⟩⟩ := hy
    exact ⟨n, ⟨mem_union_left T hn.1, by rw [← h₁, ← map_pow, hn.2, map_one]⟩⟩
@[nontriviality]
theorem subsingleton_iff [Subsingleton B] : IsCyclotomicExtension S A B ↔ S = { } ∨ S = {1} := by
  have : Subsingleton (Subalgebra A B) := inferInstance
  constructor
  · rintro ⟨hprim, -⟩
    rw [← subset_singleton_iff_eq]
    intro t ht
    obtain ⟨ζ, hζ⟩ := hprim ht
    rw [mem_singleton_iff, ← PNat.coe_eq_one_iff]
    exact mod_cast hζ.unique (IsPrimitiveRoot.of_subsingleton ζ)
  · rintro (rfl | rfl)
    · exact ⟨fun h => h.elim, fun x => by convert (mem_top (R := A) : x ∈ ⊤)⟩
    · rw [iff_singleton]
      exact ⟨⟨0, IsPrimitiveRoot.of_subsingleton 0⟩,
        fun x => by convert (mem_top (R := A) : x ∈ ⊤)⟩
theorem union_right [h : IsCyclotomicExtension (S ∪ T) A B] :
    IsCyclotomicExtension T (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) B := by
  have : {b : B | ∃ n : ℕ+, n ∈ S ∪ T ∧ b ^ (n : ℕ) = 1} =
      {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1} ∪
        {b : B | ∃ n : ℕ+, n ∈ T ∧ b ^ (n : ℕ) = 1} := by
    refine le_antisymm ?_ ?_
    · rintro x ⟨n, hn₁ | hn₂, hnpow⟩
      · left; exact ⟨n, hn₁, hnpow⟩
      · right; exact ⟨n, hn₂, hnpow⟩
    · rintro x (⟨n, hn⟩ | ⟨n, hn⟩)
      · exact ⟨n, Or.inl hn.1, hn.2⟩
      · exact ⟨n, Or.inr hn.1, hn.2⟩
  refine ⟨fun hn => ((isCyclotomicExtension_iff _ A _).1 h).1 (mem_union_right S hn), fun b => ?_⟩
  replace h := ((isCyclotomicExtension_iff _ _ _).1 h).2 b
  rwa [this, adjoin_union_eq_adjoin_adjoin, Subalgebra.mem_restrictScalars] at h
theorem union_left [h : IsCyclotomicExtension T A B] (hS : S ⊆ T) :
    IsCyclotomicExtension S A (adjoin A {b : B | ∃ a : ℕ+, a ∈ S ∧ b ^ (a : ℕ) = 1}) := by
  refine ⟨@fun n hn => ?_, fun b => ?_⟩
  · obtain ⟨b, hb⟩ := ((isCyclotomicExtension_iff _ _ _).1 h).1 (hS hn)
    refine ⟨⟨b, subset_adjoin ⟨n, hn, hb.pow_eq_one⟩⟩, ?_⟩
    rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  · convert mem_top (R := A) (x := b)
    rw [← adjoin_adjoin_coe_preimage, preimage_setOf_eq]
    norm_cast
variable {n S}
theorem of_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) [H : IsCyclotomicExtension S A B] :
    IsCyclotomicExtension (S ∪ {n}) A B := by
  refine (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => ?_, ?_⟩
  · rw [mem_union, mem_singleton_iff] at hs
    obtain hs | rfl := hs
    · exact H.exists_prim_root hs
    · obtain ⟨m, hm⟩ := hS
      obtain ⟨x, rfl⟩ := h m hm
      obtain ⟨ζ, hζ⟩ := H.exists_prim_root hm
      refine ⟨ζ ^ (x : ℕ), ?_⟩
      convert hζ.pow_of_dvd x.ne_zero (dvd_mul_left (x : ℕ) s)
      simp only [PNat.mul_coe, Nat.mul_div_left, PNat.pos]
  · refine _root_.eq_top_iff.2 ?_
    rw [← ((iff_adjoin_eq_top S A B).1 H).2]
    refine adjoin_mono fun x hx => ?_
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq] at hx ⊢
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, ⟨Or.inr hm.1, hm.2⟩⟩
theorem iff_union_of_dvd (h : ∀ s ∈ S, n ∣ s) (hS : S.Nonempty) :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {n}) A B := by
  refine
    ⟨fun H => of_union_of_dvd A B h hS, fun H => (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => ?_, ?_⟩⟩
  · exact H.exists_prim_root (subset_union_left hs)
  · rw [_root_.eq_top_iff, ← ((iff_adjoin_eq_top _ A B).1 H).2]
    refine adjoin_mono fun x hx => ?_
    simp only [union_singleton, mem_insert_iff, mem_setOf_eq] at hx ⊢
    obtain ⟨m, rfl | hm, hxpow⟩ := hx
    · obtain ⟨y, hy⟩ := hS
      refine ⟨y, ⟨hy, ?_⟩⟩
      obtain ⟨z, rfl⟩ := h y hy
      simp only [PNat.mul_coe, pow_mul, hxpow, one_pow]
    · exact ⟨m, ⟨hm, hxpow⟩⟩
variable (n S)
theorem iff_union_singleton_one :
    IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S ∪ {1}) A B := by
  obtain hS | rfl := S.eq_empty_or_nonempty.symm
  · exact iff_union_of_dvd _ _ (fun s _ => one_dvd _) hS
  rw [empty_union]
  refine ⟨fun H => ?_, fun H => ?_⟩
  · refine (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => ⟨1, by simp [mem_singleton_iff.1 hs]⟩, ?_⟩
    simp [adjoin_singleton_one, empty]
  · refine (iff_adjoin_eq_top _ A _).2 ⟨fun s hs => (not_mem_empty s hs).elim, ?_⟩
    simp [@singleton_one A B _ _ _ H]
variable {A B}
theorem singleton_one_of_bot_eq_top (h : (⊥ : Subalgebra A B) = ⊤) :
    IsCyclotomicExtension {1} A B := by
  convert (iff_union_singleton_one _ A _).1 (singleton_zero_of_bot_eq_top h)
  simp
theorem singleton_one_of_algebraMap_bijective (h : Function.Surjective (algebraMap A B)) :
    IsCyclotomicExtension {1} A B :=
  singleton_one_of_bot_eq_top (surjective_algebraMap_iff.1 h).symm
variable (A B)
protected
theorem equiv {C : Type*} [CommRing C] [Algebra A C] [h : IsCyclotomicExtension S A B]
    (f : B ≃ₐ[A] C) : IsCyclotomicExtension S A C := by
  letI : Algebra B C := f.toAlgHom.toRingHom.toAlgebra
  haveI : IsCyclotomicExtension {1} B C := singleton_one_of_algebraMap_bijective f.surjective
  haveI : IsScalarTower A B C := IsScalarTower.of_algHom f.toAlgHom
  exact (iff_union_singleton_one _ _ _).2 (trans S {1} A B C f.injective)
protected
theorem neZero [h : IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : B) := by
  obtain ⟨⟨r, hr⟩, -⟩ := (iff_singleton n A B).1 h
  exact hr.neZero'
protected
theorem neZero' [IsCyclotomicExtension {n} A B] [IsDomain B] : NeZero ((n : ℕ) : A) := by
  haveI := IsCyclotomicExtension.neZero n A B
  exact NeZero.nat_of_neZero (algebraMap A B)
end Basic
section Fintype
theorem finite_of_singleton [IsDomain B] [h : IsCyclotomicExtension {n} A B] :
    Module.Finite A B := by
  classical
  rw [Module.finite_def, ← top_toSubmodule, ← ((iff_adjoin_eq_top _ _ _).1 h).2]
  refine fg_adjoin_of_finite ?_ fun b hb => ?_
  · simp only [mem_singleton_iff, exists_eq_left]
    have : {b : B | b ^ (n : ℕ) = 1} = (nthRoots n (1 : B)).toFinset :=
      Set.ext fun x => ⟨fun h => by simpa using h, fun h => by simpa using h⟩
    rw [this]
    exact (nthRoots (↑n) 1).toFinset.finite_toSet
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hb
    exact ⟨X ^ (n : ℕ) - 1, ⟨monic_X_pow_sub_C _ n.pos.ne.symm, by simp [hb]⟩⟩
protected theorem finite [IsDomain B] [h₁ : Finite S] [h₂ : IsCyclotomicExtension S A B] :
    Module.Finite A B := by
  cases' nonempty_fintype S with h
  revert h₂ A B
  refine Set.Finite.induction_on h₁ (fun A B => ?_) @fun n S _ _ H A B => ?_
  · intro _ _ _ _ _
    refine Module.finite_def.2 ⟨({1} : Finset B), ?_⟩
    simp [← top_toSubmodule, ← empty, toSubmodule_bot, Submodule.one_eq_span]
  · intro _ _ _ _ h
    haveI : IsCyclotomicExtension S A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) :=
      union_left _ (insert n S) _ _ (subset_insert n S)
    haveI := H A (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1})
    have : Module.Finite (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) B := by
      rw [← union_singleton] at h
      letI := @union_right S {n} A B _ _ _ h
      exact finite_of_singleton n _ _
    exact Module.Finite.trans (adjoin A {b : B | ∃ n : ℕ+, n ∈ S ∧ b ^ (n : ℕ) = 1}) _
theorem numberField [h : NumberField K] [Finite S] [IsCyclotomicExtension S K L] : NumberField L :=
  { to_charZero := charZero_of_injective_algebraMap (algebraMap K L).injective
    to_finiteDimensional := by
      haveI := charZero_of_injective_algebraMap (algebraMap K L).injective
      haveI := IsCyclotomicExtension.finite S K L
      exact Module.Finite.trans K _ }
theorem integral [IsDomain B] [IsNoetherianRing A] [Finite S] [IsCyclotomicExtension S A B] :
    Algebra.IsIntegral A B :=
  have := IsCyclotomicExtension.finite S A B
  ⟨isIntegral_of_noetherian inferInstance⟩
theorem finiteDimensional (C : Type z) [Finite S] [CommRing C] [Algebra K C] [IsDomain C]
    [IsCyclotomicExtension S K C] : FiniteDimensional K C :=
  IsCyclotomicExtension.finite S K C
end Fintype
section
variable {A B}
theorem adjoin_roots_cyclotomic_eq_adjoin_nth_roots [IsDomain B] {ζ : B} {n : ℕ+}
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin A ((cyclotomic n A).rootSet B) =
      adjoin A {b : B | ∃ a : ℕ+, a ∈ ({n} : Set ℕ+) ∧ b ^ (a : ℕ) = 1} := by
  simp only [mem_singleton_iff, exists_eq_left, map_cyclotomic]
  refine le_antisymm (adjoin_mono fun x hx => ?_) (adjoin_le fun x hx => ?_)
  · rw [mem_rootSet'] at hx
    simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq]
    rw [isRoot_of_unity_iff n.pos]
    refine ⟨n, Nat.mem_divisors_self n n.ne_zero, ?_⟩
    rw [IsRoot.def, ← map_cyclotomic n (algebraMap A B), eval_map, ← aeval_def]
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hx
    obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    refine SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin ?_) _)
    rw [mem_rootSet', map_cyclotomic, aeval_def, ← eval_map, map_cyclotomic, ← IsRoot]
    exact ⟨cyclotomic_ne_zero n B, hζ.isRoot_cyclotomic n.pos⟩
theorem adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic {n : ℕ+} [IsDomain B] {ζ : B}
    (hζ : IsPrimitiveRoot ζ n) : adjoin A ((cyclotomic n A).rootSet B) = adjoin A {ζ} := by
  refine le_antisymm (adjoin_le fun x hx => ?_) (adjoin_mono fun x hx => ?_)
  · suffices hx : x ^ n.1 = 1 by
      obtain ⟨i, _, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      exact SetLike.mem_coe.2 (Subalgebra.pow_mem _ (subset_adjoin <| mem_singleton ζ) _)
    refine (isRoot_of_unity_iff n.pos B).2 ?_
    refine ⟨n, Nat.mem_divisors_self n n.ne_zero, ?_⟩
    rw [mem_rootSet', aeval_def, ← eval_map, map_cyclotomic, ← IsRoot] at hx
    exact hx.2
  · simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq] at hx
    simpa only [hx, mem_rootSet', map_cyclotomic, aeval_def, ← eval_map, IsRoot] using
      And.intro (cyclotomic_ne_zero n B) (hζ.isRoot_cyclotomic n.pos)
theorem adjoin_primitive_root_eq_top {n : ℕ+} [IsDomain B] [h : IsCyclotomicExtension {n} A B]
    {ζ : B} (hζ : IsPrimitiveRoot ζ n) : adjoin A ({ζ} : Set B) = ⊤ := by
  classical
  rw [← adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic hζ]
  rw [adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ]
  exact ((iff_adjoin_eq_top {n} A B).mp h).2
variable (A)
theorem _root_.IsPrimitiveRoot.adjoin_isCyclotomicExtension {ζ : B} {n : ℕ+}
    (h : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} A (adjoin A ({ζ} : Set B)) :=
  { exists_prim_root := fun hi => by
      rw [Set.mem_singleton_iff] at hi
      refine ⟨⟨ζ, subset_adjoin <| Set.mem_singleton ζ⟩, ?_⟩
      rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk, hi]
    adjoin_roots := fun ⟨x, hx⟩ => by
      refine
        adjoin_induction
          (hx := hx) (fun b hb => ?_) (fun a => ?_) (fun b₁ b₂ _ _ hb₁ hb₂ => ?_)
          (fun b₁ b₂ _ _ hb₁ hb₂ => ?_)
      · rw [Set.mem_singleton_iff] at hb
        refine subset_adjoin ?_
        simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq, hb]
        rw [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, Subtype.coe_mk]
        exact ((IsPrimitiveRoot.iff_def ζ n).1 h).1
      · exact Subalgebra.algebraMap_mem _ _
      · exact Subalgebra.add_mem _ hb₁ hb₂
      · exact Subalgebra.mul_mem _ hb₁ hb₂ }
end
section Field
variable {n S}
theorem splits_X_pow_sub_one [H : IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (X ^ (n : ℕ) - 1) := by
  rw [← splits_id_iff_splits, Polynomial.map_sub, Polynomial.map_one, Polynomial.map_pow,
    Polynomial.map_X]
  obtain ⟨z, hz⟩ := ((isCyclotomicExtension_iff _ _ _).1 H).1 hS
  exact X_pow_sub_one_splits hz
theorem splits_cyclotomic [IsCyclotomicExtension S K L] (hS : n ∈ S) :
    Splits (algebraMap K L) (cyclotomic n K) := by
  refine splits_of_splits_of_dvd _ (X_pow_sub_C_ne_zero n.pos _) (splits_X_pow_sub_one K L hS) ?_
  use ∏ i ∈ (n : ℕ).properDivisors, Polynomial.cyclotomic i K
  rw [(eq_cyclotomic_iff n.pos _).1 rfl, RingHom.map_one]
variable (n S)
section Singleton
variable [IsCyclotomicExtension {n} K L]
theorem isSplittingField_X_pow_sub_one : IsSplittingField K L (X ^ (n : ℕ) - 1) :=
  { splits' := splits_X_pow_sub_one K L (mem_singleton n)
    adjoin_rootSet' := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      congr
      refine Set.ext fun x => ?_
      simp only [Polynomial.map_pow, mem_singleton_iff, Multiset.mem_toFinset, exists_eq_left,
        mem_setOf_eq, Polynomial.map_X, Polynomial.map_one, Finset.mem_coe, Polynomial.map_sub]
      simp only [mem_rootSet', map_sub, map_pow, aeval_one, aeval_X, sub_eq_zero, map_X,
        and_iff_right_iff_imp, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one]
      exact fun _ => X_pow_sub_C_ne_zero n.pos (1 : L) }
def algEquiv (L' : Type*) [Field L'] [Algebra K L'] [IsCyclotomicExtension {n} K L'] :
    L ≃ₐ[K] L' :=
  let h₁ := isSplittingField_X_pow_sub_one n K L
  let h₂ := isSplittingField_X_pow_sub_one n K L'
  (@IsSplittingField.algEquiv K L _ _ _ (X ^ (n : ℕ) - 1) h₁).trans
    (@IsSplittingField.algEquiv K L' _ _ _ (X ^ (n : ℕ) - 1) h₂).symm
scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.isSplittingField_X_pow_sub_one
include n in
theorem isGalois : IsGalois K L :=
  letI := isSplittingField_X_pow_sub_one n K L
  IsGalois.of_separable_splitting_field (X_pow_sub_one_separable_iff.2
    (IsCyclotomicExtension.neZero' n K L).1)
theorem splitting_field_cyclotomic : IsSplittingField K L (cyclotomic n K) :=
  { splits' := splits_cyclotomic K L (mem_singleton n)
    adjoin_rootSet' := by
      rw [← ((iff_adjoin_eq_top {n} K L).1 inferInstance).2]
      letI := Classical.decEq L
      obtain ⟨ζ : L, hζ⟩ := IsCyclotomicExtension.exists_prim_root K (B := L) (mem_singleton n)
      exact adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ }
scoped[Cyclotomic] attribute [instance] IsCyclotomicExtension.splitting_field_cyclotomic
end Singleton
end Field
end IsCyclotomicExtension
section CyclotomicField
def CyclotomicField : Type w :=
  (cyclotomic n K).SplittingField
namespace CyclotomicField
instance : Field (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance
instance algebra : Algebra K (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance
instance : Inhabited (CyclotomicField n K) := by
  delta CyclotomicField; infer_instance
instance [CharZero K] : CharZero (CyclotomicField n K) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective
instance isCyclotomicExtension [NeZero ((n : ℕ) : K)] :
    IsCyclotomicExtension {n} K (CyclotomicField n K) := by
  haveI : NeZero ((n : ℕ) : CyclotomicField n K) :=
    NeZero.nat_of_injective (algebraMap K _).injective
  letI := Classical.decEq (CyclotomicField n K)
  obtain ⟨ζ, hζ⟩ :=
    exists_root_of_splits (algebraMap K (CyclotomicField n K)) (SplittingField.splits _)
      (degree_cyclotomic_pos n K n.pos).ne'
  rw [← eval_map, ← IsRoot.def, map_cyclotomic, isRoot_cyclotomic_iff] at hζ
  refine ⟨?_, ?_⟩
  · simp only [mem_singleton_iff, forall_eq]
    exact ⟨ζ, hζ⟩
  · rw [← Algebra.eq_top_iff, ← SplittingField.adjoin_rootSet, eq_comm]
    exact IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots hζ
end CyclotomicField
end CyclotomicField
section IsDomain
variable [Algebra A K]
section CyclotomicRing
@[nolint unusedArguments]
instance CyclotomicField.algebraBase : Algebra A (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
example : Ring.toIntAlgebra (CyclotomicField n ℚ) = CyclotomicField.algebraBase _ _ _ := rfl
instance CyclotomicField.algebra' {R : Type*} [CommRing R] [Algebra R K] :
    Algebra R (CyclotomicField n K) :=
  SplittingField.algebra' (cyclotomic n K)
instance {R : Type*} [CommRing R] [Algebra R K] : IsScalarTower R K (CyclotomicField n K) :=
  SplittingField.isScalarTower _
instance CyclotomicField.noZeroSMulDivisors [IsFractionRing A K] :
    NoZeroSMulDivisors A (CyclotomicField n K) := by
  refine NoZeroSMulDivisors.of_algebraMap_injective ?_
  rw [IsScalarTower.algebraMap_eq A K (CyclotomicField n K)]
  exact
    (Function.Injective.comp (NoZeroSMulDivisors.algebraMap_injective K (CyclotomicField n K))
      (IsFractionRing.injective A K) : _)
@[nolint unusedArguments]
def CyclotomicRing : Type w :=
  adjoin A {b : CyclotomicField n K | b ^ (n : ℕ) = 1}
namespace CyclotomicRing
instance : CommRing (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance
instance : IsDomain (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance
instance : Inhabited (CyclotomicRing n A K) := by
  delta CyclotomicRing; infer_instance
instance algebraBase : Algebra A (CyclotomicRing n A K) :=
  (adjoin A _).algebra
example {n : ℕ+} : CyclotomicRing.algebraBase n ℤ ℚ = Ring.toIntAlgebra _ := rfl
instance [IsFractionRing A K] :
    NoZeroSMulDivisors A (CyclotomicRing n A K) :=
  (adjoin A _).noZeroSMulDivisors_bot
theorem algebraBase_injective [IsFractionRing A K] :
    Function.Injective <| algebraMap A (CyclotomicRing n A K) :=
  NoZeroSMulDivisors.algebraMap_injective _ _
instance : Algebra (CyclotomicRing n A K) (CyclotomicField n K) :=
  (adjoin A _).toAlgebra
theorem adjoin_algebra_injective :
    Function.Injective <| algebraMap (CyclotomicRing n A K) (CyclotomicField n K) :=
  Subtype.val_injective
instance : NoZeroSMulDivisors (CyclotomicRing n A K) (CyclotomicField n K) :=
  NoZeroSMulDivisors.of_algebraMap_injective (adjoin_algebra_injective n A K)
instance : IsScalarTower A (CyclotomicRing n A K) (CyclotomicField n K) :=
  IsScalarTower.subalgebra' _ _ _ _
instance isCyclotomicExtension [IsFractionRing A K] [NeZero ((n : ℕ) : A)] :
    IsCyclotomicExtension {n} A (CyclotomicRing n A K) where
  exists_prim_root := @fun a han => by
    rw [mem_singleton_iff] at han
    subst a
    haveI := NeZero.of_noZeroSMulDivisors A K n
    haveI := NeZero.of_noZeroSMulDivisors A (CyclotomicField n K) n
    obtain ⟨μ, hμ⟩ := (CyclotomicField.isCyclotomicExtension n K).exists_prim_root (mem_singleton n)
    refine ⟨⟨μ, subset_adjoin ?_⟩, ?_⟩
    · apply (isRoot_of_unity_iff n.pos (CyclotomicField n K)).mpr
      refine ⟨n, Nat.mem_divisors_self _ n.ne_zero, ?_⟩
      rwa [← isRoot_cyclotomic_iff] at hμ
    · rwa [← IsPrimitiveRoot.coe_submonoidClass_iff, Subtype.coe_mk]
  adjoin_roots x := by
    obtain ⟨x, hx⟩ := x
    refine
      adjoin_induction (fun y hy => ?_) (fun a => ?_) (fun y z _ _ hy hz => ?_)
        (fun y z  _ _ hy hz => ?_) hx
    · refine subset_adjoin ?_
      simp only [mem_singleton_iff, exists_eq_left, mem_setOf_eq]
      rwa [← Subalgebra.coe_eq_one, Subalgebra.coe_pow, Subtype.coe_mk]
    · exact Subalgebra.algebraMap_mem _ a
    · exact Subalgebra.add_mem _ hy hz
    · exact Subalgebra.mul_mem _ hy hz
instance [IsFractionRing A K] [IsDomain A] [NeZero ((n : ℕ) : A)] :
    IsFractionRing (CyclotomicRing n A K) (CyclotomicField n K) where
  map_units' := fun ⟨x, hx⟩ => by
    rw [isUnit_iff_ne_zero]
    apply map_ne_zero_of_mem_nonZeroDivisors
    · apply adjoin_algebra_injective
    · exact hx
  surj' x := by
    letI : NeZero ((n : ℕ) : K) := NeZero.nat_of_injective (IsFractionRing.injective A K)
    refine
      Algebra.adjoin_induction
        (hx := ((IsCyclotomicExtension.iff_singleton n K (CyclotomicField n K)).1
            (CyclotomicField.isCyclotomicExtension n K)).2 x)
        (fun y hy => ?_) (fun k => ?_) ?_ ?_
    · exact ⟨⟨⟨y, subset_adjoin hy⟩, 1⟩, by simp; rfl⟩
    · have : IsLocalization (nonZeroDivisors A) K := inferInstance
      replace := this.surj
      obtain ⟨⟨z, w⟩, hw⟩ := this k
      refine ⟨⟨algebraMap A (CyclotomicRing n A K) z, algebraMap A (CyclotomicRing n A K) w,
        map_mem_nonZeroDivisors _ (algebraBase_injective n A K) w.2⟩, ?_⟩
      letI : IsScalarTower A K (CyclotomicField n K) :=
        IsScalarTower.of_algebraMap_eq (congr_fun rfl)
      rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        @IsScalarTower.algebraMap_apply A K _ _ _ _ _ (_root_.CyclotomicField.algebra n K) _ _ w,
        ← RingHom.map_mul, hw, ← IsScalarTower.algebraMap_apply]
    · rintro y z - - ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨⟨a.1 * b.2 + b.1 * a.2, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, ?_⟩
      rw [RingHom.map_mul, add_mul, ← mul_assoc, ha,
        mul_comm ((algebraMap (CyclotomicRing n A K) _) ↑a.2), ← mul_assoc, hb]
      simp only [map_add, map_mul]
    · rintro y z - - ⟨a, ha⟩ ⟨b, hb⟩
      refine ⟨⟨a.1 * b.1, a.2 * b.2, mul_mem_nonZeroDivisors.2 ⟨a.2.2, b.2.2⟩⟩, ?_⟩
      rw [RingHom.map_mul, mul_comm ((algebraMap (CyclotomicRing n A K) _) ↑a.2), mul_assoc, ←
        mul_assoc z, hb, ← mul_comm ((algebraMap (CyclotomicRing n A K) _) ↑a.2), ← mul_assoc, ha]
      simp only [map_mul]
  exists_of_eq {x y} h := ⟨1, by rw [adjoin_algebra_injective n A K h]⟩
theorem eq_adjoin_primitive_root {μ : CyclotomicField n K} (h : IsPrimitiveRoot μ n) :
    CyclotomicRing n A K = adjoin A ({μ} : Set (CyclotomicField n K)) := by
  rw [← IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic h,
    IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots h]
  simp [CyclotomicRing]
end CyclotomicRing
end CyclotomicRing
end IsDomain
section IsAlgClosed
variable [IsAlgClosed K]
theorem IsAlgClosed.isCyclotomicExtension (h : ∀ a ∈ S, NeZero ((a : ℕ) : K)) :
    IsCyclotomicExtension S K K := by
  refine ⟨@fun a ha => ?_, Algebra.eq_top_iff.mp <| Subsingleton.elim _ _⟩
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_aeval_eq_zero K _ (degree_cyclotomic_pos a K a.pos).ne'
  refine ⟨r, ?_⟩
  haveI := h a ha
  rwa [coe_aeval_eq_eval, ← IsRoot.def, isRoot_cyclotomic_iff] at hr
instance IsAlgClosedOfCharZero.isCyclotomicExtension [CharZero K] :
    ∀ S, IsCyclotomicExtension S K K := fun S =>
  IsAlgClosed.isCyclotomicExtension S K fun _ _ => inferInstance
end IsAlgClosed