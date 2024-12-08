import Mathlib.Algebra.Group.Pointwise.Set.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.SetTheory.Cardinal.Finite
open Pointwise
variable {M N : Type*} [Monoid M] [AddMonoid N]
section Submonoid
@[to_additive]
def Submonoid.FG (P : Submonoid M) : Prop :=
  ∃ S : Finset M, Submonoid.closure ↑S = P
add_decl_doc AddSubmonoid.FG
@[to_additive "An equivalent expression of `AddSubmonoid.FG` in terms of `Set.Finite` instead of
`Finset`."]
theorem Submonoid.fg_iff (P : Submonoid M) :
    Submonoid.FG P ↔ ∃ S : Set M, Submonoid.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩
theorem Submonoid.fg_iff_add_fg (P : Submonoid M) : P.FG ↔ P.toAddSubmonoid.FG :=
  ⟨fun h =>
    let ⟨S, hS, hf⟩ := (Submonoid.fg_iff _).1 h
    (AddSubmonoid.fg_iff _).mpr
      ⟨Additive.toMul ⁻¹' S, by simp [← Submonoid.toAddSubmonoid_closure, hS], hf⟩,
    fun h =>
    let ⟨T, hT, hf⟩ := (AddSubmonoid.fg_iff _).1 h
    (Submonoid.fg_iff _).mpr
      ⟨Multiplicative.ofAdd ⁻¹' T, by simp [← AddSubmonoid.toSubmonoid'_closure, hT], hf⟩⟩
theorem AddSubmonoid.fg_iff_mul_fg (P : AddSubmonoid N) : P.FG ↔ P.toSubmonoid.FG := by
  convert (Submonoid.fg_iff_add_fg (toSubmonoid P)).symm
end Submonoid
section Monoid
variable (M N)
class Monoid.FG : Prop where
  out : (⊤ : Submonoid M).FG
class AddMonoid.FG : Prop where
  out : (⊤ : AddSubmonoid N).FG
attribute [to_additive] Monoid.FG
variable {M N}
theorem Monoid.fg_def : Monoid.FG M ↔ (⊤ : Submonoid M).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
theorem AddMonoid.fg_def : AddMonoid.FG N ↔ (⊤ : AddSubmonoid N).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
@[to_additive
      "An equivalent expression of `AddMonoid.FG` in terms of `Set.Finite` instead of `Finset`."]
theorem Monoid.fg_iff :
    Monoid.FG M ↔ ∃ S : Set M, Submonoid.closure S = (⊤ : Submonoid M) ∧ S.Finite :=
  ⟨fun h => (Submonoid.fg_iff ⊤).1 h.out, fun h => ⟨(Submonoid.fg_iff ⊤).2 h⟩⟩
theorem Monoid.fg_iff_add_fg : Monoid.FG M ↔ AddMonoid.FG (Additive M) :=
  ⟨fun h => ⟨(Submonoid.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Submonoid.fg_iff_add_fg ⊤).2 h.out⟩⟩
theorem AddMonoid.fg_iff_mul_fg : AddMonoid.FG N ↔ Monoid.FG (Multiplicative N) :=
  ⟨fun h => ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubmonoid.fg_iff_mul_fg ⊤).2 h.out⟩⟩
instance AddMonoid.fg_of_monoid_fg [Monoid.FG M] : AddMonoid.FG (Additive M) :=
  Monoid.fg_iff_add_fg.1 ‹_›
instance Monoid.fg_of_addMonoid_fg [AddMonoid.FG N] : Monoid.FG (Multiplicative N) :=
  AddMonoid.fg_iff_mul_fg.1 ‹_›
@[to_additive]
instance (priority := 100) Monoid.fg_of_finite [Finite M] : Monoid.FG M := by
  cases nonempty_fintype M
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Submonoid.closure_univ⟩⟩
end Monoid
@[to_additive]
theorem Submonoid.FG.map {M' : Type*} [Monoid M'] {P : Submonoid M} (h : P.FG) (e : M →* M') :
    (P.map e).FG := by
  classical
    obtain ⟨s, rfl⟩ := h
    exact ⟨s.image e, by rw [Finset.coe_image, MonoidHom.map_mclosure]⟩
@[to_additive]
theorem Submonoid.FG.map_injective {M' : Type*} [Monoid M'] {P : Submonoid M} (e : M →* M')
    (he : Function.Injective e) (h : (P.map e).FG) : P.FG := by
  obtain ⟨s, hs⟩ := h
  use s.preimage e he.injOn
  apply Submonoid.map_injective_of_injective he
  rw [← hs, MonoidHom.map_mclosure e, Finset.coe_preimage]
  congr
  rw [Set.image_preimage_eq_iff, ← MonoidHom.coe_mrange e, ← Submonoid.closure_le, hs,
      MonoidHom.mrange_eq_map e]
  exact Submonoid.monotone_map le_top
@[to_additive (attr := simp)]
theorem Monoid.fg_iff_submonoid_fg (N : Submonoid M) : Monoid.FG N ↔ N.FG := by
  conv_rhs => rw [← N.mrange_subtype, MonoidHom.mrange_eq_map]
  exact ⟨fun h => h.out.map N.subtype, fun h => ⟨h.map_injective N.subtype Subtype.coe_injective⟩⟩
@[to_additive]
theorem Monoid.fg_of_surjective {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M')
    (hf : Function.Surjective f) : Monoid.FG M' := by
  classical
    obtain ⟨s, hs⟩ := Monoid.fg_def.mp ‹_›
    use s.image f
    rwa [Finset.coe_image, ← MonoidHom.map_mclosure, hs, ← MonoidHom.mrange_eq_map,
      MonoidHom.mrange_eq_top]
@[to_additive]
instance Monoid.fg_range {M' : Type*} [Monoid M'] [Monoid.FG M] (f : M →* M') :
    Monoid.FG (MonoidHom.mrange f) :=
  Monoid.fg_of_surjective f.mrangeRestrict f.mrangeRestrict_surjective
@[to_additive]
theorem Submonoid.powers_fg (r : M) : (Submonoid.powers r).FG :=
  ⟨{r}, (Finset.coe_singleton r).symm ▸ (Submonoid.powers_eq_closure r).symm⟩
@[to_additive]
instance Monoid.powers_fg (r : M) : Monoid.FG (Submonoid.powers r) :=
  (Monoid.fg_iff_submonoid_fg _).mpr (Submonoid.powers_fg r)
@[to_additive]
instance Monoid.closure_finset_fg (s : Finset M) : Monoid.FG (Submonoid.closure (s : Set M)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, Submonoid.closure_closure_coe_preimage]
@[to_additive]
instance Monoid.closure_finite_fg (s : Set M) [Finite s] : Monoid.FG (Submonoid.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Monoid.closure_finset_fg s.toFinset
variable {G H : Type*} [Group G] [AddGroup H]
section Subgroup
@[to_additive]
def Subgroup.FG (P : Subgroup G) : Prop :=
  ∃ S : Finset G, Subgroup.closure ↑S = P
add_decl_doc AddSubgroup.FG
@[to_additive "An equivalent expression of `AddSubgroup.fg` in terms of `Set.Finite` instead of
`Finset`."]
theorem Subgroup.fg_iff (P : Subgroup G) :
    Subgroup.FG P ↔ ∃ S : Set G, Subgroup.closure S = P ∧ S.Finite :=
  ⟨fun ⟨S, hS⟩ => ⟨S, hS, Finset.finite_toSet S⟩, fun ⟨S, hS, hf⟩ =>
    ⟨Set.Finite.toFinset hf, by simp [hS]⟩⟩
@[to_additive "An additive subgroup is finitely generated if
and only if it is finitely generated as an additive submonoid."]
theorem Subgroup.fg_iff_submonoid_fg (P : Subgroup G) : P.FG ↔ P.toSubmonoid.FG := by
  constructor
  · rintro ⟨S, rfl⟩
    rw [Submonoid.fg_iff]
    refine ⟨S ∪ S⁻¹, ?_, S.finite_toSet.union S.finite_toSet.inv⟩
    exact (Subgroup.closure_toSubmonoid _).symm
  · rintro ⟨S, hS⟩
    refine ⟨S, le_antisymm ?_ ?_⟩
    · rw [Subgroup.closure_le, ← Subgroup.coe_toSubmonoid, ← hS]
      exact Submonoid.subset_closure
    · rw [← Subgroup.toSubmonoid_le, ← hS, Submonoid.closure_le]
      exact Subgroup.subset_closure
theorem Subgroup.fg_iff_add_fg (P : Subgroup G) : P.FG ↔ P.toAddSubgroup.FG := by
  rw [Subgroup.fg_iff_submonoid_fg, AddSubgroup.fg_iff_addSubmonoid_fg]
  exact (Subgroup.toSubmonoid P).fg_iff_add_fg
theorem AddSubgroup.fg_iff_mul_fg (P : AddSubgroup H) : P.FG ↔ P.toSubgroup.FG := by
  rw [AddSubgroup.fg_iff_addSubmonoid_fg, Subgroup.fg_iff_submonoid_fg]
  exact AddSubmonoid.fg_iff_mul_fg (AddSubgroup.toAddSubmonoid P)
end Subgroup
section Group
variable (G H)
class Group.FG : Prop where
  out : (⊤ : Subgroup G).FG
class AddGroup.FG : Prop where
  out : (⊤ : AddSubgroup H).FG
attribute [to_additive] Group.FG
variable {G H}
theorem Group.fg_def : Group.FG G ↔ (⊤ : Subgroup G).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
theorem AddGroup.fg_def : AddGroup.FG H ↔ (⊤ : AddSubgroup H).FG :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
@[to_additive
      "An equivalent expression of `AddGroup.fg` in terms of `Set.Finite` instead of `Finset`."]
theorem Group.fg_iff : Group.FG G ↔ ∃ S : Set G, Subgroup.closure S = (⊤ : Subgroup G) ∧ S.Finite :=
  ⟨fun h => (Subgroup.fg_iff ⊤).1 h.out, fun h => ⟨(Subgroup.fg_iff ⊤).2 h⟩⟩
@[to_additive]
theorem Group.fg_iff' :
    Group.FG G ↔ ∃ (n : _) (S : Finset G), S.card = n ∧ Subgroup.closure (S : Set G) = ⊤ :=
  Group.fg_def.trans ⟨fun ⟨S, hS⟩ => ⟨S.card, S, rfl, hS⟩, fun ⟨_n, S, _hn, hS⟩ => ⟨S, hS⟩⟩
@[to_additive "An additive group is finitely generated if and only
if it is finitely generated as an additive monoid."]
theorem Group.fg_iff_monoid_fg : Group.FG G ↔ Monoid.FG G :=
  ⟨fun h => Monoid.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).1 (Group.fg_def.1 h), fun h =>
    Group.fg_def.2 <| (Subgroup.fg_iff_submonoid_fg ⊤).2 (Monoid.fg_def.1 h)⟩
@[to_additive (attr := simp)]
theorem Group.fg_iff_subgroup_fg (H : Subgroup G) : Group.FG H ↔ H.FG :=
  (fg_iff_monoid_fg.trans (Monoid.fg_iff_submonoid_fg _)).trans
    (Subgroup.fg_iff_submonoid_fg _).symm
theorem GroupFG.iff_add_fg : Group.FG G ↔ AddGroup.FG (Additive G) :=
  ⟨fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).1 h.out⟩, fun h => ⟨(Subgroup.fg_iff_add_fg ⊤).2 h.out⟩⟩
theorem AddGroup.fg_iff_mul_fg : AddGroup.FG H ↔ Group.FG (Multiplicative H) :=
  ⟨fun h => ⟨(AddSubgroup.fg_iff_mul_fg ⊤).1 h.out⟩, fun h =>
    ⟨(AddSubgroup.fg_iff_mul_fg ⊤).2 h.out⟩⟩
instance AddGroup.fg_of_group_fg [Group.FG G] : AddGroup.FG (Additive G) :=
  GroupFG.iff_add_fg.1 ‹_›
instance Group.fg_of_mul_group_fg [AddGroup.FG H] : Group.FG (Multiplicative H) :=
  AddGroup.fg_iff_mul_fg.1 ‹_›
@[to_additive]
instance (priority := 100) Group.fg_of_finite [Finite G] : Group.FG G := by
  cases nonempty_fintype G
  exact ⟨⟨Finset.univ, by rw [Finset.coe_univ]; exact Subgroup.closure_univ⟩⟩
@[to_additive]
theorem Group.fg_of_surjective {G' : Type*} [Group G'] [hG : Group.FG G] {f : G →* G'}
    (hf : Function.Surjective f) : Group.FG G' :=
  Group.fg_iff_monoid_fg.mpr <|
    @Monoid.fg_of_surjective G _ G' _ (Group.fg_iff_monoid_fg.mp hG) f hf
@[to_additive]
instance Group.fg_range {G' : Type*} [Group G'] [Group.FG G] (f : G →* G') : Group.FG f.range :=
  Group.fg_of_surjective f.rangeRestrict_surjective
@[to_additive]
instance Group.closure_finset_fg (s : Finset G) : Group.FG (Subgroup.closure (s : Set G)) := by
  refine ⟨⟨s.preimage Subtype.val Subtype.coe_injective.injOn, ?_⟩⟩
  rw [Finset.coe_preimage, ← Subgroup.coeSubtype, Subgroup.closure_preimage_eq_top]
@[to_additive]
instance Group.closure_finite_fg (s : Set G) [Finite s] : Group.FG (Subgroup.closure s) :=
  haveI := Fintype.ofFinite s
  s.coe_toFinset ▸ Group.closure_finset_fg s.toFinset
variable (G)
@[to_additive "The minimum number of generators of an additive group"]
noncomputable def Group.rank [h : Group.FG G] :=
  @Nat.find _ (Classical.decPred _) (Group.fg_iff'.mp h)
@[to_additive]
theorem Group.rank_spec [h : Group.FG G] :
    ∃ S : Finset G, S.card = Group.rank G ∧ Subgroup.closure (S : Set G) = ⊤ :=
  @Nat.find_spec _ (Classical.decPred _) (Group.fg_iff'.mp h)
@[to_additive]
theorem Group.rank_le [h : Group.FG G] {S : Finset G} (hS : Subgroup.closure (S : Set G) = ⊤) :
    Group.rank G ≤ S.card :=
  @Nat.find_le _ _ (Classical.decPred _) (Group.fg_iff'.mp h) ⟨S, rfl, hS⟩
variable {G} {G' : Type*} [Group G']
@[to_additive]
theorem Group.rank_le_of_surjective [Group.FG G] [Group.FG G'] (f : G →* G')
    (hf : Function.Surjective f) : Group.rank G' ≤ Group.rank G := by
  classical
    obtain ⟨S, hS1, hS2⟩ := Group.rank_spec G
    trans (S.image f).card
    · apply Group.rank_le
      rw [Finset.coe_image, ← MonoidHom.map_closure, hS2, Subgroup.map_top_of_surjective f hf]
    · exact Finset.card_image_le.trans_eq hS1
@[to_additive]
theorem Group.rank_range_le [Group.FG G] {f : G →* G'} : Group.rank f.range ≤ Group.rank G :=
  Group.rank_le_of_surjective f.rangeRestrict f.rangeRestrict_surjective
@[to_additive]
theorem Group.rank_congr [Group.FG G] [Group.FG G'] (f : G ≃* G') : Group.rank G = Group.rank G' :=
  le_antisymm (Group.rank_le_of_surjective f.symm f.symm.surjective)
    (Group.rank_le_of_surjective f f.surjective)
end Group
namespace Subgroup
@[to_additive]
theorem rank_congr {H K : Subgroup G} [Group.FG H] [Group.FG K] (h : H = K) :
    Group.rank H = Group.rank K := by subst h; rfl
@[to_additive]
theorem rank_closure_finset_le_card (s : Finset G) : Group.rank (closure (s : Set G)) ≤ s.card := by
  classical
  let t : Finset (closure (s : Set G)) := s.preimage Subtype.val Subtype.coe_injective.injOn
  have ht : closure (t : Set (closure (s : Set G))) = ⊤ := by
    rw [Finset.coe_preimage]
    exact closure_preimage_eq_top (s : Set G)
  apply (Group.rank_le (closure (s : Set G)) ht).trans
  suffices H : Set.InjOn Subtype.val (t : Set (closure (s : Set G))) by
    rw [← Finset.card_image_of_injOn H, Finset.image_preimage]
    apply Finset.card_filter_le
  apply Subtype.coe_injective.injOn
@[to_additive]
theorem rank_closure_finite_le_nat_card (s : Set G) [Finite s] :
    Group.rank (closure s) ≤ Nat.card s := by
  haveI := Fintype.ofFinite s
  rw [Nat.card_eq_fintype_card, ← s.toFinset_card, ← rank_congr (congr_arg _ s.coe_toFinset)]
  exact rank_closure_finset_le_card s.toFinset
theorem nat_card_centralizer_nat_card_stabilizer (g : G) :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  rw [Subgroup.centralizer_eq_comap_stabilizer]
  rfl
end Subgroup
section QuotientGroup
@[to_additive]
instance QuotientGroup.fg [Group.FG G] (N : Subgroup G) [Subgroup.Normal N] : Group.FG <| G ⧸ N :=
  Group.fg_of_surjective <| QuotientGroup.mk'_surjective N
end QuotientGroup