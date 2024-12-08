import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Flat.Basic
open scoped TensorProduct
noncomputable section
universe u v w
namespace Submodule
variable {R : Type u} {S : Type v}
section Semiring
variable [CommSemiring R] [Semiring S] [Algebra R S]
variable (M N : Submodule R S)
@[mk_iff]
protected structure LinearDisjoint : Prop where
  injective : Function.Injective (mulMap M N)
variable {M N}
protected def LinearDisjoint.mulMap (H : M.LinearDisjoint N) : M ⊗[R] N ≃ₗ[R] M * N :=
  LinearEquiv.ofInjective (M.mulMap N) H.injective ≪≫ₗ LinearEquiv.ofEq _ _ (mulMap_range M N)
@[simp]
theorem LinearDisjoint.val_mulMap_tmul (H : M.LinearDisjoint N) (m : M) (n : N) :
    (H.mulMap (m ⊗ₜ[R] n) : S) = m.1 * n.1 := rfl
@[nontriviality]
theorem LinearDisjoint.of_subsingleton [Subsingleton R] : M.LinearDisjoint N := by
  haveI : Subsingleton S := Module.subsingleton R S
  exact ⟨Function.injective_of_subsingleton _⟩
theorem linearDisjoint_op :
    M.LinearDisjoint N ↔ (equivOpposite.symm (MulOpposite.op N)).LinearDisjoint
      (equivOpposite.symm (MulOpposite.op M)) := by
  simp only [linearDisjoint_iff, mulMap_op, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.comp_injective, EquivLike.injective_comp]
alias ⟨LinearDisjoint.op, LinearDisjoint.of_op⟩ := linearDisjoint_op
theorem LinearDisjoint.symm_of_commute (H : M.LinearDisjoint N)
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : N.LinearDisjoint M := by
  rw [linearDisjoint_iff, mulMap_comm_of_commute M N hc]
  exact ((TensorProduct.comm R N M).toEquiv.injective_comp _).2 H.injective
theorem linearDisjoint_comm_of_commute
    (hc : ∀ (m : M) (n : N), Commute m.1 n.1) : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩
namespace LinearDisjoint
variable (M N)
theorem of_basis_left' {ι : Type*} (m : Basis ι R M)
    (H : Function.Injective (mulLeftMap N m)) : M.LinearDisjoint N := by
  classical simp_rw [mulLeftMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_rTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩
theorem of_basis_right' {ι : Type*} (n : Basis ι R N)
    (H : Function.Injective (mulRightMap M n)) : M.LinearDisjoint N := by
  classical simp_rw [mulRightMap_eq_mulMap_comp, ← Basis.coe_repr_symm,
    ← LinearEquiv.coe_lTensor, LinearEquiv.comp_coe, LinearMap.coe_comp,
    LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩
theorem of_basis_mul' {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : Function.Injective (Finsupp.linearCombination R fun i : κ × ι ↦ (m i.1 * n i.2 : S))) :
    M.LinearDisjoint N := by
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := TensorProduct.congr m.repr n.repr
  let i := mulMap M N ∘ₗ (i0.trans i1.symm).toLinearMap
  have : i = Finsupp.linearCombination R fun i : κ × ι ↦ (m i.1 * n i.2 : S) := by
    ext x
    simp [i, i0, i1, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  simp_rw [← this, i, LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.injective_comp] at H
  exact ⟨H⟩
theorem bot_left : (⊥ : Submodule R S).LinearDisjoint N :=
  ⟨Function.injective_of_subsingleton _⟩
theorem bot_right : M.LinearDisjoint (⊥ : Submodule R S) :=
  ⟨Function.injective_of_subsingleton _⟩
theorem one_left : (1 : Submodule R S).LinearDisjoint N := by
  rw [linearDisjoint_iff, ← Algebra.toSubmodule_bot, mulMap_one_left_eq]
  exact N.injective_subtype.comp N.lTensorOne.injective
theorem one_right : M.LinearDisjoint (1 : Submodule R S) := by
  rw [linearDisjoint_iff, ← Algebra.toSubmodule_bot, mulMap_one_right_eq]
  exact M.injective_subtype.comp M.rTensorOne.injective
theorem of_linearDisjoint_fg_left
    (H : ∀ M' : Submodule R S, M' ≤ M → M'.FG → M'.LinearDisjoint N) :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy ↦ by
  obtain ⟨M', hM, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_left_of_finite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H M' hM hFG).injective (by simp [← mulMap_comp_rTensor _ hM, hx', hy', hxy])
theorem of_linearDisjoint_fg_right
    (H : ∀ N' : Submodule R S, N' ≤ N → N'.FG → M.LinearDisjoint N') :
    M.LinearDisjoint N := (linearDisjoint_iff _ _).2 fun x y hxy ↦ by
  obtain ⟨N', hN, hFG, h⟩ :=
    TensorProduct.exists_finite_submodule_right_of_finite' {x, y} (Set.toFinite _)
  rw [Module.Finite.iff_fg] at hFG
  obtain ⟨x', hx'⟩ := h (show x ∈ {x, y} by simp)
  obtain ⟨y', hy'⟩ := h (show y ∈ {x, y} by simp)
  rw [← hx', ← hy']; congr
  exact (H N' hN hFG).injective (by simp [← mulMap_comp_lTensor _ hN, hx', hy', hxy])
theorem of_linearDisjoint_fg
    (H : ∀ (M' N' : Submodule R S), M' ≤ M → N' ≤ N → M'.FG → N'.FG → M'.LinearDisjoint N') :
    M.LinearDisjoint N :=
  of_linearDisjoint_fg_left _ _ fun _ hM hM' ↦
    of_linearDisjoint_fg_right _ _ fun _ hN hN' ↦ H _ _ hM hN hM' hN'
end LinearDisjoint
end Semiring
section CommSemiring
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M N : Submodule R S}
theorem LinearDisjoint.symm (H : M.LinearDisjoint N) : N.LinearDisjoint M :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _
theorem linearDisjoint_comm : M.LinearDisjoint N ↔ N.LinearDisjoint M :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩
end CommSemiring
section Ring
namespace LinearDisjoint
variable [CommRing R] [Ring S] [Algebra R S]
variable (M N : Submodule R S)
variable {M N} in
theorem linearIndependent_left_of_flat (H : M.LinearDisjoint N) [Module.Flat R N]
    {ι : Type*} {m : ι → M} (hm : LinearIndependent R m) : LinearMap.ker (mulLeftMap N m) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulLeftMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hm
  exact H.injective.comp (Module.Flat.rTensor_preserves_injective_linearMap (M := N) _ hm)
theorem of_basis_left {ι : Type*} (m : Basis ι R M)
    (H : LinearMap.ker (mulLeftMap N m) = ⊥) : M.LinearDisjoint N := by
  letI : AddCommGroup (ι →₀ N) := Finsupp.instAddCommGroup
  exact of_basis_left' M N m (LinearMap.ker_eq_bot.1 H)
variable {M N} in
theorem linearIndependent_right_of_flat (H : M.LinearDisjoint N) [Module.Flat R M]
    {ι : Type*} {n : ι → N} (hn : LinearIndependent R n) : LinearMap.ker (mulRightMap M n) = ⊥ := by
  refine LinearMap.ker_eq_bot_of_injective ?_
  classical simp_rw [mulRightMap_eq_mulMap_comp, LinearMap.coe_comp, LinearEquiv.coe_coe,
    ← Function.comp_assoc, EquivLike.injective_comp]
  rw [LinearIndependent] at hn
  exact H.injective.comp (Module.Flat.lTensor_preserves_injective_linearMap (M := M) _ hn)
theorem of_basis_right {ι : Type*} (n : Basis ι R N)
    (H : LinearMap.ker (mulRightMap M n) = ⊥) : M.LinearDisjoint N := by
  letI : AddCommGroup (ι →₀ M) := Finsupp.instAddCommGroup
  exact of_basis_right' M N n (LinearMap.ker_eq_bot.1 H)
variable {M N} in
theorem linearIndependent_mul_of_flat_left (H : M.LinearDisjoint N) [Module.Flat R M]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.rTensor (ι →₀ R) (Finsupp.linearCombination R m)
  let i2 := LinearMap.lTensor M (Finsupp.linearCombination R n)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h2 : Function.Injective i2 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.linearCombination R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h
variable {M N} in
theorem linearIndependent_mul_of_flat_right (H : M.LinearDisjoint N) [Module.Flat R N]
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rw [LinearIndependent] at hm hn ⊢
  let i0 := (finsuppTensorFinsupp' R κ ι).symm
  let i1 := LinearMap.lTensor (κ →₀ R) (Finsupp.linearCombination R n)
  let i2 := LinearMap.rTensor N (Finsupp.linearCombination R m)
  let i := mulMap M N ∘ₗ i2 ∘ₗ i1 ∘ₗ i0.toLinearMap
  have h1 : Function.Injective i1 := Module.Flat.lTensor_preserves_injective_linearMap _ hn
  have h2 : Function.Injective i2 := Module.Flat.rTensor_preserves_injective_linearMap _ hm
  have h : Function.Injective i := H.injective.comp h2 |>.comp h1 |>.comp i0.injective
  have : i = Finsupp.linearCombination R fun i ↦ (m i.1).1 * (n i.2).1 := by
    ext x
    simp [i, i0, i1, i2, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  rwa [this] at h
variable {M N} in
theorem linearIndependent_mul_of_flat (H : M.LinearDisjoint N)
    (hf : Module.Flat R M ∨ Module.Flat R N)
    {κ ι : Type*} {m : κ → M} {n : ι → N} (hm : LinearIndependent R m)
    (hn : LinearIndependent R n) : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1 := by
  rcases hf with _ | _
  · exact H.linearIndependent_mul_of_flat_left hm hn
  · exact H.linearIndependent_mul_of_flat_right hm hn
theorem of_basis_mul {κ ι : Type*} (m : Basis κ R M) (n : Basis ι R N)
    (H : LinearIndependent R fun (i : κ × ι) ↦ (m i.1).1 * (n i.2).1) : M.LinearDisjoint N := by
  rw [LinearIndependent] at H
  exact of_basis_mul' M N m n H
variable {M N} in
theorem of_le_left_of_flat (H : M.LinearDisjoint N) {M' : Submodule R S}
    (h : M' ≤ M) [Module.Flat R N] : M'.LinearDisjoint N := by
  let i := mulMap M N ∘ₗ (inclusion h).rTensor N
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.rTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M' N := by ext; simp [i]
  exact ⟨this ▸ hi⟩
variable {M N} in
theorem of_le_right_of_flat (H : M.LinearDisjoint N) {N' : Submodule R S}
    (h : N' ≤ N) [Module.Flat R M] : M.LinearDisjoint N' := by
  let i := mulMap M N ∘ₗ (inclusion h).lTensor M
  have hi : Function.Injective i := H.injective.comp <|
    Module.Flat.lTensor_preserves_injective_linearMap _ <| inclusion_injective h
  have : i = mulMap M N' := by ext; simp [i]
  exact ⟨this ▸ hi⟩
variable {M N} in
theorem of_le_of_flat_right (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R N] [Module.Flat R M'] :
    M'.LinearDisjoint N' := (H.of_le_left_of_flat hm).of_le_right_of_flat hn
variable {M N} in
theorem of_le_of_flat_left (H : M.LinearDisjoint N) {M' N' : Submodule R S}
    (hm : M' ≤ M) (hn : N' ≤ N) [Module.Flat R M] [Module.Flat R N'] :
    M'.LinearDisjoint N' := (H.of_le_right_of_flat hn).of_le_left_of_flat hm
theorem of_left_le_one_of_flat (h : M ≤ 1) [Module.Flat R N] :
    M.LinearDisjoint N := (one_left N).of_le_left_of_flat h
theorem of_right_le_one_of_flat (h : N ≤ 1) [Module.Flat R M] :
    M.LinearDisjoint N := (one_right M).of_le_right_of_flat h
section not_linearIndependent_pair
variable {M N}
section
variable (H : M.LinearDisjoint N)
include H
section
variable [Nontrivial R]
theorem not_linearIndependent_pair_of_commute_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let n : Fin 2 → N := (inclusion inf_le_right) ∘ ![a, b]
  have hn : LinearIndependent R n := h.map' _ (ker_inclusion _ _ _)
  letI : AddCommGroup (Fin 2 →₀ M) := Finsupp.instAddCommGroup
  let m : Fin 2 →₀ M := .single 0 ⟨b.1, b.2.1⟩ - .single 1 ⟨a.1, a.2.1⟩
  have hm : mulRightMap M n m = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.linearIndependent_right_of_flat hn, mem_bot] at hm
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, m] at hm
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hm
  exact h.ne_zero 0 hm.2
theorem not_linearIndependent_pair_of_commute_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := fun h ↦ by
  let m : Fin 2 → M := (inclusion inf_le_left) ∘ ![a, b]
  have hm : LinearIndependent R m := h.map' _ (ker_inclusion _ _ _)
  letI : AddCommGroup (Fin 2 →₀ N) := Finsupp.instAddCommGroup
  let n : Fin 2 →₀ N := .single 0 ⟨b.1, b.2.2⟩ - .single 1 ⟨a.1, a.2.2⟩
  have hn : mulLeftMap N m n = 0 := by simp [m, n, show _ * _ = _ * _ from hc]
  rw [← LinearMap.mem_ker, H.linearIndependent_left_of_flat hm, mem_bot] at hn
  simp only [Fin.isValue, sub_eq_zero, Finsupp.single_eq_single_iff, zero_ne_one, Subtype.mk.injEq,
    SetLike.coe_eq_coe, false_and, false_or, n] at hn
  repeat rw [AddSubmonoid.mk_eq_zero, ZeroMemClass.coe_eq_zero] at hn
  exact h.ne_zero 0 hn.2
theorem not_linearIndependent_pair_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) (hc : Commute a.1 b.1) : ¬LinearIndependent R ![a, b] := by
  rcases hf with _ | _
  · exact H.not_linearIndependent_pair_of_commute_of_flat_left a b hc
  · exact H.not_linearIndependent_pair_of_commute_of_flat_right a b hc
end
theorem rank_inf_le_one_of_commute_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 := by
  nontriviality R
  refine _root_.rank_le fun s h ↦ ?_
  by_contra hs
  rw [not_le, ← Fintype.card_coe, Fintype.one_lt_card_iff_nontrivial] at hs
  obtain ⟨a, b, hab⟩ := hs.exists_pair_ne
  refine H.not_linearIndependent_pair_of_commute_of_flat hf a.1 b.1 (hc a.1 b.1) ?_
  have := h.comp ![a, b] fun i j hij ↦ by
    fin_cases i <;> fin_cases j
    · rfl
    · simp [hab] at hij
    · simp [hab.symm] at hij
    · rfl
  convert this
  ext i
  fin_cases i <;> simp
theorem rank_inf_le_one_of_commute_of_flat_left [Module.Flat R M]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inl ‹_›) hc
theorem rank_inf_le_one_of_commute_of_flat_right [Module.Flat R N]
    (hc : ∀ (m n : ↥(M ⊓ N)), Commute m.1 n.1) : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat (Or.inr ‹_›) hc
end
theorem rank_le_one_of_commute_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M]
    (hc : ∀ (m n : M), Commute m.1 n.1) : Module.rank R M ≤ 1 := by
  rw [← inf_of_le_left (le_refl M)] at hc ⊢
  exact H.rank_inf_le_one_of_commute_of_flat_left hc
end not_linearIndependent_pair
end LinearDisjoint
end Ring
section CommRing
namespace LinearDisjoint
variable [CommRing R] [CommRing S] [Algebra R S]
variable (M N : Submodule R S)
section not_linearIndependent_pair
variable {M N}
section
variable (H : M.LinearDisjoint N)
include H
section
variable [Nontrivial R]
theorem not_linearIndependent_pair_of_flat_left [Module.Flat R M]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_left a b (mul_comm _ _)
theorem not_linearIndependent_pair_of_flat_right [Module.Flat R N]
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat_right a b (mul_comm _ _)
theorem not_linearIndependent_pair_of_flat (hf : Module.Flat R M ∨ Module.Flat R N)
    (a b : ↥(M ⊓ N)) : ¬LinearIndependent R ![a, b] :=
  H.not_linearIndependent_pair_of_commute_of_flat hf a b (mul_comm _ _)
end
theorem rank_inf_le_one_of_flat (hf : Module.Flat R M ∨ Module.Flat R N) :
    Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat hf fun _ _ ↦ mul_comm _ _
theorem rank_inf_le_one_of_flat_left [Module.Flat R M] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_left fun _ _ ↦ mul_comm _ _
theorem rank_inf_le_one_of_flat_right [Module.Flat R N] : Module.rank R ↥(M ⊓ N) ≤ 1 :=
  H.rank_inf_le_one_of_commute_of_flat_right fun _ _ ↦ mul_comm _ _
end
theorem rank_le_one_of_flat_of_self (H : M.LinearDisjoint M) [Module.Flat R M] :
    Module.rank R M ≤ 1 :=
  H.rank_le_one_of_commute_of_flat_of_self fun _ _ ↦ mul_comm _ _
end not_linearIndependent_pair
end LinearDisjoint
end CommRing
end Submodule