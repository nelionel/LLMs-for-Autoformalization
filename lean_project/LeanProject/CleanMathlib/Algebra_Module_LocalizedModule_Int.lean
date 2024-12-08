import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
variable {R : Type*} [CommSemiring R] {S : Submonoid R} {M : Type*} [AddCommMonoid M]
  [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')
open Function
namespace IsLocalizedModule
def IsInteger (x : M') : Prop :=
  x ∈ LinearMap.range f
lemma isInteger_zero : IsInteger f (0 : M') :=
  Submodule.zero_mem _
theorem isInteger_add {x y : M'} (hx : IsInteger f x) (hy : IsInteger f y) : IsInteger f (x + y) :=
  Submodule.add_mem _ hx hy
theorem isInteger_smul {a : R} {x : M'} (hx : IsInteger f x) : IsInteger f (a • x) := by
  rcases hx with ⟨x', hx⟩
  use a • x'
  rw [← hx, LinearMapClass.map_smul]
variable (S)
variable [IsLocalizedModule S f]
theorem exists_integer_multiple (x : M') : ∃ a : S, IsInteger f (a.val • x) :=
  let ⟨⟨Num, denom⟩, h⟩ := IsLocalizedModule.surj S f x
  ⟨denom, Set.mem_range.mpr ⟨Num, h.symm⟩⟩
theorem exist_integer_multiples {ι : Type*} (s : Finset ι) (g : ι → M') :
    ∃ b : S, ∀ i ∈ s, IsInteger f (b.val • g i) := by
  classical
  choose sec hsec using (fun i ↦ IsLocalizedModule.surj S f (g i))
  refine ⟨∏ i ∈ s, (sec i).2, fun i hi => ⟨?_, ?_⟩⟩
  · exact (∏ j ∈ s.erase i, (sec j).2) • (sec i).1
  · simp only [LinearMap.map_smul_of_tower, Submonoid.coe_finset_prod]
    rw [← hsec, ← mul_smul, Submonoid.smul_def]
    congr
    simp only [Submonoid.coe_mul, Submonoid.coe_finset_prod, mul_comm]
    rw [← Finset.prod_insert (f := fun i ↦ ((sec i).snd).val) (s.not_mem_erase i),
      Finset.insert_erase hi]
theorem exist_integer_multiples_of_finite {ι : Type*} [Finite ι] (g : ι → M') :
    ∃ b : S, ∀ i, IsInteger f ((b : R) • g i) := by
  cases nonempty_fintype ι
  obtain ⟨b, hb⟩ := exist_integer_multiples S f Finset.univ g
  exact ⟨b, fun i => hb i (Finset.mem_univ _)⟩
theorem exist_integer_multiples_of_finset (s : Finset M') :
    ∃ b : S, ∀ a ∈ s, IsInteger f ((b : R) • a) :=
  exist_integer_multiples S f s id
noncomputable def commonDenom {ι : Type*} (s : Finset ι) (g : ι → M') : S :=
  (exist_integer_multiples S f s g).choose
noncomputable def integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) : M :=
  ((exist_integer_multiples S f s g).choose_spec i i.prop).choose
@[simp]
theorem map_integerMultiple {ι : Type*} (s : Finset ι) (g : ι → M') (i : s) :
    f (integerMultiple S f s g i) = commonDenom S f s g • g i :=
  ((exist_integer_multiples S f s g).choose_spec _ i.prop).choose_spec
noncomputable def commonDenomOfFinset (s : Finset M') : S :=
  commonDenom S f s id
noncomputable def finsetIntegerMultiple [DecidableEq M] (s : Finset M') : Finset M :=
  s.attach.image fun t => integerMultiple S f s id t
open Pointwise
theorem finsetIntegerMultiple_image [DecidableEq M] (s : Finset M') :
    f '' finsetIntegerMultiple S f s = commonDenomOfFinset S f s • (s : Set M') := by
  delta finsetIntegerMultiple commonDenom
  rw [Finset.coe_image]
  ext
  constructor
  · rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩
    rw [map_integerMultiple]
    exact Set.mem_image_of_mem _ x.prop
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integerMultiple S f s id _⟩
theorem smul_mem_finsetIntegerMultiple_span [DecidableEq M] (x : M) (s : Finset M')
    (hx : f x ∈ Submodule.span R s) :
    ∃ (m : S), m • x ∈ Submodule.span R (IsLocalizedModule.finsetIntegerMultiple S f s) := by
  let y : S := IsLocalizedModule.commonDenomOfFinset S f s
  have hx₁ : (y : R) • (s : Set M') = f '' _ :=
    (IsLocalizedModule.finsetIntegerMultiple_image S f s).symm
  apply congrArg (Submodule.span R) at hx₁
  rw [Submodule.span_smul] at hx₁
  replace hx : _ ∈ y • Submodule.span R (s : Set M') := Set.smul_mem_smul_set hx
  erw [hx₁, ← f.map_smul, ← Submodule.map_span f] at hx
  obtain ⟨x', hx', hx''⟩ := hx
  obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp hx''
  use a * y
  convert (Submodule.span R
    (IsLocalizedModule.finsetIntegerMultiple S f s : Set M)).smul_mem
      a hx' using 1
  convert ha.symm using 1
  simp only [Submonoid.coe_subtype, Submonoid.smul_def]
  erw [← smul_smul]
end IsLocalizedModule