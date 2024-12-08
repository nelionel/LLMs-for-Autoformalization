import Mathlib.RingTheory.HahnSeries.Multiplication
assert_not_exists Cardinal
noncomputable section
variable {Γ : Type*} [PartialOrder Γ] {R : Type*} {V W : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
abbrev HVertexOperator (Γ : Type*) [PartialOrder Γ] (R : Type*) [CommRing R]
    (V : Type*) (W : Type*) [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] :=
  V →ₗ[R] (HahnModule Γ R W)
namespace HVertexOperator
section Coeff
open HahnModule
@[ext]
theorem ext (A B : HVertexOperator Γ R V W) (h : ∀ v : V, A v = B v) :
    A = B := LinearMap.ext h
@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.ext := ext
@[simps]
def coeff (A : HVertexOperator Γ R V W) (n : Γ) : V →ₗ[R] W where
  toFun v := ((of R).symm (A v)).coeff n
  map_add' _ _ := by simp
  map_smul' _ _ := by
    simp only [map_smul, RingHom.id_apply, of_symm_smul, HahnSeries.smul_coeff]
@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.coeff := coeff
theorem coeff_isPWOsupport (A : HVertexOperator Γ R V W) (v : V) :
    ((of R).symm (A v)).coeff.support.IsPWO :=
  ((of R).symm (A v)).isPWO_support'
@[deprecated (since := "2024-06-18")]
alias _root_.VertexAlg.coeff_isPWOsupport := coeff_isPWOsupport
@[ext]
theorem coeff_inj : Function.Injective (coeff : HVertexOperator Γ R V W → Γ → (V →ₗ[R] W)) := by
  intro _ _ h
  ext v n
  exact congrFun (congrArg DFunLike.coe (congrFun h n)) v
@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.coeff_inj := coeff_inj
@[simps]
def of_coeff (f : Γ → V →ₗ[R] W)
    (hf : ∀(x : V), (Function.support (f · x)).IsPWO) : HVertexOperator Γ R V W where
  toFun x := (of R) { coeff := fun g => f g x, isPWO_support' := hf x }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
@[deprecated (since := "2024-06-18")] alias _root_.VertexAlg.HetVertexOperator.of_coeff := of_coeff
end Coeff
section Products
variable {Γ Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [OrderedCancelAddCommMonoid Γ'] {R : Type*}
  [CommRing R] {U V W : Type*} [AddCommGroup U] [Module R U][AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] (A : HVertexOperator Γ R V W) (B : HVertexOperator Γ' R U V)
open HahnModule
@[simps]
def compHahnSeries (u : U) : HahnSeries Γ' (HahnSeries Γ W) where
  coeff g' := A (coeff B g' u)
  isPWO_support' := by
    refine Set.IsPWO.mono (((of R).symm (B u)).isPWO_support') ?_
    simp_all only [coeff_apply, Function.support_subset_iff, ne_eq, Function.mem_support]
    intro g' hg' hAB
    apply hg'
    simp_rw [hAB]
    simp_all only [map_zero, HahnSeries.zero_coeff, not_true_eq_false]
@[simp]
theorem compHahnSeries_add (u v : U) :
    compHahnSeries A B (u + v) = compHahnSeries A B u + compHahnSeries A B v := by
  ext
  simp only [compHahnSeries_coeff, map_add, coeff_apply, HahnSeries.add_coeff', Pi.add_apply]
  rw [← HahnSeries.add_coeff]
@[simp]
theorem compHahnSeries_smul (r : R) (u : U) :
    compHahnSeries A B (r • u) = r • compHahnSeries A B u := by
  ext
  simp only [compHahnSeries_coeff, LinearMapClass.map_smul, coeff_apply, HahnSeries.smul_coeff]
  rw [← HahnSeries.smul_coeff]
@[simps]
def comp : HVertexOperator (Γ' ×ₗ Γ) R U W where
  toFun u := HahnModule.of R (HahnSeries.ofIterate (compHahnSeries A B u))
  map_add' := by
    intro u v
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries_add, Equiv.symm_apply_apply,
      HahnModule.of_symm_add, HahnSeries.add_coeff', Pi.add_apply]
  map_smul' := by
    intro r x
    ext g
    simp only [HahnSeries.ofIterate, compHahnSeries_smul, HahnSeries.smul_coeff,
      compHahnSeries_coeff, coeff_apply, Equiv.symm_apply_apply, RingHom.id_apply, of_symm_smul]
@[simp]
theorem comp_coeff (g : Γ' ×ₗ Γ) :
    (comp A B).coeff g = A.coeff (ofLex g).2 ∘ₗ B.coeff (ofLex g).1 := by
  rfl
end Products
end HVertexOperator