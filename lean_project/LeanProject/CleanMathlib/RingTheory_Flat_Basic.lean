import Mathlib.Algebra.DirectSum.Finsupp
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Finiteness.TensorProduct
universe v' u v w
namespace Module
open Function (Surjective)
open LinearMap Submodule TensorProduct DirectSum
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
@[mk_iff] class Flat : Prop where
  out : ∀ ⦃I : Ideal R⦄ (_ : I.FG),
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
namespace Flat
variable {R} in
instance instSubalgebraToSubmodule {S : Type v} [Ring S] [Algebra R S]
    (A : Subalgebra R S) [Flat R A] : Flat R (Subalgebra.toSubmodule A) := ‹Flat R A›
instance self (R : Type u) [CommRing R] : Flat R R :=
  ⟨by
    intro I _
    rw [← Equiv.injective_comp (TensorProduct.rid R I).symm.toEquiv]
    convert Subtype.coe_injective using 1
    ext x
    simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, rid_symm_apply, comp_apply, mul_one,
      lift.tmul, Submodule.subtype_apply, Algebra.id.smul_eq_mul, lsmul_apply]⟩
lemma iff_rTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (rTensor M I.subtype) := by
  simp [flat_iff, ← lid_comp_rTensor]
theorem iff_rTensor_injective' :
    Flat R M ↔ ∀ I : Ideal R, Function.Injective (rTensor M I.subtype) := by
  rewrite [Flat.iff_rTensor_injective]
  refine ⟨fun h I => ?_, fun h I _ => h I⟩
  rewrite [injective_iff_map_eq_zero]
  intro x hx₀
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rewrite [← rTensor_comp_apply] at hx₀
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx₀, LinearMap.map_zero]
@[deprecated (since := "2024-03-29")]
alias lTensor_inj_iff_rTensor_inj := LinearMap.lTensor_inj_iff_rTensor_inj
theorem iff_lTensor_injective :
    Module.Flat R M ↔ ∀ ⦃I : Ideal R⦄ (_ : I.FG), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using Module.Flat.iff_rTensor_injective R M
theorem iff_lTensor_injective' :
    Module.Flat R M ↔ ∀ (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using Module.Flat.iff_rTensor_injective' R M
variable (N : Type w) [AddCommGroup N] [Module R N]
lemma of_retract [f : Flat R M] (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id) :
    Flat R N := by
  rw [iff_rTensor_injective] at *
  intro I hI
  have h₁ : Function.Injective (lTensor R i) := by
    apply Function.RightInverse.injective (g := (lTensor R r))
    intro x
    rw [← LinearMap.comp_apply, ← lTensor_comp, h]
    simp
  rw [← Function.Injective.of_comp_iff h₁ (rTensor N I.subtype), ← LinearMap.coe_comp]
  rw [LinearMap.lTensor_comp_rTensor, ← LinearMap.rTensor_comp_lTensor]
  rw [LinearMap.coe_comp, Function.Injective.of_comp_iff (f hI)]
  apply Function.RightInverse.injective (g := lTensor _ r)
  intro x
  rw [← LinearMap.comp_apply, ← lTensor_comp, h]
  simp
lemma of_linearEquiv [f : Flat R M] (e : N ≃ₗ[R] M) : Flat R N := by
  have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by simp
  exact of_retract _ _ _ e.toLinearMap e.symm.toLinearMap h
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ => of_linearEquiv R M N e.symm, fun _ => of_linearEquiv R N M e⟩
instance ulift [Module.Flat R M] : Module.Flat R (ULift.{v'} M) :=
  of_linearEquiv R M (ULift.{v'} M) ULift.moduleEquiv
lemma of_ulift [Module.Flat R (ULift.{v'} M)] : Module.Flat R M :=
  of_linearEquiv R (ULift.{v'} M) M ULift.moduleEquiv.symm
instance shrink [Small.{v'} M] [Module.Flat R M] : Module.Flat R (Shrink.{v'} M) :=
  of_linearEquiv R M (Shrink.{v'} M) (Shrink.linearEquiv M R)
lemma of_shrink [Small.{v'} M] [Module.Flat R (Shrink.{v'} M)] :
    Module.Flat R M :=
  of_linearEquiv R (Shrink.{v'} M) M (Shrink.linearEquiv M R).symm
instance directSum (ι : Type v) (M : ι → Type w) [(i : ι) → AddCommGroup (M i)]
    [(i : ι) → Module R (M i)] [F : (i : ι) → (Flat R (M i))] : Flat R (⨁ i, M i) := by
  haveI := Classical.decEq ι
  rw [iff_rTensor_injective]
  intro I hI
  letI : ∀ i, AddCommGroup (I ⊗[R] M i) := inferInstance
  rw [← Equiv.comp_injective _ (TensorProduct.lid R (⨁ i, M i)).toEquiv]
  set η₁ := TensorProduct.lid R (⨁ i, M i)
  set η := fun i ↦ TensorProduct.lid R (M i)
  set φ := fun i ↦ rTensor (M i) I.subtype
  set π := fun i ↦ component R ι (fun j ↦ M j) i
  set ψ := (TensorProduct.directSumRight R {x // x ∈ I} (fun i ↦ M i)).symm.toLinearMap with psi_def
  set ρ := rTensor (⨁ i, M i) I.subtype
  set τ := (fun i ↦ component R ι (fun j ↦ ({x // x ∈ I} ⊗[R] (M j))) i)
  rw [← Equiv.injective_comp (TensorProduct.directSumRight _ _ _).symm.toEquiv]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [LinearEquiv.coe_toEquiv, ← LinearEquiv.coe_coe, ← LinearMap.coe_comp]
  rw [← psi_def, injective_iff_map_eq_zero ((η₁.comp ρ).comp ψ)]
  have h₁ : ∀ (i : ι), (π i).comp ((η₁.comp ρ).comp ψ) = (η i).comp ((φ i).comp (τ i)) := by
    intro i
    apply DirectSum.linearMap_ext
    intro j
    apply TensorProduct.ext'
    intro a m
    simp only [ρ, ψ, φ, η, η₁, coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      directSumRight_symm_lof_tmul, rTensor_tmul, Submodule.coe_subtype, lid_tmul, map_smul]
    rw [DirectSum.component.of, DirectSum.component.of]
    by_cases h₂ : j = i
    · subst j; simp
    · simp [h₂]
  intro a ha; rw [DirectSum.ext_iff R]; intro i
  have f := LinearMap.congr_arg (f := (π i)) ha
  erw [LinearMap.congr_fun (h₁ i) a] at f
  rw [(map_zero (π i) : (π i) 0 = (0 : M i))] at f
  have h₂ := F i
  rw [iff_rTensor_injective] at h₂
  have h₃ := h₂ hI
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, EmbeddingLike.map_eq_zero_iff,
    h₃, LinearMap.map_eq_zero_iff] at f
  simp [f]
open scoped Classical in
instance finsupp (ι : Type v) : Flat R (ι →₀ R) :=
  of_linearEquiv R _ _ (finsuppLEquivDirectSum R R ι)
instance of_free [Free R M] : Flat R M := of_linearEquiv R _ _ (Free.repr R M)
lemma of_projective_surjective (ι : Type w) [Projective R M] (p : (ι →₀ R) →ₗ[R] M)
    (hp : Surjective p) : Flat R M := by
  have h := Module.projective_lifting_property p (LinearMap.id) hp
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he
instance of_projective [h : Projective R M] : Flat R M := by
  rw [Module.projective_def'] at h
  cases h with
    | _ e he => exact of_retract R _ _ _ _ he
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap :
    Module.Injective R (CharacterModule M) ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.rTensor M) := by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl
variable {R M N}
theorem iff_characterModule_baer : Flat R M ↔ Module.Baer R (CharacterModule M) := by
  simp_rw [iff_rTensor_injective', Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall]; rfl
theorem iff_characterModule_injective [Small.{v} R] :
    Flat R M ↔ Module.Injective R (CharacterModule M) :=
  iff_characterModule_baer.trans Module.Baer.iff_injective
theorem rTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [h : Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.rTensor M) :=
  rTensor_injective_iff_lcomp_surjective.2 ((iff_characterModule_baer.1 h).extension_property _ hL)
@[deprecated (since := "2024-03-29")]
alias preserves_injective_linearMap := rTensor_preserves_injective_linearMap
instance {S} [CommRing S] [Algebra R S] [Module S M] [IsScalarTower R S M] [Flat S M] [Flat R N] :
    Flat S (M ⊗[R] N) :=
  (iff_rTensor_injective' _ _).mpr fun I ↦ by
    simpa [AlgebraTensorModule.rTensor_tensor] using
      rTensor_preserves_injective_linearMap (.restrictScalars R <| rTensor M I.subtype)
      (rTensor_preserves_injective_linearMap _ I.injective_subtype)
example [Flat R M] [Flat R N] : Flat R (M ⊗[R] N) := inferInstance
theorem lTensor_preserves_injective_linearMap {N' : Type*} [AddCommGroup N'] [Module R N']
    [Flat R M] (L : N →ₗ[R] N') (hL : Function.Injective L) :
    Function.Injective (L.lTensor M) :=
  (L.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap L hL)
variable (R M) in
lemma iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) :=
  (Module.Flat.equiv_iff R M (Shrink.{v'} M) (Shrink.linearEquiv M R).symm).trans <|
    iff_characterModule_injective.trans <|
      (injective_characterModule_iff_rTensor_preserves_injective_linearMap R (Shrink.{v'} M)).trans
        <| forall₅_congr <| fun N N' _ _ _ => forall₃_congr <| fun _ f _ =>
  let frmu := f.rTensor (Shrink.{v'} M)
  let frm := f.rTensor M
  let emn := TensorProduct.congr (LinearEquiv.refl R N) (Shrink.linearEquiv M R)
  let emn' := TensorProduct.congr (LinearEquiv.refl R N') (Shrink.linearEquiv M R)
  have h : emn'.toLinearMap.comp frmu = frm.comp emn.toLinearMap := TensorProduct.ext rfl
  (EquivLike.comp_injective frmu emn').symm.trans <|
    (congrArg Function.Injective (congrArg DFunLike.coe h)).to_iff.trans <|
      EquivLike.injective_comp emn frm
variable (R M) in
lemma iff_rTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.rTensor M) :=
  iff_rTensor_preserves_injective_linearMap'.{max u v} R M
variable (R M) in
lemma iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (L : N →ₗ[R] N'), Function.Injective L → Function.Injective (L.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]
variable (R M) in
lemma iff_lTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N') (_ : Function.Injective f), Function.Injective (f.lTensor M) :=
  iff_lTensor_preserves_injective_linearMap'.{max u v} R M
variable (M) in
lemma lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [show g = ι.comp π from rfl, lTensor_comp]
    exact exact1.comp_injective _ (lTensor_preserves_injective_linearMap ι <| by
      simpa [ι, - Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.lTensor_exact _ (fun x => by simp [π]) Quotient.mk''_surjective
variable (M) in
lemma rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [show g = ι.comp π from rfl, rTensor_comp]
    exact exact1.comp_injective _ (rTensor_preserves_injective_linearMap ι <| by
      simpa [ι, - Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.rTensor_exact M (fun x => by simp [π]) Quotient.mk''_surjective
theorem iff_lTensor_exact' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ => lTensor_exact M, fun H => iff_lTensor_preserves_injective_linearMap' R M |>.mpr
    fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp  hx
theorem iff_lTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) :=
  iff_lTensor_exact'.{max u v}
theorem iff_rTensor_exact' [Small.{v'} R] [Small.{v'} M] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ => rTensor_exact M, fun H => iff_rTensor_preserves_injective_linearMap' R M |>.mpr
    fun N' N'' _ _ _ _ L hL => LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) => ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x => by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp hx
theorem iff_rTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) :=
  iff_rTensor_exact'.{max u v}
variable (p : Submodule R M) (q : Submodule R N)
theorem tensorProduct_mapIncl_injective_of_right
    [Flat R M] [Flat R q] : Function.Injective (mapIncl p q) := by
  rw [mapIncl, ← lTensor_comp_rTensor]
  exact (lTensor_preserves_injective_linearMap _ q.injective_subtype).comp
    (rTensor_preserves_injective_linearMap _ p.injective_subtype)
theorem tensorProduct_mapIncl_injective_of_left
    [Flat R p] [Flat R N] : Function.Injective (mapIncl p q) := by
  rw [mapIncl, ← rTensor_comp_lTensor]
  exact (rTensor_preserves_injective_linearMap _ p.injective_subtype).comp
    (lTensor_preserves_injective_linearMap _ q.injective_subtype)
end Flat
end Module