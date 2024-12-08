import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.Flat.Algebra
suppress_compilation
universe u v
variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]
open TensorProduct
namespace AdicCompletion
private
def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    ext n
    simp [mul_smul (r.val n)]
@[simp]
private lemma ofTensorProductBil_apply_apply (r : AdicCompletion I R) (x : M) :
    ((AdicCompletion.ofTensorProductBil I M) r) x = r • (of I M) x :=
  rfl
def ofTensorProduct : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift (ofTensorProductBil I M)
@[simp]
lemma ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  simp [ofTensorProduct]
variable {M} in
lemma ofTensorProduct_naturality (f : M →ₗ[R] N) :
    map I f ∘ₗ ofTensorProduct I M =
      ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp
section PiFintype
variable (ι : Type*)
section DecidableEq
variable [Fintype ι] [DecidableEq ι]
private lemma piEquivOfFintype_comp_ofTensorProduct_eq :
    piEquivOfFintype I (fun _ : ι ↦ R) ∘ₗ ofTensorProduct I (ι → R) =
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  ext i j k
  suffices h : (if j = i then 1 else 0) = (if j = i then 1 else 0 : AdicCompletion I R).val k by
    simpa [Pi.single_apply, -smul_eq_mul, -Algebra.id.smul_eq_mul]
  split <;> simp only [smul_eq_mul, val_zero, val_one]
private lemma ofTensorProduct_eq :
    ofTensorProduct I (ι → R) = (piEquivOfFintype I (ι := ι) (fun _ : ι ↦ R)).symm.toLinearMap ∘ₗ
      (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).toLinearMap := by
  rw [← piEquivOfFintype_comp_ofTensorProduct_eq I ι, ← LinearMap.comp_assoc]
  simp
private def ofTensorProductInvOfPiFintype :
    AdicCompletion I (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (ι → R) :=
  letI f := piEquivOfFintype I (fun _ : ι ↦ R)
  letI g := (TensorProduct.piScalarRight R (AdicCompletion I R) (AdicCompletion I R) ι).symm
  f.trans g
private lemma ofTensorProductInvOfPiFintype_comp_ofTensorProduct :
    ofTensorProductInvOfPiFintype I ι ∘ₗ ofTensorProduct I (ι → R) = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, LinearMap.comp_assoc, piEquivOfFintype_comp_ofTensorProduct_eq]
  simp
private lemma ofTensorProduct_comp_ofTensorProductInvOfPiFintype :
    ofTensorProduct I (ι → R) ∘ₗ ofTensorProductInvOfPiFintype I ι = LinearMap.id := by
  dsimp only [ofTensorProductInvOfPiFintype]
  rw [LinearEquiv.coe_trans, ofTensorProduct_eq, LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp
def ofTensorProductEquivOfPiFintype :
    AdicCompletion I R ⊗[R] (ι → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (ι → R) :=
  LinearEquiv.ofLinear
    (ofTensorProduct I (ι → R))
    (ofTensorProductInvOfPiFintype I ι)
    (ofTensorProduct_comp_ofTensorProductInvOfPiFintype I ι)
    (ofTensorProductInvOfPiFintype_comp_ofTensorProduct I ι)
end DecidableEq
lemma ofTensorProduct_bijective_of_pi_of_fintype [Finite ι] :
    Function.Bijective (ofTensorProduct I (ι → R)) := by
  classical
  cases nonempty_fintype ι
  exact EquivLike.bijective (ofTensorProductEquivOfPiFintype I ι)
end PiFintype
lemma ofTensorProduct_surjective_of_finite [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := map I p ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hf : Function.Surjective f := by
    simp only [hfg, LinearMap.coe_comp, g]
    apply Function.Surjective.comp
    · exact AdicCompletion.map_surjective I hp
    · exact (ofTensorProduct_bijective_of_pi_of_fintype I (Fin n)).surjective
  exact Function.Surjective.of_comp hf
section Noetherian
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]
open CategoryTheory
section
variable {ι : Type} (f : (ι → R) →ₗ[R] M)
private
def lTensorKerIncl : AdicCompletion I R ⊗[R] LinearMap.ker f →ₗ[AdicCompletion I R]
    AdicCompletion I R ⊗[R] (ι → R) :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.ker f).subtype
private def lTensorf :
    AdicCompletion I R ⊗[R] (ι → R) →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] M :=
  AlgebraTensorModule.map LinearMap.id f
variable (hf : Function.Surjective f)
section
include hf
private lemma tens_exact : Function.Exact (lTensorKerIncl I M f) (lTensorf I M f) :=
  lTensor_exact (AdicCompletion I R) (f.exact_subtype_ker_map) hf
private lemma tens_surj : Function.Surjective (lTensorf I M f) :=
  LinearMap.lTensor_surjective (AdicCompletion I R) hf
private lemma adic_exact [IsNoetherianRing R] [Fintype ι] :
    Function.Exact (map I (LinearMap.ker f).subtype) (map I f) :=
  map_exact (Submodule.injective_subtype _) (f.exact_subtype_ker_map) hf
private lemma adic_surj : Function.Surjective (map I f) :=
  map_surjective I hf
end
private instance : AddCommGroup (AdicCompletion I R ⊗[R] (LinearMap.ker f)) :=
  inferInstance
private def firstRow : ComposableArrows (ModuleCat (AdicCompletion I R)) 4 :=
  ComposableArrows.mk₄
    (ModuleCat.ofHom <| lTensorKerIncl I M f)
    (ModuleCat.ofHom <| lTensorf I M f)
    (ModuleCat.ofHom (0 : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] PUnit))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))
private def secondRow : ComposableArrows (ModuleCat (AdicCompletion I R)) 4 :=
  ComposableArrows.mk₄
    (ModuleCat.ofHom (map I <| (LinearMap.ker f).subtype))
    (ModuleCat.ofHom (map I f))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))
include hf
private lemma firstRow_exact : (firstRow I M f).Exact where
  zero k _ := match k with
    | 0 => (tens_exact I M f hf).linearMap_comp_eq_zero
    | 1 => LinearMap.zero_comp _
    | 2 => LinearMap.zero_comp 0
  exact k _ := by
    rw [ShortComplex.moduleCat_exact_iff]
    match k with
    | 0 => intro x hx; exact (tens_exact I M f hf x).mp hx
    | 1 => intro x _; exact (tens_surj I M f hf) x
    | 2 => intro _ _; exact ⟨0, rfl⟩
private lemma secondRow_exact [Fintype ι] [IsNoetherianRing R] : (secondRow I M f).Exact where
  zero k _ := match k with
    | 0 => (adic_exact I M f hf).linearMap_comp_eq_zero
    | 1 => LinearMap.zero_comp (map I f)
    | 2 => LinearMap.zero_comp 0
  exact k _ := by
    rw [ShortComplex.moduleCat_exact_iff]
    match k with
    | 0 => intro x hx; exact (adic_exact I M f hf x).mp hx
    | 1 => intro x _; exact (adic_surj I M f hf) x
    | 2 => intro _ _; exact ⟨0, rfl⟩
private def firstRowToSecondRow : firstRow I M f ⟶ secondRow I M f :=
  ComposableArrows.homMk₄
    (ModuleCat.ofHom (ofTensorProduct I (LinearMap.ker f)))
    (ModuleCat.ofHom (ofTensorProduct I (ι → R)))
    (ModuleCat.ofHom (ofTensorProduct I M))
    (ModuleCat.ofHom 0)
    (ModuleCat.ofHom 0)
    (ofTensorProduct_naturality I <| (LinearMap.ker f).subtype).symm
    (ofTensorProduct_naturality I f).symm
    rfl
    rfl
private lemma ofTensorProduct_iso [Fintype ι] [IsNoetherianRing R] :
    IsIso (ModuleCat.ofHom (ofTensorProduct I M)) := by
  refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (firstRow_exact I M f hf) (secondRow_exact I M f hf) (firstRowToSecondRow I M f) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.epi_of_surjective
    exact ofTensorProduct_surjective_of_finite I (LinearMap.ker f)
  · apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ofTensorProduct_bijective_of_pi_of_fintype I ι
  · show IsIso (ModuleCat.ofHom 0)
    apply Limits.isIso_of_isTerminal
      <;> exact Limits.IsZero.isTerminal (ModuleCat.isZero_of_subsingleton _)
  · apply ConcreteCategory.mono_of_injective
    intro x y _
    rfl
private
lemma ofTensorProduct_bijective_of_map_from_fin [Fintype ι] [IsNoetherianRing R] :
    Function.Bijective (ofTensorProduct I M) := by
  have : IsIso (ModuleCat.ofHom (ofTensorProduct I M)) :=
    ofTensorProduct_iso I M f hf
  exact ConcreteCategory.bijective_of_isIso (ModuleCat.ofHom (ofTensorProduct I M))
end
variable [IsNoetherianRing R]
theorem ofTensorProduct_bijective_of_finite_of_isNoetherian
    [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf
def ofTensorProductEquivOfFiniteNoetherian [Module.Finite R M] :
    AdicCompletion I R ⊗[R] M ≃ₗ[AdicCompletion I R] AdicCompletion I M :=
  LinearEquiv.ofBijective (ofTensorProduct I M)
    (ofTensorProduct_bijective_of_finite_of_isNoetherian I M)
@[simp]
lemma ofTensorProductEquivOfFiniteNoetherian_apply [Module.Finite R M]
    (x : AdicCompletion I R ⊗[R] M) :
    ofTensorProductEquivOfFiniteNoetherian I M x = ofTensorProduct I M x :=
  rfl
@[simp]
lemma ofTensorProductEquivOfFiniteNoetherian_symm_of
    [Module.Finite R M] (x : M) :
    (ofTensorProductEquivOfFiniteNoetherian I M).symm ((of I M) x) = 1 ⊗ₜ x := by
  have h : (of I M) x = ofTensorProductEquivOfFiniteNoetherian I M (1 ⊗ₜ x) := by
    simp
  rw [h, LinearEquiv.symm_apply_apply]
section
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {N : Type u} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
variable [Module.Finite R M] [Module.Finite R N]
lemma tensor_map_id_left_eq_map :
    (AlgebraTensorModule.map LinearMap.id f) =
      (ofTensorProductEquivOfFiniteNoetherian I N).symm.toLinearMap ∘ₗ
      map I f ∘ₗ
      (ofTensorProductEquivOfFiniteNoetherian I M).toLinearMap := by
  erw [ofTensorProduct_naturality I f]
  ext x
  simp
variable {f}
lemma tensor_map_id_left_injective_of_injective (hf : Function.Injective f) :
    Function.Injective (AlgebraTensorModule.map LinearMap.id f :
        AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] N) := by
  rw [tensor_map_id_left_eq_map I f]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact map_injective I hf
end
instance flat_of_isNoetherian [IsNoetherianRing R] : Algebra.Flat R (AdicCompletion I R) where
  out := (Module.Flat.iff_lTensor_injective' R (AdicCompletion I R)).mpr <| fun J ↦
    tensor_map_id_left_injective_of_injective I (Submodule.injective_subtype J)
end Noetherian
end AdicCompletion