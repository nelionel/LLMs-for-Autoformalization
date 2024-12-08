import Mathlib.Algebra.DirectLimit
open TensorProduct Module Module.DirectLimit
variable {R : Type*} [CommRing R]
variable {ι : Type*}
variable [DecidableEq ι] [Preorder ι]
variable {G : ι → Type*}
variable [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
variable (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)
variable (M : Type*) [AddCommGroup M] [Module R M]
local notation M " ◁ " f => fun i j h ↦ LinearMap.lTensor M (f _ _ h)
local notation f " ▷ " N => fun i j h ↦ LinearMap.rTensor N (f _ _ h)
namespace TensorProduct
noncomputable def fromDirectLimit :
    DirectLimit (G · ⊗[R] M) (f ▷ M) →ₗ[R] DirectLimit G f ⊗[R] M :=
  DirectLimit.lift _ _ _ _ (fun _ ↦ (of _ _ _ _ _).rTensor M)
    fun _ _ _ x ↦ by refine x.induction_on ?_ ?_ ?_ <;> aesop
variable {M} in
@[simp] lemma fromDirectLimit_of_tmul {i : ι} (g : G i) (m : M) :
    fromDirectLimit f M (of _ _ _ _ i (g ⊗ₜ m)) = (of _ _ _ f i g) ⊗ₜ m :=
  lift_of (G := (G · ⊗[R] M)) _ _ (g ⊗ₜ m)
noncomputable def toDirectLimit : DirectLimit G f ⊗[R] M →ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) :=
  TensorProduct.lift <| DirectLimit.lift _ _ _ _
    (fun i ↦
      (TensorProduct.mk R _ _).compr₂ (of R ι _ (fun _i _j h ↦ (f _ _ h).rTensor M) i))
    fun _ _ _ g ↦ DFunLike.ext _ _ (of_f (G := (G · ⊗[R] M)) (x := g ⊗ₜ ·))
variable {M} in
@[simp] lemma toDirectLimit_tmul_of
    {i : ι} (g : G i) (m : M) :
    (toDirectLimit f M <| (of _ _ G f i g) ⊗ₜ m) = (of _ _ _ _ i (g ⊗ₜ m)) := by
  rw [toDirectLimit, lift.tmul, lift_of]
  rfl
variable [IsDirected ι (· ≤ ·)]
noncomputable def directLimitLeft :
    DirectLimit G f ⊗[R] M ≃ₗ[R] DirectLimit (G · ⊗[R] M) (f ▷ M) := by
  refine LinearEquiv.ofLinear (toDirectLimit f M) (fromDirectLimit f M) ?_ ?_
    <;> cases isEmpty_or_nonempty ι
  · ext; subsingleton
  · refine DFunLike.ext _ _ fun x ↦ x.induction_on fun i g ↦ g.induction_on ?_ ?_ ?_ <;> aesop
  · ext; subsingleton
  · exact ext (DFunLike.ext _ _ fun g ↦ DFunLike.ext _ _ fun _ ↦ g.induction_on <| by aesop)
@[simp] lemma directLimitLeft_tmul_of {i : ι} (g : G i) (m : M) :
    directLimitLeft f M (of _ _ _ _ _ g ⊗ₜ m) = of _ _ _ (f ▷ M) _ (g ⊗ₜ m) :=
  toDirectLimit_tmul_of f g m
@[simp] lemma directLimitLeft_symm_of_tmul {i : ι} (g : G i) (m : M) :
    (directLimitLeft f M).symm (of _ _ _ _ _ (g ⊗ₜ m)) = of _ _ _ f _ g ⊗ₜ m :=
  fromDirectLimit_of_tmul f g m
noncomputable def directLimitRight :
    M ⊗[R] DirectLimit G f ≃ₗ[R] DirectLimit (M ⊗[R] G ·) (M ◁ f) :=
  TensorProduct.comm _ _ _ ≪≫ₗ directLimitLeft f M ≪≫ₗ
    Module.DirectLimit.congr (fun _ ↦ TensorProduct.comm _ _ _)
      (fun i j h ↦ TensorProduct.ext <| DFunLike.ext _ _ <| by aesop)
@[simp] lemma directLimitRight_tmul_of {i : ι} (m : M) (g : G i) :
    directLimitRight f M (m ⊗ₜ of _ _ _ _ _ g) = of _ _ _ _ i (m ⊗ₜ g) := by
  simp [directLimitRight, congr_apply_of]
@[simp] lemma directLimitRight_symm_of_tmul {i : ι} (m : M) (g : G i) :
    (directLimitRight f M).symm (of _ _ _ _ _ (m ⊗ₜ g)) = m ⊗ₜ of _ _ _ f _ g := by
  simp [directLimitRight, congr_symm_apply_of]
end TensorProduct