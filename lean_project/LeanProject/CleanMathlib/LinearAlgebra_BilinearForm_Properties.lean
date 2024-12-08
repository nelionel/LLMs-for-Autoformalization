import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Dual
open LinearMap (BilinForm)
universe u v w
variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}
namespace LinearMap
namespace BilinForm
def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B
namespace IsRefl
theorem eq_zero (H : B.IsRefl) : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
protected theorem smul {α} [CommSemiring α] [Module α R] [SMulCommClass R α R]
    [NoZeroSMulDivisors α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp
end IsRefl
@[simp]
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl
@[simp]
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩
def IsSymm (B : BilinForm R M) : Prop := LinearMap.IsSymm B
namespace IsSymm
protected theorem eq (H : B.IsSymm) (x y : M) : B x y = B y x :=
  H x y
theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => H x y ▸ H1
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := fun x y => (congr_arg₂ (· + ·) (hB₁ x y) (hB₂ x y) : _)
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := fun x y => (congr_arg₂ Sub.sub (hB₁ x y) (hB₂ x y) : _)
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := fun x y =>
  congr_arg Neg.neg (hB x y)
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := fun x y =>
  congr_arg (a • ·) (hB x y)
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := fun x y => b x y
end IsSymm
@[simp]
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := fun _ _ => rfl
@[simp]
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩
theorem isSymm_iff_flip : B.IsSymm ↔ flipHom B = B :=
  (forall₂_congr fun _ _ => by exact eq_comm).trans BilinForm.ext_iff.symm
def IsAlt (B : BilinForm R M) : Prop := LinearMap.IsAlt B
namespace IsAlt
theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 := LinearMap.IsAlt.self_eq_zero H x
theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := LinearMap.IsAlt.neg H x y
theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := LinearMap.IsAlt.isRefl H
theorem eq_of_add_add_eq_zero [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0) :
    B a b = B b c := LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) : _).trans <| add_zero _
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg (a • ·) (hB x)).trans <| smul_zero _
end IsAlt
@[simp]
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl
@[simp]
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩
section LinearAdjoints
variable (B) (F : BilinForm R M)
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable (B' : BilinForm R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)
def IsAdjointPair :=
  ∀ ⦃x y⦄, B' (f x) y = B x (g y)
variable {B B' f f' g g'}
theorem IsAdjointPair.eq (h : IsAdjointPair B B' f g) : ∀ {x y}, B' (f x) y = B x (g y) :=
  @h
theorem isAdjointPair_iff_compLeft_eq_compRight (f g : Module.End R M) :
    IsAdjointPair B F f g ↔ F.compLeft f = B.compRight g := by
  constructor <;> intro h
  · ext x
    simp only [compLeft_apply, compRight_apply]
    apply h
  · intro x y
    rw [← compLeft_apply, ← compRight_apply]
    rw [h]
theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun x y => by
  simp only [BilinForm.zero_left, BilinForm.zero_right, LinearMap.zero_apply]
theorem isAdjointPair_id : IsAdjointPair B B 1 1 := fun _ _ => rfl
theorem IsAdjointPair.add (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x y => by
  rw [LinearMap.add_apply, LinearMap.add_apply, add_left, add_right, h, h']
variable {M₁' : Type*} [AddCommGroup M₁'] [Module R₁ M₁']
variable {B₁' : BilinForm R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}
theorem IsAdjointPair.sub (h : IsAdjointPair B₁ B₁' f₁ g₁) (h' : IsAdjointPair B₁ B₁' f₁' g₁') :
    IsAdjointPair B₁ B₁' (f₁ - f₁') (g₁ - g₁') := fun x y => by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, sub_left, sub_right, h, h']
variable {B₂' : BilinForm R M'} {f₂ : M →ₗ[R] M'} {g₂ : M' →ₗ[R] M}
theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B₂' f₂ g₂) :
    IsAdjointPair B B₂' (c • f₂) (c • g₂) := fun x y => by
  rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_left, smul_right, h]
variable {M'' : Type*} [AddCommMonoid M''] [Module R M'']
variable (B'' : BilinForm R M'')
theorem IsAdjointPair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B' B'' f' g') : IsAdjointPair B B'' (f'.comp f) (g.comp g') := fun x y => by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, h', h]
theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) := fun x y => by
  rw [LinearMap.mul_apply, LinearMap.mul_apply, h, h']
variable (B B' B₁ B₂) (F₂ : BilinForm R M)
def IsPairSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B F f f
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B₂ F₂ f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c
@[simp]
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f ∈ isPairSelfAdjointSubmodule B₂ F₂ ↔ IsPairSelfAdjoint B₂ F₂ f := Iff.rfl
theorem isPairSelfAdjoint_equiv (e : M' ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B₂ F₂ f ↔
      IsPairSelfAdjoint (B₂.comp ↑e ↑e) (F₂.comp ↑e ↑e) (e.symm.conj f) := by
  have hₗ : (F₂.comp ↑e ↑e).compLeft (e.symm.conj f) = (F₂.compLeft f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.symm_conj_apply]
  have hᵣ : (B₂.comp ↑e ↑e).compRight (e.symm.conj f) = (B₂.compRight f).comp ↑e ↑e := by
    ext
    simp [LinearEquiv.conj_apply]
  have he : Function.Surjective (⇑(↑e : M' →ₗ[R] M) : M' → M) := e.surjective
  show BilinForm.IsAdjointPair _ _ _ _ ↔ BilinForm.IsAdjointPair _ _ _ _
  rw [isAdjointPair_iff_compLeft_eq_compRight, isAdjointPair_iff_compLeft_eq_compRight, hᵣ,
    hₗ, comp_inj _ _ he he]
def IsSelfAdjoint (f : Module.End R M) :=
  IsAdjointPair B B f f
def IsSkewAdjoint (f : Module.End R₁ M₁) :=
  IsAdjointPair B₁ B₁ f (-f)
theorem isSkewAdjoint_iff_neg_self_adjoint (f : Module.End R₁ M₁) :
    B₁.IsSkewAdjoint f ↔ IsAdjointPair (-B₁) B₁ f f :=
  show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y) by
    simp only [LinearMap.neg_apply, BilinForm.neg_apply, BilinForm.neg_right]
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B
@[simp]
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f ∈ B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B₁) B₁
@[simp]
theorem mem_skewAdjointSubmodule (f : Module.End R₁ M₁) :
    f ∈ B₁.skewAdjointSubmodule ↔ B₁.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl
end LinearAdjoints
end BilinForm
namespace BilinForm
def Nondegenerate (B : BilinForm R M) : Prop :=
  ∀ m : M, (∀ n : M, B m n = 0) → m = 0
section
variable (R M)
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h m fun _ => rfl)
end
variable {M' : Type*}
variable [AddCommMonoid M'] [Module R M']
theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h
theorem Nondegenerate.congr {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate := fun m hm =>
  e.symm.map_eq_zero_iff.1 <|
    h (e.symm m) fun n => (congr_arg _ (e.symm_apply_apply n).symm).trans (hm (e n))
@[simp]
theorem nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩
theorem nondegenerate_iff_ker_eq_bot {B : BilinForm R M} :
    B.Nondegenerate ↔ LinearMap.ker B = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  constructor <;> intro h
  · refine fun m hm => h _ fun x => ?_
    rw [hm]
    rfl
  · intro m hm
    apply h
    ext x
    exact hm x
theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := nondegenerate_iff_ker_eq_bot.mp h
theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b _ ?_)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
section FiniteDimensional
variable [FiniteDimensional K V]
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
theorem toDual_def {B : BilinForm K V} (b : B.SeparatingLeft) {m n : V} : B.toDual b m n = B m n :=
  rfl
@[simp]
lemma apply_toDual_symm_apply {B : BilinForm K V} {hB : B.Nondegenerate}
    (f : Module.Dual K V) (v : V) :
    B ((B.toDual hB).symm f) v = f v := by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]
lemma Nondegenerate.flip {B : BilinForm K V} (hB : B.Nondegenerate) :
    B.flip.Nondegenerate := by
  intro x hx
  apply (Module.evalEquiv K V).injective
  ext f
  obtain ⟨y, rfl⟩ := (B.toDual hB).surjective f
  simpa using hx y
lemma nonDegenerateFlip_iff {B : BilinForm K V} :
    B.flip.Nondegenerate ↔ B.Nondegenerate := ⟨Nondegenerate.flip, Nondegenerate.flip⟩
end FiniteDimensional
section DualBasis
variable {ι : Type*} [DecidableEq ι] [Finite ι]
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := FiniteDimensional.of_fintype_basis b
  b.dualBasis.map (B.toDual hB).symm
@[simp]
theorem dualBasis_repr_apply
    (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  #adaptation_note
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, @toDual_def]
theorem apply_dualBasis_left (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := FiniteDimensional.of_fintype_basis b
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
theorem apply_dualBasis_right (B : BilinForm K V) (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym.eq, apply_dualBasis_left]
@[simp]
lemma dualBasis_dualBasis_flip [FiniteDimensional K V]
    (B : BilinForm K V) (hB : B.Nondegenerate) {ι : Type*}
    [Finite ι] [DecidableEq ι] (b : Basis ι K V) :
    B.dualBasis hB (B.flip.dualBasis hB.flip b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j ↦ ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]
@[simp]
lemma dualBasis_flip_dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    B.flip.dualBasis hB.flip (B.dualBasis hB b) = b :=
  dualBasis_dualBasis_flip _ hB.flip b
@[simp]
lemma dualBasis_dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (hB' : B.IsSymm) {ι}
    [Finite ι] [DecidableEq ι] [FiniteDimensional K V] (b : Basis ι K V) :
    B.dualBasis hB (B.dualBasis hB b) = b := by
  convert dualBasis_dualBasis_flip _ hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]
end DualBasis
section LinearAdjoints
variable [FiniteDimensional K V]
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁
theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B₁ v := by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply, DFunLike.coe_fn_eq]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]
@[simp]
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b
theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩
end LinearAdjoints
end BilinForm
end LinearMap