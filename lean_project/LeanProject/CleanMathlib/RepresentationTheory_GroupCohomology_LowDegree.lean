import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RepresentationTheory.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Invariants
universe v u
noncomputable section
open CategoryTheory Limits Representation
variable {k G : Type u} [CommRing k] [Group G] (A : Rep k G)
namespace groupCohomology
section Cochains
def zeroCochainsLequiv : (inhomogeneousCochains A).X 0 ≃ₗ[k] A :=
  LinearEquiv.funUnique (Fin 0 → G) k A
def oneCochainsLequiv : (inhomogeneousCochains A).X 1 ≃ₗ[k] G → A :=
  LinearEquiv.funCongrLeft k A (Equiv.funUnique (Fin 1) G).symm
def twoCochainsLequiv : (inhomogeneousCochains A).X 2 ≃ₗ[k] G × G → A :=
  LinearEquiv.funCongrLeft k A <| (piFinTwoEquiv fun _ => G).symm
def threeCochainsLequiv : (inhomogeneousCochains A).X 3 ≃ₗ[k] G × G × G → A :=
  LinearEquiv.funCongrLeft k A <| ((Fin.consEquiv _).symm.trans
    ((Equiv.refl G).prodCongr (piFinTwoEquiv fun _ => G))).symm
end Cochains
section Differentials
@[simps]
def dZero : A →ₗ[k] G → A where
  toFun m g := A.ρ g m - m
  map_add' x y := funext fun g => by simp only [map_add, add_sub_add_comm]; rfl
  map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_sub]
theorem dZero_ker_eq_invariants : LinearMap.ker (dZero A) = invariants A.ρ := by
  ext x
  simp only [LinearMap.mem_ker, mem_invariants, ← @sub_eq_zero _ _ _ x, funext_iff]
  rfl
@[simp] theorem dZero_eq_zero [A.IsTrivial] : dZero A = 0 := by
  ext
  simp only [dZero_apply, apply_eq_self, sub_self, LinearMap.zero_apply, Pi.zero_apply]
@[simps]
def dOne : (G → A) →ₗ[k] G × G → A where
  toFun f g := A.ρ g.1 (f g.2) - f (g.1 * g.2) + f g.1
  map_add' x y := funext fun g => by dsimp; rw [map_add, add_add_add_comm, add_sub_add_comm]
  map_smul' r x := funext fun g => by dsimp; rw [map_smul, smul_add, smul_sub]
@[simps]
def dTwo : (G × G → A) →ₗ[k] G × G × G → A where
  toFun f g :=
    A.ρ g.1 (f (g.2.1, g.2.2)) - f (g.1 * g.2.1, g.2.2) + f (g.1, g.2.1 * g.2.2) - f (g.1, g.2.1)
  map_add' x y :=
    funext fun g => by
      dsimp
      rw [map_add, add_sub_add_comm (A.ρ _ _), add_sub_assoc, add_sub_add_comm, add_add_add_comm,
        add_sub_assoc, add_sub_assoc]
  map_smul' r x := funext fun g => by dsimp; simp only [map_smul, smul_add, smul_sub]
theorem dZero_comp_eq : dZero A ∘ₗ (zeroCochainsLequiv A) =
    oneCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 0 1 := by
  ext x y
  show A.ρ y (x default) - x default = _ + ({0} : Finset _).sum _
  simp_rw [Fin.val_eq_zero, zero_add, pow_one, neg_smul, one_smul,
    Finset.sum_singleton, sub_eq_add_neg]
  rcongr i <;> exact Fin.elim0 i
theorem dOne_comp_eq : dOne A ∘ₗ oneCochainsLequiv A =
    twoCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 1 2 := by
  ext x y
  show A.ρ y.1 (x _) - x _ + x _ =  _ + _
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, zero_add, pow_one, neg_smul, one_smul, Fin.val_one,
    Nat.one_add, neg_one_sq, sub_eq_add_neg, add_assoc]
  rcongr i <;> rw [Subsingleton.elim i 0] <;> rfl
theorem dTwo_comp_eq :
    dTwo A ∘ₗ twoCochainsLequiv A = threeCochainsLequiv A ∘ₗ (inhomogeneousCochains A).d 2 3 := by
  ext x y
  show A.ρ y.1 (x _) - x _ + x _ - x _ = _ + _
  dsimp
  rw [Fin.sum_univ_three]
  simp only [sub_eq_add_neg, add_assoc, Fin.val_zero, zero_add, pow_one, neg_smul,
    one_smul, Fin.val_one, Fin.val_two, pow_succ' (-1 : k) 2, neg_sq, Nat.one_add, one_pow, mul_one]
  rcongr i <;> fin_cases i <;> rfl
theorem dOne_comp_dZero : dOne A ∘ₗ dZero A = 0 := by
  ext x g
  simp only [LinearMap.coe_comp, Function.comp_apply, dOne_apply A, dZero_apply A, map_sub,
    map_mul, LinearMap.mul_apply, sub_sub_sub_cancel_left, sub_add_sub_cancel, sub_self]
  rfl
theorem dTwo_comp_dOne : dTwo A ∘ₗ dOne A = 0 := by
  show ModuleCat.ofHom (dOne A) ≫ ModuleCat.ofHom (dTwo A) = _
  have h1 : _ ≫ ModuleCat.ofHom (dOne A) = _ ≫ _ := congr_arg ModuleCat.ofHom (dOne_comp_eq A)
  have h2 : _ ≫ ModuleCat.ofHom (dTwo A) = _ ≫ _ := congr_arg ModuleCat.ofHom (dTwo_comp_eq A)
  simp only [← LinearEquiv.toModuleIso_hom] at h1 h2
  simp only [(Iso.eq_inv_comp _).2 h2, (Iso.eq_inv_comp _).2 h1,
    Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.d_comp_d_assoc, zero_comp, comp_zero]
end Differentials
section Cocycles
def oneCocycles : Submodule k (G → A) := LinearMap.ker (dOne A)
def twoCocycles : Submodule k (G × G → A) := LinearMap.ker (dTwo A)
variable {A}
instance : FunLike (oneCocycles A) G A := ⟨Subtype.val, Subtype.val_injective⟩
@[simp]
theorem oneCocycles.coe_mk (f : G → A) (hf) : ((⟨f, hf⟩ : oneCocycles A) : G → A) = f := rfl
@[simp]
theorem oneCocycles.val_eq_coe (f : oneCocycles A) : f.1 = f := rfl
@[ext]
theorem oneCocycles_ext {f₁ f₂ : oneCocycles A} (h : ∀ g : G, f₁ g = f₂ g) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ h
theorem mem_oneCocycles_def (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, A.ρ g (f h) - f (g * h) + f g = 0 :=
  LinearMap.mem_ker.trans <| by
    rw [funext_iff]
    simp only [dOne_apply, Pi.zero_apply, Prod.forall]
theorem mem_oneCocycles_iff (f : G → A) :
    f ∈ oneCocycles A ↔ ∀ g h : G, f (g * h) = A.ρ g (f h) + f g := by
  simp_rw [mem_oneCocycles_def, sub_add_eq_add_sub, sub_eq_zero, eq_comm]
@[simp] theorem oneCocycles_map_one (f : oneCocycles A) : f 1 = 0 := by
  have := (mem_oneCocycles_def f).1 f.2 1 1
  simpa only [map_one, LinearMap.one_apply, mul_one, sub_self, zero_add] using this
@[simp] theorem oneCocycles_map_inv (f : oneCocycles A) (g : G) :
    A.ρ g (f g⁻¹) = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← oneCocycles_map_one f, ← mul_inv_cancel g,
    (mem_oneCocycles_iff f).1 f.2 g g⁻¹]
theorem oneCocycles_map_mul_of_isTrivial [A.IsTrivial] (f : oneCocycles A) (g h : G) :
    f (g * h) = f g + f h := by
  rw [(mem_oneCocycles_iff f).1 f.2, apply_eq_self A.ρ g (f h), add_comm]
theorem mem_oneCocycles_of_addMonoidHom [A.IsTrivial] (f : Additive G →+ A) :
    f ∘ Additive.ofMul ∈ oneCocycles A :=
  (mem_oneCocycles_iff _).2 fun g h => by
    simp only [Function.comp_apply, ofMul_mul, map_add,
      oneCocycles_map_mul_of_isTrivial, apply_eq_self A.ρ g (f (Additive.ofMul h)),
      add_comm (f (Additive.ofMul g))]
variable (A)
@[simps] def oneCocyclesLequivOfIsTrivial [hA : A.IsTrivial] :
    oneCocycles A ≃ₗ[k] Additive G →+ A where
  toFun f :=
    { toFun := f ∘ Additive.toMul
      map_zero' := oneCocycles_map_one f
      map_add' := oneCocycles_map_mul_of_isTrivial f }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    { val := f
      property := mem_oneCocycles_of_addMonoidHom f }
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
variable {A}
instance : FunLike (twoCocycles A) (G × G) A := ⟨Subtype.val, Subtype.val_injective⟩
@[simp]
theorem twoCocycles.coe_mk (f : G × G → A) (hf) : ((⟨f, hf⟩ : twoCocycles A) : G × G → A) = f := rfl
@[simp]
theorem twoCocycles.val_eq_coe (f : twoCocycles A) : f.1 = f := rfl
@[ext]
theorem twoCocycles_ext {f₁ f₂ : twoCocycles A} (h : ∀ g h : G, f₁ (g, h) = f₂ (g, h)) : f₁ = f₂ :=
  DFunLike.ext f₁ f₂ (Prod.forall.mpr h)
theorem mem_twoCocycles_def (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      A.ρ g (f (h, j)) - f (g * h, j) + f (g, h * j) - f (g, h) = 0 :=
  LinearMap.mem_ker.trans <| by
    rw [funext_iff]
    simp only [dTwo_apply, Prod.mk.eta, Pi.zero_apply, Prod.forall]
theorem mem_twoCocycles_iff (f : G × G → A) :
    f ∈ twoCocycles A ↔ ∀ g h j : G,
      f (g * h, j) + f (g, h) =
        A.ρ g (f (h, j)) + f (g, h * j) := by
  simp_rw [mem_twoCocycles_def, sub_eq_zero, sub_add_eq_add_sub, sub_eq_iff_eq_add, eq_comm,
    add_comm (f (_ * _, _))]
theorem twoCocycles_map_one_fst (f : twoCocycles A) (g : G) :
    f (1, g) = f (1, 1) := by
  have := ((mem_twoCocycles_iff f).1 f.2 1 1 g).symm
  simpa only [map_one, LinearMap.one_apply, one_mul, add_right_inj, this]
theorem twoCocycles_map_one_snd (f : twoCocycles A) (g : G) :
    f (g, 1) = A.ρ g (f (1, 1)) := by
  have := (mem_twoCocycles_iff f).1 f.2 g 1 1
  simpa only [mul_one, add_left_inj, this]
lemma twoCocycles_ρ_map_inv_sub_map_inv (f : twoCocycles A) (g : G) :
    A.ρ g (f (g⁻¹, g)) - f (g, g⁻¹)
      = f (1, 1) - f (g, 1) := by
  have := (mem_twoCocycles_iff f).1 f.2 g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, twoCocycles_map_one_fst _ g]
    at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm
end Cocycles
section Coboundaries
def oneCoboundaries : Submodule k (oneCocycles A) :=
  LinearMap.range ((dZero A).codRestrict (oneCocycles A) fun c =>
    LinearMap.ext_iff.1 (dOne_comp_dZero A) c)
def twoCoboundaries : Submodule k (twoCocycles A) :=
  LinearMap.range ((dOne A).codRestrict (twoCocycles A) fun c =>
    LinearMap.ext_iff.1 (dTwo_comp_dOne.{u} A) c)
variable {A}
def oneCoboundariesOfMemRange {f : G → A} (h : f ∈ LinearMap.range (dZero A)) :
    oneCoboundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dOne_comp_dZero A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩
theorem oneCoboundaries_of_mem_range_apply {f : G → A} (h : f ∈ LinearMap.range (dZero A)) :
    (oneCoboundariesOfMemRange h).1.1 = f := rfl
def oneCoboundariesOfEq {f : G → A} {x : A} (hf : ∀ g, A.ρ g x - x = f g) :
    oneCoboundaries A :=
  oneCoboundariesOfMemRange ⟨x, funext hf⟩
theorem oneCoboundariesOfEq_apply {f : G → A} {x : A} (hf : ∀ g, A.ρ g x - x = f g) :
    (oneCoboundariesOfEq hf).1.1 = f := rfl
theorem mem_range_of_mem_oneCoboundaries {f : oneCocycles A} (h : f ∈ oneCoboundaries A) :
    f.1 ∈ LinearMap.range (dZero A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩
theorem oneCoboundaries_eq_bot_of_isTrivial (A : Rep k G) [A.IsTrivial] :
    oneCoboundaries A = ⊥ := by
  simp_rw [oneCoboundaries, dZero_eq_zero]
  exact LinearMap.range_eq_bot.2 rfl
theorem mem_oneCoboundaries_iff (f : oneCocycles A) : f ∈ oneCoboundaries A ↔
    ∃ x : A, ∀ g : G, A.ρ g x - x = f g := exists_congr fun x ↦ by
  simpa only [LinearMap.codRestrict, dZero, LinearMap.coe_mk, AddHom.coe_mk] using
    groupCohomology.oneCocycles_ext_iff
def twoCoboundariesOfMemRange {f : G × G → A} (h : f ∈ LinearMap.range (dOne A)) :
    twoCoboundaries A :=
  ⟨⟨f, LinearMap.range_le_ker_iff.2 (dTwo_comp_dOne A) h⟩,
    by rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩⟩
theorem twoCoboundariesOfMemRange_apply {f : G × G → A} (h : f ∈ LinearMap.range (dOne A)) :
    (twoCoboundariesOfMemRange h).1.1 = f := rfl
def twoCoboundariesOfEq {f : G × G → A} {x : G → A}
    (hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)) :
    twoCoboundaries A :=
  twoCoboundariesOfMemRange ⟨x, funext fun g ↦ hf g.1 g.2⟩
theorem twoCoboundariesOfEq_apply {f : G × G → A} {x : G → A}
    (hf : ∀ g h, A.ρ g (x h) - x (g * h) + x g = f (g, h)) :
    (twoCoboundariesOfEq hf).1.1 = f := rfl
theorem mem_range_of_mem_twoCoboundaries {f : twoCocycles A} (h : f ∈ twoCoboundaries A) :
    (twoCocycles A).subtype f ∈ LinearMap.range (dOne A) := by
  rcases h with ⟨x, rfl⟩; exact ⟨x, rfl⟩
theorem mem_twoCoboundaries_iff (f : twoCocycles A) : f ∈ twoCoboundaries A ↔
    ∃ x : G → A, ∀ g h : G, A.ρ g (x h) - x (g * h) + x g = f (g, h) := exists_congr fun x ↦ by
  simpa only [LinearMap.codRestrict, dOne, LinearMap.coe_mk, AddHom.coe_mk] using
    groupCohomology.twoCocycles_ext_iff
end Coboundaries
section IsCocycle
section
variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
def IsOneCocycle (f : G → A) : Prop := ∀ g h : G, f (g * h) = g • f h + f g
def IsTwoCocycle (f : G × G → A) : Prop :=
  ∀ g h j : G, f (g * h, j) + f (g, h) = g • (f (h, j)) + f (g, h * j)
end
section
variable {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]
theorem map_one_of_isOneCocycle {f : G → A} (hf : IsOneCocycle f) :
    f 1 = 0 := by
  simpa only [mul_one, one_smul, self_eq_add_right] using hf 1 1
theorem map_one_fst_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, add_right_inj] using (hf 1 1 g).symm
theorem map_one_snd_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, add_left_inj] using hf g 1 1
end
section
variable {G A : Type*} [Group G] [AddCommGroup A] [MulAction G A]
@[scoped simp] theorem map_inv_of_isOneCocycle {f : G → A} (hf : IsOneCocycle f) (g : G) :
    g • f g⁻¹ = - f g := by
  rw [← add_eq_zero_iff_eq_neg, ← map_one_of_isOneCocycle hf, ← mul_inv_cancel g, hf g g⁻¹]
theorem smul_map_inv_sub_map_inv_of_isTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) (g : G) :
    g • f (g⁻¹, g) - f (g, g⁻¹) = f (1, 1) - f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isTwoCocycle hf g] at this
  exact sub_eq_sub_iff_add_eq_add.2 this.symm
end
end IsCocycle
section IsCoboundary
variable {G A : Type*} [Mul G] [AddCommGroup A] [SMul G A]
def IsOneCoboundary (f : G → A) : Prop := ∃ x : A, ∀ g : G, g • x - x = f g
def IsTwoCoboundary (f : G × G → A) : Prop :=
  ∃ x : G → A, ∀ g h : G, g • x h - x (g * h) + x g = f (g, h)
end IsCoboundary
section ofDistribMulAction
variable {k G A : Type u} [CommRing k] [Group G] [AddCommGroup A] [Module k A]
  [DistribMulAction G A] [SMulCommClass G k A]
def oneCocyclesOfIsOneCocycle {f : G → A} (hf : IsOneCocycle f) :
    oneCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_oneCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩
theorem isOneCocycle_of_oneCocycles (f : oneCocycles (Rep.ofDistribMulAction k G A)) :
    IsOneCocycle (A := A) f := (mem_oneCocycles_iff f).1 f.2
def oneCoboundariesOfIsOneCoboundary {f : G → A} (hf : IsOneCoboundary f) :
    oneCoboundaries (Rep.ofDistribMulAction k G A) :=
  oneCoboundariesOfMemRange ⟨hf.choose, funext hf.choose_spec⟩
theorem isOneCoboundary_of_oneCoboundaries (f : oneCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsOneCoboundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_oneCoboundaries f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩
def twoCocyclesOfIsTwoCocycle {f : G × G → A} (hf : IsTwoCocycle f) :
    twoCocycles (Rep.ofDistribMulAction k G A) :=
  ⟨f, (mem_twoCocycles_iff (A := Rep.ofDistribMulAction k G A) f).2 hf⟩
theorem isTwoCocycle_of_twoCocycles (f : twoCocycles (Rep.ofDistribMulAction k G A)) :
    IsTwoCocycle (A := A) f := (mem_twoCocycles_iff f).1 f.2
def twoCoboundariesOfIsTwoCoboundary {f : G × G → A} (hf : IsTwoCoboundary f) :
    twoCoboundaries (Rep.ofDistribMulAction k G A) :=
  twoCoboundariesOfMemRange (⟨hf.choose,funext fun g ↦ hf.choose_spec g.1 g.2⟩)
theorem isTwoCoboundary_of_twoCoboundaries (f : twoCoboundaries (Rep.ofDistribMulAction k G A)) :
    IsTwoCoboundary (A := A) f.1.1 := by
  rcases mem_range_of_mem_twoCoboundaries f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => funext_iff.1 hx (g, h)⟩
end ofDistribMulAction
section IsMulCocycle
section
variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]
def IsMulOneCocycle (f : G → M) : Prop := ∀ g h : G, f (g * h) = g • f h * f g
def IsMulTwoCocycle (f : G × G → M) : Prop :=
  ∀ g h j : G, f (g * h, j) * f (g, h) = g • (f (h, j)) * f (g, h * j)
end
section
variable {G M : Type*} [Monoid G] [CommGroup M] [MulAction G M]
theorem map_one_of_isMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) :
    f 1 = 1 := by
  simpa only [mul_one, one_smul, self_eq_mul_right] using hf 1 1
theorem map_one_fst_of_isMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    f (1, g) = f (1, 1) := by
  simpa only [one_smul, one_mul, mul_one, mul_right_inj] using (hf 1 1 g).symm
theorem map_one_snd_of_isMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    f (g, 1) = g • f (1, 1) := by
  simpa only [mul_one, mul_left_inj] using hf g 1 1
end
section
variable {G M : Type*} [Group G] [CommGroup M] [MulAction G M]
@[scoped simp] theorem map_inv_of_isMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) (g : G) :
    g • f g⁻¹ = (f g)⁻¹ := by
  rw [← mul_eq_one_iff_eq_inv, ← map_one_of_isMulOneCocycle hf, ← mul_inv_cancel g, hf g g⁻¹]
theorem smul_map_inv_div_map_inv_of_isMulTwoCocycle
    {f : G × G → M} (hf : IsMulTwoCocycle f) (g : G) :
    g • f (g⁻¹, g) / f (g, g⁻¹) = f (1, 1) / f (g, 1) := by
  have := hf g g⁻¹ g
  simp only [mul_inv_cancel, inv_mul_cancel, map_one_fst_of_isMulTwoCocycle hf g] at this
  exact div_eq_div_iff_mul_eq_mul.2 this.symm
end
end IsMulCocycle
section IsMulCoboundary
variable {G M : Type*} [Mul G] [CommGroup M] [SMul G M]
def IsMulOneCoboundary (f : G → M) : Prop := ∃ x : M, ∀ g : G, g • x / x = f g
def IsMulTwoCoboundary (f : G × G → M) : Prop :=
  ∃ x : G → M, ∀ g h : G, g • x h / x (g * h) * x g = f (g, h)
end IsMulCoboundary
section ofMulDistribMulAction
variable {G M : Type} [Group G] [CommGroup M] [MulDistribMulAction G M]
def oneCocyclesOfIsMulOneCocycle {f : G → M} (hf : IsMulOneCocycle f) :
    oneCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_oneCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩
theorem isMulOneCocycle_of_oneCocycles (f : oneCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCocycle (M := M) (Additive.toMul ∘ f) := (mem_oneCocycles_iff f).1 f.2
def oneCoboundariesOfIsMulOneCoboundary {f : G → M} (hf : IsMulOneCoboundary f) :
    oneCoboundaries (Rep.ofMulDistribMulAction G M) :=
  oneCoboundariesOfMemRange (f := Additive.ofMul ∘ f) ⟨hf.choose, funext hf.choose_spec⟩
theorem isMulOneCoboundary_of_oneCoboundaries
    (f : oneCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulOneCoboundary (M := M) (Additive.ofMul ∘ f.1.1) := by
  rcases mem_range_of_mem_oneCoboundaries f.2 with ⟨x, hx⟩
  exact ⟨x, by rw [← hx]; intro g; rfl⟩
def twoCocyclesOfIsMulTwoCocycle {f : G × G → M} (hf : IsMulTwoCocycle f) :
    twoCocycles (Rep.ofMulDistribMulAction G M) :=
  ⟨Additive.ofMul ∘ f, (mem_twoCocycles_iff (A := Rep.ofMulDistribMulAction G M) f).2 hf⟩
theorem isMulTwoCocycle_of_twoCocycles (f : twoCocycles (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCocycle (M := M) (Additive.toMul ∘ f) := (mem_twoCocycles_iff f).1 f.2
def twoCoboundariesOfIsMulTwoCoboundary {f : G × G → M} (hf : IsMulTwoCoboundary f) :
    twoCoboundaries (Rep.ofMulDistribMulAction G M) :=
  twoCoboundariesOfMemRange ⟨hf.choose, funext fun g ↦ hf.choose_spec g.1 g.2⟩
theorem isMulTwoCoboundary_of_twoCoboundaries
    (f : twoCoboundaries (Rep.ofMulDistribMulAction G M)) :
    IsMulTwoCoboundary (M := M) (Additive.toMul ∘ f.1.1) := by
  rcases mem_range_of_mem_twoCoboundaries f.2 with ⟨x, hx⟩
  exact ⟨x, fun g h => funext_iff.1 hx (g, h)⟩
end ofMulDistribMulAction
section Cohomology
abbrev H0 := A.ρ.invariants
abbrev H1 := oneCocycles A ⧸ oneCoboundaries A
def H1_π : oneCocycles A →ₗ[k] H1 A := (oneCoboundaries A).mkQ
abbrev H2 := twoCocycles A ⧸ twoCoboundaries A
def H2_π : twoCocycles A →ₗ[k] H2 A := (twoCoboundaries A).mkQ
end Cohomology
section H0
def H0LequivOfIsTrivial [A.IsTrivial] :
    H0 A ≃ₗ[k] A := LinearEquiv.ofTop _ (invariants_eq_top A.ρ)
@[simp] theorem H0LequivOfIsTrivial_eq_subtype [A.IsTrivial] :
    H0LequivOfIsTrivial A = A.ρ.invariants.subtype := rfl
theorem H0LequivOfIsTrivial_apply [A.IsTrivial] (x : H0 A) :
    H0LequivOfIsTrivial A x = x := rfl
@[simp] theorem H0LequivOfIsTrivial_symm_apply [A.IsTrivial] (x : A) :
    (H0LequivOfIsTrivial A).symm x = x := rfl
end H0
section H1
def H1LequivOfIsTrivial [A.IsTrivial] :
    H1 A ≃ₗ[k] Additive G →+ A :=
  (Submodule.quotEquivOfEqBot _ (oneCoboundaries_eq_bot_of_isTrivial A)).trans
    (oneCocyclesLequivOfIsTrivial A)
theorem H1LequivOfIsTrivial_comp_H1_π [A.IsTrivial] :
    (H1LequivOfIsTrivial A).comp (H1_π A) = oneCocyclesLequivOfIsTrivial A := by
  ext; rfl
@[simp] theorem H1LequivOfIsTrivial_H1_π_apply_apply
    [A.IsTrivial] (f : oneCocycles A) (x : Additive G) :
    H1LequivOfIsTrivial A (H1_π A f) x = f x.toMul := rfl
@[simp] theorem H1LequivOfIsTrivial_symm_apply [A.IsTrivial] (f : Additive G →+ A) :
    (H1LequivOfIsTrivial A).symm f = H1_π A ((oneCocyclesLequivOfIsTrivial A).symm f) :=
  rfl
end H1
section groupCohomologyIso
open ShortComplex
section H0
lemma dZero_comp_H0_subtype : dZero A ∘ₗ (H0 A).subtype = 0 := by
  ext ⟨x, hx⟩ g
  replace hx := hx g
  rw [← sub_eq_zero] at hx
  exact hx
def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk _ _ (dZero_comp_H0_subtype A)
instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  apply Submodule.injective_subtype
lemma shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro (x : A) (hx : dZero _ x = 0)
  refine ⟨⟨x, fun g => ?_⟩, rfl⟩
  rw [← sub_eq_zero]
  exact congr_fun hx g
@[simps! hom_left hom_right inv_left inv_right]
def dZeroArrowIso : Arrow.mk ((inhomogeneousCochains A).d 0 1) ≅
    Arrow.mk (ModuleCat.ofHom (dZero A)) :=
  Arrow.isoMk (zeroCochainsLequiv A).toModuleIso
    (oneCochainsLequiv A).toModuleIso (dZero_comp_eq A)
def isoZeroCocycles : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  KernelFork.mapIsoOfIsLimit
    ((inhomogeneousCochains A).cyclesIsKernel 0 1 (by simp)) (shortComplexH0_exact A).fIsKernel
      (dZeroArrowIso A)
lemma isoZeroCocycles_hom_comp_subtype :
    (isoZeroCocycles A).hom ≫ A.ρ.invariants.subtype =
      iCocycles A 0 ≫ (zeroCochainsLequiv A).toModuleIso.hom := by
  dsimp [isoZeroCocycles]
  apply KernelFork.mapOfIsLimit_ι
def isoH0 : groupCohomology A 0 ≅ ModuleCat.of k (H0 A) :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ isoZeroCocycles A
lemma groupCohomologyπ_comp_isoH0_hom  :
    groupCohomologyπ A 0 ≫ (isoH0 A).hom = (isoZeroCocycles A).hom := by
  simp [isoH0]
end H0
section H1
def shortComplexH1 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dZero A) (dOne A) (dOne_comp_dZero A)
@[simps! hom inv]
def shortComplexH1Iso : (inhomogeneousCochains A).sc' 0 1 2 ≅ shortComplexH1 A :=
    isoMk (zeroCochainsLequiv A).toModuleIso (oneCochainsLequiv A).toModuleIso
      (twoCochainsLequiv A).toModuleIso (dZero_comp_eq A) (dOne_comp_eq A)
def isoOneCocycles : cocycles A 1 ≅ ModuleCat.of k (oneCocycles A) :=
  (inhomogeneousCochains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatCyclesIso
lemma isoOneCocycles_hom_comp_subtype :
    (isoOneCocycles A).hom ≫ ModuleCat.ofHom (oneCocycles A).subtype =
      iCocycles A 1 ≫ (oneCochainsLequiv A).toModuleIso.hom := by
  dsimp [isoOneCocycles]
  rw [Category.assoc, Category.assoc]
  erw [(shortComplexH1 A).moduleCatCyclesIso_hom_subtype]
  rw [cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]
lemma toCocycles_comp_isoOneCocycles_hom :
    toCocycles A 0 1 ≫ (isoOneCocycles A).hom =
      (zeroCochainsLequiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH1 A).moduleCatToCycles := by
  simp [isoOneCocycles]
  rfl
def isoH1 : groupCohomology A 1 ≅ ModuleCat.of k (H1 A) :=
  (inhomogeneousCochains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH1Iso A) ≪≫ (shortComplexH1 A).moduleCatHomologyIso
lemma groupCohomologyπ_comp_isoH1_hom  :
    groupCohomologyπ A 1 ≫ (isoH1 A).hom =
      (isoOneCocycles A).hom ≫ (shortComplexH1 A).moduleCatHomologyπ := by
  simp [isoH1, isoOneCocycles]
end H1
section H2
def shortComplexH2 : ShortComplex (ModuleCat k) :=
  moduleCatMk (dOne A) (dTwo A) (dTwo_comp_dOne A)
@[simps! hom inv]
def shortComplexH2Iso :
    (inhomogeneousCochains A).sc' 1 2 3 ≅ shortComplexH2 A :=
  isoMk (oneCochainsLequiv A).toModuleIso (twoCochainsLequiv A).toModuleIso
    (threeCochainsLequiv A).toModuleIso (dOne_comp_eq A) (dTwo_comp_eq A)
def isoTwoCocycles : cocycles A 2 ≅ ModuleCat.of k (twoCocycles A) :=
  (inhomogeneousCochains A).cyclesIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    cyclesMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatCyclesIso
lemma isoTwoCocycles_hom_comp_subtype :
    (isoTwoCocycles A).hom ≫ ModuleCat.ofHom (twoCocycles A).subtype =
      iCocycles A 2 ≫ (twoCochainsLequiv A).toModuleIso.hom := by
  dsimp [isoTwoCocycles]
  rw [Category.assoc, Category.assoc]
  erw [(shortComplexH2 A).moduleCatCyclesIso_hom_subtype]
  rw [cyclesMap_i, HomologicalComplex.cyclesIsoSc'_hom_iCycles_assoc]
lemma toCocycles_comp_isoTwoCocycles_hom :
    toCocycles A 1 2 ≫ (isoTwoCocycles A).hom =
      (oneCochainsLequiv A).toModuleIso.hom ≫
        ModuleCat.ofHom (shortComplexH2 A).moduleCatToCycles := by
  simp [isoTwoCocycles]
  rfl
def isoH2 : groupCohomology A 2 ≅ ModuleCat.of k (H2 A) :=
  (inhomogeneousCochains A).homologyIsoSc' _ _ _ (by aesop) (by aesop) ≪≫
    homologyMapIso (shortComplexH2Iso A) ≪≫ (shortComplexH2 A).moduleCatHomologyIso
lemma groupCohomologyπ_comp_isoH2_hom  :
    groupCohomologyπ A 2 ≫ (isoH2 A).hom =
      (isoTwoCocycles A).hom ≫ (shortComplexH2 A).moduleCatHomologyπ := by
  simp [isoH2, isoTwoCocycles]
end H2
end groupCohomologyIso
end groupCohomology