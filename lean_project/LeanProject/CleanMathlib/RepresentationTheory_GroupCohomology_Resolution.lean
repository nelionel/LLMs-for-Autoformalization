import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RepresentationTheory.Rep
import Mathlib.RingTheory.TensorProduct.Free
suppress_compilation
noncomputable section
universe u v w
variable {k G : Type u} [CommRing k] {n : ℕ}
open CategoryTheory Finsupp
local notation "Gⁿ" => Fin n → G
set_option quotPrecheck false
local notation "Gⁿ⁺¹" => Fin (n + 1) → G
namespace groupCohomology.resolution
open Finsupp hiding lift
open MonoidalCategory
open Fin (partialProd)
section Basis
variable (k G n) [Group G]
section Action
open Action
def actionDiagonalSucc (G : Type u) [Group G] :
    ∀ n : ℕ, diagonal G (n + 1) ≅ leftRegular G ⊗ Action.mk (Fin n → G) 1
  | 0 =>
    diagonalOneIsoLeftRegular G ≪≫
      (ρ_ _).symm ≪≫ tensorIso (Iso.refl _) (tensorUnitIso (Equiv.equivOfUnique PUnit _).toIso)
  | n + 1 =>
    diagonalSucc _ _ ≪≫
      tensorIso (Iso.refl _) (actionDiagonalSucc G n) ≪≫
        leftRegularTensorIso _ _ ≪≫
          tensorIso (Iso.refl _)
            (mkIso (Fin.insertNthEquiv (fun _ => G) 0).toIso fun _ => rfl)
theorem actionDiagonalSucc_hom_apply {G : Type u} [Group G] {n : ℕ} (f : Fin (n + 1) → G) :
    (actionDiagonalSucc G n).hom.hom f = (f 0, fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) := by
  induction' n with n hn
  · exact Prod.ext rfl (funext fun x => Fin.elim0 x)
  · refine Prod.ext rfl (funext fun x => ?_)
    dsimp [actionDiagonalSucc]
    erw [hn (fun (j : Fin (n + 1)) => f j.succ)]
    exact Fin.cases rfl (fun i => rfl) x
theorem actionDiagonalSucc_inv_apply {G : Type u} [Group G] {n : ℕ} (g : G) (f : Fin n → G) :
    (actionDiagonalSucc G n).inv.hom (g, f) = (g • Fin.partialProd f : Fin (n + 1) → G) := by
  revert g
  induction' n with n hn
  · intro g
    funext (x : Fin 1)
    simp only [Subsingleton.elim x 0, Pi.smul_apply, Fin.partialProd_zero, smul_eq_mul, mul_one]
    rfl
  · intro g
    funext x
    dsimp [actionDiagonalSucc]
    erw [hn, Fin.consEquiv_apply]
    refine Fin.cases ?_ (fun i => ?_) x
    · simp only [Fin.insertNth_zero, Fin.cons_zero, Fin.partialProd_zero, mul_one]
    · simp only [Fin.cons_succ, Pi.smul_apply, smul_eq_mul, Fin.partialProd_succ', ← mul_assoc]
      rfl
end Action
section Rep
open Rep
def diagonalSucc (n : ℕ) :
    diagonal k G (n + 1) ≅ leftRegular k G ⊗ trivial k G ((Fin n → G) →₀ k) :=
  (linearization k G).mapIso (actionDiagonalSucc G n) ≪≫
    (Functor.Monoidal.μIso (linearization k G) _ _).symm ≪≫
      tensorIso (Iso.refl _) (linearizationTrivialIso k G (Fin n → G))
variable {k G n}
theorem diagonalSucc_hom_single (f : Gⁿ⁺¹) (a : k) :
    (diagonalSucc k G n).hom.hom (single f a) =
      single (f 0) 1 ⊗ₜ single (fun i => (f (Fin.castSucc i))⁻¹ * f i.succ) a := by
  dsimp [diagonalSucc]
  erw [lmapDomain_apply, mapDomain_single, LinearEquiv.coe_toLinearMap, finsuppTensorFinsupp',
    LinearEquiv.trans_symm, LinearEquiv.trans_apply, lcongr_symm, Equiv.refl_symm]
  erw [lcongr_single]
  rw [TensorProduct.lid_symm_apply, actionDiagonalSucc_hom_apply, finsuppTensorFinsupp_symm_single]
  rfl
theorem diagonalSucc_inv_single_single (g : G) (f : Gⁿ) (a b : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g a ⊗ₜ Finsupp.single f b) =
      single (g • partialProd f) (a * b) := by
  change mapDomain (actionDiagonalSucc G n).inv.hom
    (lcongr (Equiv.refl (G × (Fin n → G))) (TensorProduct.lid k k)
      (finsuppTensorFinsupp k k k k G (Fin n → G) (single g a ⊗ₜ[k] single f b)))
    = single (g • partialProd f) (a * b)
  rw [finsuppTensorFinsupp_single, lcongr_single, mapDomain_single, Equiv.refl_apply,
    actionDiagonalSucc_inv_apply]
  rfl
theorem diagonalSucc_inv_single_left (g : G) (f : Gⁿ →₀ k) (r : k) :
    (diagonalSucc k G n).inv.hom (Finsupp.single g r ⊗ₜ f) =
      Finsupp.lift (Gⁿ⁺¹ →₀ k) k Gⁿ (fun f => single (g • partialProd f) r) f := by
  refine f.induction ?_ ?_
  · simp only [TensorProduct.tmul_zero, map_zero]
  · intro a b x _ _ hx
    simp only [lift_apply, smul_single', mul_one, TensorProduct.tmul_add, map_add,
      diagonalSucc_inv_single_single, hx, Finsupp.sum_single_index, mul_comm b,
      zero_mul, single_zero]
theorem diagonalSucc_inv_single_right (g : G →₀ k) (f : Gⁿ) (r : k) :
    (diagonalSucc k G n).inv.hom (g ⊗ₜ Finsupp.single f r) =
      Finsupp.lift _ k G (fun a => single (a • partialProd f) r) g := by
  refine g.induction ?_ ?_
  · simp only [TensorProduct.zero_tmul, map_zero]
  · intro a b x _ _ hx
    simp only [lift_apply, smul_single', map_add, hx, diagonalSucc_inv_single_single,
      TensorProduct.add_tmul, Finsupp.sum_single_index, zero_mul, single_zero]
end Rep
open scoped TensorProduct
open Representation
def ofMulActionBasisAux :
    MonoidAlgebra k G ⊗[k] ((Fin n → G) →₀ k) ≃ₗ[MonoidAlgebra k G]
      (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  { (Rep.equivalenceModuleMonoidAlgebra.1.mapIso (diagonalSucc k G n).symm).toLinearEquiv with
    map_smul' := fun r x => by
      rw [RingHom.id_apply, LinearEquiv.toFun_eq_coe, ← LinearEquiv.map_smul]
      congr 1
      show _ = Representation.asAlgebraHom (tensorObj (Rep.leftRegular k G)
        (Rep.trivial k G ((Fin n → G) →₀ k))).ρ r _
      refine x.induction_on ?_ (fun x y => ?_) fun y z hy hz => ?_
      · rw [smul_zero, map_zero]
      · rw [TensorProduct.smul_tmul', smul_eq_mul, ← ofMulAction_self_smul_eq_mul]
        exact (smul_tprod_one_asModule (Representation.ofMulAction k G G) r x y).symm
      · rw [smul_add, hz, hy, map_add] }
def ofMulActionBasis :
    Basis (Fin n → G) (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Basis.map
    (Algebra.TensorProduct.basis (MonoidAlgebra k G)
      (Finsupp.basisSingleOne : Basis (Fin n → G) k ((Fin n → G) →₀ k)))
    (ofMulActionBasisAux k G n)
theorem ofMulAction_free :
    Module.Free (MonoidAlgebra k G) (ofMulAction k G (Fin (n + 1) → G)).asModule :=
  Module.Free.of_basis (ofMulActionBasis k G n)
end Basis
end groupCohomology.resolution
namespace Rep
variable (n) [Group G] (A : Rep k G)
open groupCohomology.resolution
noncomputable def diagonalHomEquiv :
    (Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) ≃ₗ[k] (Fin n → G) → A :=
  Linear.homCongr k
        ((diagonalSucc k G n).trans ((Representation.ofMulAction k G G).repOfTprodIso 1))
        (Iso.refl _) ≪≫ₗ
      (Rep.MonoidalClosed.linearHomEquivComm _ _ _ ≪≫ₗ Rep.leftRegularHomEquiv _) ≪≫ₗ
    (Finsupp.llift A k k (Fin n → G)).symm
variable {n A}
theorem diagonalHomEquiv_apply (f : Rep.ofMulAction k G (Fin (n + 1) → G) ⟶ A) (x : Fin n → G) :
    diagonalHomEquiv n A f x = f.hom (Finsupp.single (Fin.partialProd x) 1) := by
  change f.hom ((diagonalSucc k G n).inv.hom (Finsupp.single 1 1 ⊗ₜ[k] Finsupp.single x 1)) = _
  rw [diagonalSucc_inv_single_single, one_smul, one_mul]
theorem diagonalHomEquiv_symm_apply (f : (Fin n → G) → A) (x : Fin (n + 1) → G) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single x 1) =
      A.ρ (x 0) (f fun i : Fin n => (x (Fin.castSucc i))⁻¹ * x i.succ) := by
  unfold diagonalHomEquiv
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    leftRegularHomEquiv_symm_apply, Linear.homCongr_symm_apply, Iso.trans_hom, Iso.refl_inv,
    Category.comp_id, Action.comp_hom, MonoidalClosed.linearHomEquivComm_symm_hom]
  rw [ModuleCat.coe_comp]
  simp only [ModuleCat.coe_comp, Function.comp_apply]
  erw [diagonalSucc_hom_single]
  conv_lhs =>
    erw [TensorProduct.uncurry_apply, Finsupp.lift_apply, Finsupp.sum_single_index]
    · simp only [one_smul]
      erw [Representation.linHom_apply]
      simp only [LinearMap.comp_apply, MonoidHom.one_apply, LinearMap.one_apply]
      erw [Finsupp.llift_apply]
      rw [Finsupp.lift_apply]
      erw [Finsupp.sum_single_index]
      · rw [one_smul]
      · rw [zero_smul]
    · rw [zero_smul]
theorem diagonalHomEquiv_symm_partialProd_succ (f : (Fin n → G) → A) (g : Fin (n + 1) → G)
    (a : Fin (n + 1)) :
    ((diagonalHomEquiv n A).symm f).hom (Finsupp.single (Fin.partialProd g ∘ a.succ.succAbove) 1)
      = f (Fin.contractNth a (· * ·) g) := by
  simp only [diagonalHomEquiv_symm_apply, Function.comp_apply, Fin.succ_succAbove_zero,
    Fin.partialProd_zero, map_one, Fin.succ_succAbove_succ, LinearMap.one_apply,
    Fin.partialProd_succ]
  congr
  ext
  rw [← Fin.partialProd_succ, Fin.inv_partialProd_mul_eq_contractNth]
end Rep
variable (G)
def classifyingSpaceUniversalCover [Monoid G] :
    SimplicialObject (Action (Type u) <| MonCat.of G) where
  obj n := Action.ofMulAction G (Fin (n.unop.len + 1) → G)
  map f :=
    { hom := fun x => x ∘ f.unop.toOrderHom
      comm := fun _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl
namespace classifyingSpaceUniversalCover
open CategoryTheory CategoryTheory.Limits
variable [Monoid G]
def cechNerveTerminalFromIso :
    cechNerveTerminalFrom (Action.ofMulAction G G) ≅ classifyingSpaceUniversalCover G :=
  NatIso.ofComponents (fun _ => limit.isoLimitCone (Action.ofMulActionLimitCone _ _)) fun f => by
    refine IsLimit.hom_ext (Action.ofMulActionLimitCone.{u, 0} G fun _ => G).2 fun j => ?_
    dsimp only [cechNerveTerminalFrom, Pi.lift]
    rw [Category.assoc, limit.isoLimitCone_hom_π, limit.lift_π, Category.assoc]
    exact (limit.isoLimitCone_hom_π _ _).symm
def cechNerveTerminalFromIsoCompForget :
    cechNerveTerminalFrom G ≅ classifyingSpaceUniversalCover G ⋙ forget _ :=
  NatIso.ofComponents (fun _ => Types.productIso _) fun _ =>
    Matrix.ext fun _ _ => Types.Limit.lift_π_apply (Discrete.functor fun _ ↦ G) _ _ _
variable (k)
open AlgebraicTopology SimplicialObject.Augmented SimplicialObject CategoryTheory.Arrow
def compForgetAugmented : SimplicialObject.Augmented (Type u) :=
  SimplicialObject.augment (classifyingSpaceUniversalCover G ⋙ forget _) (terminal _)
    (terminal.from _) fun _ _ _ => Subsingleton.elim _ _
def extraDegeneracyAugmentedCechNerve :
    ExtraDegeneracy (Arrow.mk <| terminal.from G).augmentedCechNerve :=
  AugmentedCechNerve.extraDegeneracy (Arrow.mk <| terminal.from G)
    ⟨fun _ => (1 : G),
      @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _⟩
def extraDegeneracyCompForgetAugmented : ExtraDegeneracy (compForgetAugmented G) := by
  refine
    ExtraDegeneracy.ofIso (?_ : (Arrow.mk <| terminal.from G).augmentedCechNerve ≅ _)
      (extraDegeneracyAugmentedCechNerve G)
  exact
    Comma.isoMk (CechNerveTerminalFrom.iso G ≪≫ cechNerveTerminalFromIsoCompForget G)
      (Iso.refl _) (by ext : 1; exact IsTerminal.hom_ext terminalIsTerminal _ _)
def compForgetAugmented.toModule : SimplicialObject.Augmented (ModuleCat.{u} k) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj (ModuleCat.free k)).obj (compForgetAugmented G)
def extraDegeneracyCompForgetAugmentedToModule :
    ExtraDegeneracy (compForgetAugmented.toModule k G) :=
  ExtraDegeneracy.map (extraDegeneracyCompForgetAugmented G) (ModuleCat.free k)
end classifyingSpaceUniversalCover
variable (k)
def groupCohomology.resolution [Monoid G] :=
  (AlgebraicTopology.alternatingFaceMapComplex (Rep k G)).obj
    (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G)
namespace groupCohomology.resolution
open classifyingSpaceUniversalCover AlgebraicTopology CategoryTheory CategoryTheory.Limits
variable [Monoid G]
def d (G : Type u) (n : ℕ) : ((Fin (n + 1) → G) →₀ k) →ₗ[k] (Fin n → G) →₀ k :=
  Finsupp.lift ((Fin n → G) →₀ k) k (Fin (n + 1) → G) fun g =>
    (@Finset.univ (Fin (n + 1)) _).sum fun p =>
      Finsupp.single (g ∘ p.succAbove) ((-1 : k) ^ (p : ℕ))
variable {k G}
@[simp]
theorem d_of {G : Type u} {n : ℕ} (c : Fin (n + 1) → G) :
    d k G n (Finsupp.single c 1) =
      Finset.univ.sum fun p : Fin (n + 1) =>
        Finsupp.single (c ∘ p.succAbove) ((-1 : k) ^ (p : ℕ)) := by
  simp [d]
variable (k G)
def xIso (n : ℕ) : (groupCohomology.resolution k G).X n ≅ Rep.ofMulAction k G (Fin (n + 1) → G) :=
  Iso.refl _
instance x_projective (G : Type u) [Group G] (n : ℕ) :
    Projective ((groupCohomology.resolution k G).X n) :=
  Rep.equivalenceModuleMonoidAlgebra.toAdjunction.projective_of_map_projective _ <|
    @ModuleCat.projective_of_free.{u} _ _
      (ModuleCat.of (MonoidAlgebra k G) (Representation.ofMulAction k G (Fin (n + 1) → G)).asModule)
      _ (ofMulActionBasis k G n)
theorem d_eq (n : ℕ) : ((groupCohomology.resolution k G).d (n + 1) n).hom = d k G (n + 1) := by
  refine Finsupp.lhom_ext' fun x => LinearMap.ext_ring ?_
  dsimp [groupCohomology.resolution]
  simp_rw [alternatingFaceMapComplex_obj_d, AlternatingFaceMapComplex.objD, SimplicialObject.δ,
    Functor.comp_map, ← Int.cast_smul_eq_zsmul k ((-1) ^ _ : ℤ), Int.cast_pow, Int.cast_neg,
    Int.cast_one, Action.sum_hom, Action.smul_hom, Rep.linearization_map_hom]
  rw [LinearMap.coeFn_sum, Fintype.sum_apply]
  erw [d_of (k := k) x]
  refine Finset.sum_congr rfl fun _ _ => ?_
  erw [LinearMap.smul_apply]
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.smul_single', mul_one]
  rfl
section Exactness
def forget₂ToModuleCat :=
  ((forget₂ (Rep k G) (ModuleCat.{u} k)).mapHomologicalComplex _).obj
    (groupCohomology.resolution k G)
def compForgetAugmentedIso :
    AlternatingFaceMapComplex.obj
        (SimplicialObject.Augmented.drop.obj (compForgetAugmented.toModule k G)) ≅
      groupCohomology.resolution.forget₂ToModuleCat k G :=
  eqToIso
    (Functor.congr_obj (map_alternatingFaceMapComplex (forget₂ (Rep k G) (ModuleCat.{u} k))).symm
      (classifyingSpaceUniversalCover G ⋙ Rep.linearization k G))
def forget₂ToModuleCatHomotopyEquiv :
    HomotopyEquiv (groupCohomology.resolution.forget₂ToModuleCat k G)
      ((ChainComplex.single₀ (ModuleCat k)).obj ((forget₂ (Rep k G) _).obj <| Rep.trivial k G k)) :=
  (HomotopyEquiv.ofIso (compForgetAugmentedIso k G).symm).trans <|
    (SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv
          (extraDegeneracyCompForgetAugmentedToModule k G)).trans
      (HomotopyEquiv.ofIso <|
        (ChainComplex.single₀ (ModuleCat.{u} k)).mapIso
          (@Finsupp.LinearEquiv.finsuppUnique k k _ _ _ (⊤_ Type u)
              Types.terminalIso.toEquiv.unique).toModuleIso)
def ε : Rep.ofMulAction k G (Fin 1 → G) ⟶ Rep.trivial k G k where
  hom := Finsupp.linearCombination _ fun _ => (1 : k)
  comm g := Finsupp.lhom_ext' fun _ => LinearMap.ext_ring (by
    show
      Finsupp.linearCombination k (fun _ => (1 : k)) (Finsupp.mapDomain _ (Finsupp.single _ _)) =
        Finsupp.linearCombination k (fun _ => (1 : k)) (Finsupp.single _ _)
    simp only [Finsupp.mapDomain_single, Finsupp.linearCombination_single])
theorem forget₂ToModuleCatHomotopyEquiv_f_0_eq :
    (forget₂ToModuleCatHomotopyEquiv k G).1.f 0 = (forget₂ (Rep k G) _).map (ε k G) := by
  show (HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _ ≫ HomotopyEquiv.hom _).f 0 = _
  simp only [HomologicalComplex.comp_f]
  dsimp
  convert Category.id_comp (X := (forget₂ToModuleCat k G).X 0) _
  · dsimp only [HomotopyEquiv.ofIso, compForgetAugmentedIso]
    simp only [Iso.symm_hom, eqToIso.inv, HomologicalComplex.eqToHom_f, eqToHom_refl]
  trans (linearCombination _ fun _ => (1 : k)).comp ((ModuleCat.free k).map (terminal.from _))
  · erw [Finsupp.lmapDomain_linearCombination (α := Fin 1 → G) (R := k) (α' := ⊤_ Type u)
        (v := fun _ => (1 : k)) (v' := fun _ => (1 : k))
        (terminal.from
          ((classifyingSpaceUniversalCover G).obj (Opposite.op (SimplexCategory.mk 0))).V)
        LinearMap.id fun i => rfl,
      LinearMap.id_comp]
    rfl
  · congr
    · ext x
      dsimp (config := { unfoldPartialApp := true }) [HomotopyEquiv.ofIso,
        Finsupp.LinearEquiv.finsuppUnique]
      rw [linearCombination_single, one_smul,
        @Unique.eq_default _ Types.terminalIso.toEquiv.unique x,
        ChainComplex.single₀_map_f_zero, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
        Finsupp.equivFunOnFinite_apply, Finsupp.single_eq_same]
    · exact @Subsingleton.elim _ (@Unique.instSubsingleton _ (Limits.uniqueToTerminal _)) _ _
theorem d_comp_ε : (groupCohomology.resolution k G).d 1 0 ≫ ε k G = 0 := by
  ext : 1
  refine LinearMap.ext fun x => ?_
  have : (forget₂ToModuleCat k G).d 1 0
      ≫ (forget₂ (Rep k G) (ModuleCat.{u} k)).map (ε k G) = 0 := by
    rw [← forget₂ToModuleCatHomotopyEquiv_f_0_eq,
      ← (forget₂ToModuleCatHomotopyEquiv k G).1.2 1 0 rfl]
    exact comp_zero
  exact LinearMap.ext_iff.1 this _
def εToSingle₀ :
    groupCohomology.resolution k G ⟶ (ChainComplex.single₀ _).obj (Rep.trivial k G k) :=
  ((groupCohomology.resolution k G).toSingle₀Equiv _).symm ⟨ε k G, d_comp_ε k G⟩
theorem εToSingle₀_comp_eq :
    ((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G) ≫
        (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _ =
      (forget₂ToModuleCatHomotopyEquiv k G).hom := by
  dsimp
  ext1
  dsimp
  simpa using (forget₂ToModuleCatHomotopyEquiv_f_0_eq k G).symm
theorem quasiIso_forget₂_εToSingle₀ :
    QuasiIso (((forget₂ _ (ModuleCat.{u} k)).mapHomologicalComplex _).map (εToSingle₀ k G)) := by
  have h : QuasiIso (forget₂ToModuleCatHomotopyEquiv k G).hom := inferInstance
  rw [← εToSingle₀_comp_eq k G] at h
  exact quasiIso_of_comp_right (hφφ' := h)
instance : QuasiIso (εToSingle₀ k G) := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ (forget₂ _ (ModuleCat.{u} k))]
  apply quasiIso_forget₂_εToSingle₀
end Exactness
end groupCohomology.resolution
open groupCohomology.resolution HomologicalComplex.Hom
variable [Group G]
def groupCohomology.projectiveResolution : ProjectiveResolution (Rep.trivial k G k) where
  π := εToSingle₀ k G
instance : EnoughProjectives (Rep k G) :=
  Rep.equivalenceModuleMonoidAlgebra.enoughProjectives_iff.2
    ModuleCat.moduleCat_enoughProjectives.{u}
def groupCohomology.extIso (V : Rep k G) (n : ℕ) :
    ((Ext k (Rep k G) n).obj (Opposite.op <| Rep.trivial k G k)).obj V ≅
      ((groupCohomology.resolution k G).linearYonedaObj k V).homology n :=
  (groupCohomology.projectiveResolution k G).isoExt n V