import Mathlib.Topology.Homotopy.Equiv
import Mathlib.CategoryTheory.Equivalence
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
noncomputable section
universe u
open FundamentalGroupoid
open CategoryTheory
open FundamentalGroupoidFunctor
open scoped FundamentalGroupoid
open scoped unitInterval
namespace unitInterval
def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl
def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl
attribute [local instance] Path.Homotopic.setoid
def uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧
end unitInterval
namespace ContinuousMap.Homotopy
open unitInterval (uhpath01)
attribute [local instance] Path.Homotopic.setoid
section Casts
abbrev hcast {X : TopCat} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
  eqToHom <| FundamentalGroupoid.ext hx
@[simp]
theorem hcast_def {X : TopCat} {x₀ x₁ : X} (hx₀ : x₀ = x₁) :
    hcast hx₀ = eqToHom (FundamentalGroupoid.ext hx₀) :=
  rfl
variable {X₁ X₂ Y : TopCat.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)} {x₀ x₁ : X₁} {x₂ x₃ : X₂}
  {p : Path x₀ x₁} {q : Path x₂ x₃} (hfg : ∀ t, f (p t) = g (q t))
include hfg
theorem heq_path_of_eq_image : HEq ((πₘ f).map ⟦p⟧) ((πₘ g).map ⟦q⟧) := by
  simp only [map_eq, ← Path.Homotopic.map_lift]; apply Path.Homotopic.hpath_hext; exact hfg
private theorem start_path : f x₀ = g x₂ := by convert hfg 0 <;> simp only [Path.source]
private theorem end_path : f x₁ = g x₃ := by convert hfg 1 <;> simp only [Path.target]
theorem eq_path_of_eq_image :
    (πₘ f).map ⟦p⟧ = hcast (start_path hfg) ≫ (πₘ g).map ⟦q⟧ ≫ hcast (end_path hfg).symm := by
  rw [conj_eqToHom_iff_heq
    ((πₘ f).map ⟦p⟧) ((πₘ g).map ⟦q⟧)
    (FundamentalGroupoid.ext <| start_path hfg)
    (FundamentalGroupoid.ext <| end_path hfg)]
  exact heq_path_of_eq_image hfg
end Casts
variable {X Y : TopCat.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) {x₀ x₁ : X}
  (p : fromTop x₀ ⟶ fromTop x₁)
def uliftMap : C(TopCat.of (ULift.{u} I × X), Y) :=
  ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uLift_down.comp continuous_fst).prod_mk continuous_snd)⟩
@[simp, nolint simpNF]
theorem ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x) :=
  rfl
abbrev prodToProdTopI {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
    (p₂ : fromTop b₁ ⟶ fromTop b₂) :=
  (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)
def diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁)) :=
  (πₘ H.uliftMap).map (prodToProdTopI uhpath01 p)
def diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁) :=
  hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)
theorem apply_zero_path : (πₘ f).map p = hcast (H.apply_zero x₀).symm ≫
    (πₘ H.uliftMap).map (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 0))) p) ≫
    hcast (H.apply_zero x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    erw [Path.prod_coe]; simp_rw [ulift_apply]; simp
theorem apply_one_path : (πₘ g).map p = hcast (H.apply_one x₀).symm ≫
    (πₘ H.uliftMap).map (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 1))) p) ≫
    hcast (H.apply_one x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    erw [Path.prod_coe]; simp_rw [ulift_apply]; simp
theorem evalAt_eq (x : X) : ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫
    (πₘ H.uliftMap).map (prodToProdTopI uhpath01 (𝟙 (fromTop x))) ≫
      hcast (H.apply_one x).symm.symm := by
  dsimp only [prodToProdTopI, uhpath01, hcast]
  refine (@conj_eqToHom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _
    (FundamentalGroupoid.ext <| H.apply_one x).symm).mpr ?_
  simp only [id_eq_path_refl, prodToProdTop_map, Path.Homotopic.prod_lift, map_eq, ←
    Path.Homotopic.map_lift]
  apply Path.Homotopic.hpath_hext; intro; rfl
theorem eq_diag_path : (πₘ f).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
    (⟦H.evalAt x₀⟧ ≫ (πₘ g).map p : fromTop (f x₀) ⟶ fromTop (g x₁)) = H.diagonalPath' p := by
  rw [H.apply_zero_path, H.apply_one_path, H.evalAt_eq]
  erw [H.evalAt_eq] 
  dsimp only [prodToProdTopI]
  constructor
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] 
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] 
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl
end ContinuousMap.Homotopy
namespace FundamentalGroupoidFunctor
open CategoryTheory
open scoped FundamentalGroupoid
attribute [local instance] Path.Homotopic.setoid
variable {X Y : TopCat.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g)
def homotopicMapsNatIso : @Quiver.Hom _ Functor.category.toQuiver (πₘ f) (πₘ g) where
  app x := ⟦H.evalAt x.as⟧
  naturality x y p := by erw [(H.eq_diag_path p).1, (H.eq_diag_path p).2]
instance : IsIso (homotopicMapsNatIso H) := by apply NatIso.isIso_of_isIso_app
open scoped ContinuousMap
def equivOfHomotopyEquiv (hequiv : X ≃ₕ Y) : πₓ X ≌ πₓ Y := by
  apply CategoryTheory.Equivalence.mk (πₘ hequiv.toFun : πₓ X ⥤ πₓ Y)
    (πₘ hequiv.invFun : πₓ Y ⥤ πₓ X) <;>
    simp only [Grpd.hom_to_functor, Grpd.id_to_functor]
  · convert (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
    exacts [((π).map_id X).symm, ((π).map_comp _ _).symm]
  · convert asIso (homotopicMapsNatIso hequiv.right_inv.some)
    exacts [((π).map_comp _ _).symm, ((π).map_id Y).symm]
end FundamentalGroupoidFunctor