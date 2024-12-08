import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Sheaves.Stalks
universe v u
open CategoryTheory
open TopologicalSpace
open Opposite
open TopCat
open TopCat.Presheaf
namespace AlgebraicGeometry
abbrev RingedSpace : TypeMax.{u+1, v+1} :=
  SheafedSpace.{v+1, v, u} CommRingCat.{v}
namespace RingedSpace
open SheafedSpace
@[simp]
lemma res_zero {X : RingedSpace.{u}} {U V : TopologicalSpace.Opens X}
    (hUV : U ≤ V) : (0 : X.presheaf.obj (op V)) |_ U = 0 :=
  map_zero _
variable (X : RingedSpace)
instance : CoeSort RingedSpace Type* where
  coe X := X.carrier
lemma exists_res_eq_zero_of_germ_eq_zero (U : Opens X) (f : X.presheaf.obj (op U)) (x : U)
    (h : X.presheaf.germ U x.val x.property f = 0) :
    ∃ (V : Opens X) (i : V ⟶ U) (_ : x.1 ∈ V), X.presheaf.map i.op f = 0 := by
  have h1 : X.presheaf.germ U x.val x.property f = X.presheaf.germ U x.val x.property 0 := by simpa
  obtain ⟨V, hv, i, _, hv4⟩ := TopCat.Presheaf.germ_eq X.presheaf x.1 x.2 x.2 f 0 h1
  use V, i, hv
  simpa using hv4
theorem isUnit_res_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U)) (x : X) (hx : x ∈ U)
    (h : IsUnit (X.presheaf.germ U x hx f)) :
    ∃ (V : Opens X) (i : V ⟶ U) (_ : x ∈ V), IsUnit (X.presheaf.map i.op f) := by
  obtain ⟨g', heq⟩ := h.exists_right_inv
  obtain ⟨V, hxV, g, rfl⟩ := X.presheaf.germ_exist x g'
  let W := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  replace heq : (X.presheaf.germ _ x hxW) ((X.presheaf.map (U.infLELeft V).op) f *
      (X.presheaf.map (U.infLERight V).op) g) = (X.presheaf.germ _ x hxW) 1 := by
    dsimp [germ]
    erw [map_mul, map_one, show X.presheaf.germ _ x hxW ((X.presheaf.map (U.infLELeft V).op) f) =
      X.presheaf.germ U x hx f from X.presheaf.germ_res_apply (Opens.infLELeft U V) x hxW f,
      show X.presheaf.germ _ x hxW (X.presheaf.map (U.infLERight V).op g) =
      X.presheaf.germ _ x hxV g from X.presheaf.germ_res_apply (Opens.infLERight U V) x hxW g]
    exact heq
  obtain ⟨W', hxW', i₁, i₂, heq'⟩ := X.presheaf.germ_eq x hxW hxW _ _ heq
  use W', i₁ ≫ Opens.infLELeft U V, hxW'
  rw [(X.presheaf.map i₂.op).map_one, (X.presheaf.map i₁.op).map_mul] at heq'
  rw [← comp_apply, ← X.presheaf.map_comp, ← comp_apply, ← X.presheaf.map_comp, ← op_comp] at heq'
  exact isUnit_of_mul_eq_one _ _ heq'
theorem isUnit_of_isUnit_germ (U : Opens X) (f : X.presheaf.obj (op U))
    (h : ∀ (x) (hx : x ∈ U), IsUnit (X.presheaf.germ U x hx f)) : IsUnit f := by
  choose V iVU m h_unit using fun x : U => X.isUnit_res_of_isUnit_germ U f x x.2 (h x.1 x.2)
  have hcover : U ≤ iSup V := by
    intro x hxU
    erw [Opens.mem_iSup]
    exact ⟨⟨x, hxU⟩, m ⟨x, hxU⟩⟩
  choose g hg using fun x : U => IsUnit.exists_right_inv (h_unit x)
  have ic : IsCompatible (sheaf X).val V g := by
    intro x y
    apply section_ext X.sheaf (V x ⊓ V y)
    rintro z ⟨hzVx, hzVy⟩
    rw [germ_res_apply, germ_res_apply]
    apply (h z ((iVU x).le hzVx)).mul_right_inj.mp
    rw [← X.presheaf.germ_res_apply (iVU x) z hzVx f]
    change X.presheaf.germ _ z hzVx _ * (X.presheaf.germ _ z hzVx _) =
      X.presheaf.germ _ z hzVx _ * X.presheaf.germ _ z hzVy (g y)
    rw [← RingHom.map_mul,
      congr_arg (X.presheaf.germ (V x) z hzVx) (hg x),
      X.presheaf.germ_res_apply _ _ _ f,
      ← X.presheaf.germ_res_apply (iVU y) z hzVy f,
      ← RingHom.map_mul,
      congr_arg (X.presheaf.germ (V y) z hzVy) (hg y), RingHom.map_one, RingHom.map_one]
  obtain ⟨gl, gl_spec, -⟩ := X.sheaf.existsUnique_gluing' V U iVU hcover g ic
  apply isUnit_of_mul_eq_one f gl
  apply X.sheaf.eq_of_locally_eq' V U iVU hcover
  intro i
  rw [RingHom.map_one, RingHom.map_mul, gl_spec]
  exact hg i
def basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) : Opens X where
  carrier := { x : X | ∃ (hx : x ∈ U), IsUnit (X.presheaf.germ U x hx f) }
  is_open' := by
    rw [isOpen_iff_forall_mem_open]
    rintro x ⟨hxU, hx⟩
    obtain ⟨V, i, hxV, hf⟩ := X.isUnit_res_of_isUnit_germ U f x hxU hx
    use V.1
    refine ⟨?_, V.2, hxV⟩
    intro y hy
    use i.le hy
    convert RingHom.isUnit_map (X.presheaf.germ _ y hy) hf
    exact (X.presheaf.germ_res_apply i y hy f).symm
theorem mem_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) (x : X) (hx : x ∈ U) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x hx f) :=
  ⟨Exists.choose_spec, (⟨hx, ·⟩)⟩
@[simp]
theorem mem_basicOpen' {U : Opens X} (f : X.presheaf.obj (op U)) (x : U) :
    ↑x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.germ U x.1 x.2 f) :=
  mem_basicOpen X f x.1 x.2
@[simp]
theorem mem_top_basicOpen (f : X.presheaf.obj (op ⊤)) (x : X) :
    x ∈ X.basicOpen f ↔ IsUnit (X.presheaf.Γgerm x f) :=
  mem_basicOpen X f x .intro
theorem basicOpen_le {U : Opens X} (f : X.presheaf.obj (op U)) : X.basicOpen f ≤ U := by
  rintro x ⟨h, _⟩; exact h
theorem isUnit_res_basicOpen {U : Opens X} (f : X.presheaf.obj (op U)) :
    IsUnit (X.presheaf.map (@homOfLE (Opens X) _ _ _ (X.basicOpen_le f)).op f) := by
  apply isUnit_of_isUnit_germ
  rintro x ⟨hxU, hx⟩
  convert hx
  convert X.presheaf.germ_res_apply _ _ _ _
@[simp]
theorem basicOpen_res {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = unop V ⊓ @basicOpen X (unop U) f := by
  ext x; constructor
  · rintro ⟨hxV, hx⟩
    rw [X.presheaf.germ_res_apply'] at hx
    exact ⟨hxV, i.unop.le hxV, hx⟩
  · rintro ⟨hxV, _, hx⟩
    refine ⟨hxV, ?_⟩
    rw [X.presheaf.germ_res_apply']
    exact hx
@[simp (high)]
theorem basicOpen_res_eq {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) [IsIso i] (f : X.presheaf.obj U) :
    @basicOpen X (unop V) (X.presheaf.map i f) = @RingedSpace.basicOpen X (unop U) f := by
  apply le_antisymm
  · rw [X.basicOpen_res i f]; exact inf_le_right
  · have := X.basicOpen_res (inv i) (X.presheaf.map i f)
    rw [← comp_apply, ← X.presheaf.map_comp, IsIso.hom_inv_id, X.presheaf.map_id, id_apply] at this
    rw [this]
    exact inf_le_right
@[simp]
theorem basicOpen_mul {U : Opens X} (f g : X.presheaf.obj (op U)) :
    X.basicOpen (f * g) = X.basicOpen f ⊓ X.basicOpen g := by
  ext x
  by_cases hx : x ∈ U
  · simp [mem_basicOpen (hx := hx)]
  · simp [mt (basicOpen_le X _ ·) hx]
@[simp]
lemma basicOpen_pow {U : Opens X} (f : X.presheaf.obj (op U)) (n : ℕ) (h : 0 < n) :
    X.basicOpen (f ^ n) = X.basicOpen f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' h
  induction k with
  | zero => simp
  | succ n hn => rw [pow_add]; simp_all
theorem basicOpen_of_isUnit {U : Opens X} {f : X.presheaf.obj (op U)} (hf : IsUnit f) :
    X.basicOpen f = U := by
  apply le_antisymm
  · exact X.basicOpen_le f
  intro x hx
  rw [SetLike.mem_coe, X.mem_basicOpen f x hx]
  exact RingHom.isUnit_map _ hf
def zeroLocus {U : Opens X} (s : Set (X.presheaf.obj (op U))) : Set X :=
  ⋂ f ∈ s, (X.basicOpen f)ᶜ
lemma zeroLocus_isClosed {U : Opens X} (s : Set (X.presheaf.obj (op U))) :
    IsClosed (X.zeroLocus s) := by
  apply isClosed_biInter
  intro i _
  simp only [isClosed_compl_iff]
  exact Opens.isOpen (X.basicOpen i)
lemma zeroLocus_singleton {U : Opens X} (f : X.presheaf.obj (op U)) :
    X.zeroLocus {f} = (X.basicOpen f).carrierᶜ := by
  simp [zeroLocus]
@[simp]
lemma zeroLocus_empty_eq_univ {U : Opens X} :
    X.zeroLocus (∅ : Set (X.presheaf.obj (op U))) = Set.univ := by
  simp [zeroLocus]
@[simp]
lemma mem_zeroLocus_iff {U : Opens X} (s : Set (X.presheaf.obj (op U))) (x : X) :
    x ∈ X.zeroLocus s ↔ ∀ f ∈ s, x ∉ X.basicOpen f := by
  simp [zeroLocus]
end RingedSpace
end AlgebraicGeometry