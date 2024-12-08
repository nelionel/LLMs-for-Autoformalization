import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Instances
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.Topology.Sheaves.LocalPredicate
universe u
noncomputable section
variable (R : Type u) [CommRing R]
open TopCat
open TopologicalSpace
open CategoryTheory
open Opposite
namespace AlgebraicGeometry
def PrimeSpectrum.Top : TopCat :=
  TopCat.of (PrimeSpectrum R)
namespace StructureSheaf
def Localizations (P : PrimeSpectrum.Top R) : Type u :=
  Localization.AtPrime P.asIdeal
instance commRingLocalizations (P : PrimeSpectrum.Top R) : CommRing <| Localizations R P :=
  inferInstanceAs <| CommRing <| Localization.AtPrime P.asIdeal
instance localRingLocalizations (P : PrimeSpectrum.Top R) : IsLocalRing <| Localizations R P :=
  inferInstanceAs <| IsLocalRing <| Localization.AtPrime P.asIdeal
instance (P : PrimeSpectrum.Top R) : Inhabited (Localizations R P) :=
  ⟨1⟩
instance (U : Opens (PrimeSpectrum.Top R)) (x : U) : Algebra R (Localizations R x) :=
  inferInstanceAs <| Algebra R (Localization.AtPrime x.1.asIdeal)
instance (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    IsLocalization.AtPrime (Localizations R x) (x : PrimeSpectrum.Top R).asIdeal :=
  Localization.isLocalization
variable {R}
def IsFraction {U : Opens (PrimeSpectrum.Top R)} (f : ∀ x : U, Localizations R x) : Prop :=
  ∃ r s : R, ∀ x : U, ¬s ∈ x.1.asIdeal ∧ f x * algebraMap _ _ s = algebraMap _ _ r
theorem IsFraction.eq_mk' {U : Opens (PrimeSpectrum.Top R)} {f : ∀ x : U, Localizations R x}
    (hf : IsFraction f) :
    ∃ r s : R,
      ∀ x : U,
        ∃ hs : s ∉ x.1.asIdeal,
          f x =
            IsLocalization.mk' (Localization.AtPrime _) r
              (⟨s, hs⟩ : (x : PrimeSpectrum.Top R).asIdeal.primeCompl) := by
  rcases hf with ⟨r, s, h⟩
  refine ⟨r, s, fun x => ⟨(h x).1, (IsLocalization.mk'_eq_iff_eq_mul.mpr ?_).symm⟩⟩
  exact (h x).2.symm
variable (R)
def isFractionPrelocal : PrelocalPredicate (Localizations R) where
  pred {_} f := IsFraction f
  res := by rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x => w (i x)⟩
def isLocallyFraction : LocalPredicate (Localizations R) :=
  (isFractionPrelocal R).sheafify
@[simp]
theorem isLocallyFraction_pred {U : Opens (PrimeSpectrum.Top R)} (f : ∀ x : U, Localizations R x) :
    (isLocallyFraction R).pred f =
      ∀ x : U,
        ∃ (V : _) (_ : x.1 ∈ V) (i : V ⟶ U),
          ∃ r s : R,
            ∀ y : V, ¬s ∈ y.1.asIdeal ∧ f (i y : U) * algebraMap _ _ s = algebraMap _ _ r :=
  rfl
def sectionsSubring (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    Subring (∀ x : U.unop, Localizations R x) where
  carrier := { f | (isLocallyFraction R).pred f }
  zero_mem' := by
    refine fun x => ⟨unop U, x.2, 𝟙 _, 0, 1, fun y => ⟨?_, ?_⟩⟩
    · rw [← Ideal.ne_top_iff_one]; exact y.1.isPrime.1
    · simp
  one_mem' := by
    refine fun x => ⟨unop U, x.2, 𝟙 _, 1, 1, fun y => ⟨?_, ?_⟩⟩
    · rw [← Ideal.ne_top_iff_one]; exact y.1.isPrime.1
    · simp
  add_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * sb + rb * sa, sa * sb, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [add_mul, RingHom.map_add, Pi.add_apply, RingHom.map_mul]
      rw [← wa, ← wb]
      simp only [mul_assoc]
      congr 2
      rw [mul_comm]
  neg_mem' := by
    intro a ha x
    rcases ha x with ⟨V, m, i, r, s, w⟩
    refine ⟨V, m, i, -r, s, ?_⟩
    intro y
    rcases w y with ⟨nm, w⟩
    fconstructor
    · exact nm
    · simp only [RingHom.map_neg, Pi.neg_apply]
      rw [← w]
      simp only [neg_mul]
  mul_mem' := by
    intro a b ha hb x
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, ?_⟩
    intro y
    rcases wa (Opens.infLELeft _ _ y) with ⟨nma, wa⟩
    rcases wb (Opens.infLERight _ _ y) with ⟨nmb, wb⟩
    fconstructor
    · intro H; cases y.1.isPrime.mem_or_mem H <;> contradiction
    · simp only [Pi.mul_apply, RingHom.map_mul]
      rw [← wa, ← wb]
      simp only [mul_left_comm, mul_assoc, mul_comm]
end StructureSheaf
open StructureSheaf
def structureSheafInType : Sheaf (Type u) (PrimeSpectrum.Top R) :=
  subsheafToTypes (isLocallyFraction R)
instance commRingStructureSheafInTypeObj (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    CommRing ((structureSheafInType R).1.obj U) :=
  (sectionsSubring R U).toCommRing
open PrimeSpectrum
@[simps]
def structurePresheafInCommRing : Presheaf CommRingCat (PrimeSpectrum.Top R) where
  obj U := CommRingCat.of ((structureSheafInType R).1.obj U)
  map {_ _} i :=
    { toFun := (structureSheafInType R).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
attribute [nolint simpNF] AlgebraicGeometry.structurePresheafInCommRing_map_apply
def structurePresheafCompForget :
    structurePresheafInCommRing R ⋙ forget CommRingCat ≅ (structureSheafInType R).1 :=
  NatIso.ofComponents fun _ => Iso.refl _
open TopCat.Presheaf
def Spec.structureSheaf : Sheaf CommRingCat (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInCommRing R,
    (
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget R).symm (structureSheafInType R).cond)⟩
open Spec (structureSheaf)
namespace StructureSheaf
@[simp]
theorem res_apply (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U)
    (s : (structureSheaf R).1.obj (op U)) (x : V) :
    ((structureSheaf R).1.map i.op s).1 x = (s.1 (i x) : _) :=
  rfl
def const (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (structureSheaf R).1.obj (op U) :=
  ⟨fun x => IsLocalization.mk' _ f ⟨g, hu x x.2⟩, fun x =>
    ⟨U, x.2, 𝟙 _, f, g, fun y => ⟨hu y y.2, IsLocalization.mk'_spec _ _ _⟩⟩⟩
@[simp]
theorem const_apply (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U) :
    (const R f g U hu).1 x =
      IsLocalization.mk' (Localization.AtPrime x.1.asIdeal) f ⟨g, hu x x.2⟩ :=
  rfl
theorem const_apply' (f g : R) (U : Opens (PrimeSpectrum.Top R))
    (hu : ∀ x ∈ U, g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) (x : U)
    (hx : g ∈ (x : PrimeSpectrum.Top R).asIdeal.primeCompl) :
    (const R f g U hu).1 x = IsLocalization.mk' _ f ⟨g, hx⟩ :=
  rfl
theorem exists_const (U) (s : (structureSheaf R).1.obj (op U)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    ∃ (V : Opens (PrimeSpectrum.Top R)) (_ : x ∈ V) (i : V ⟶ U) (f g : R) (hg : _),
      const R f g V hg = (structureSheaf R).1.map i.op s :=
  let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩
  ⟨V, hxV, iVU, f, g, fun y hyV => (hfg ⟨y, hyV⟩).1,
    Subtype.eq <| funext fun y => IsLocalization.mk'_eq_iff_eq_mul.2 <| Eq.symm <| (hfg y).2⟩
@[simp]
theorem res_const (f g : R) (U hu V hv i) :
    (structureSheaf R).1.map i (const R f g U hu) = const R f g V hv :=
  rfl
theorem res_const' (f g : R) (V hv) :
    (structureSheaf R).1.map (homOfLE hv).op (const R f g (PrimeSpectrum.basicOpen g) fun _ => id) =
      const R f g V hv :=
  rfl
theorem const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
  Subtype.eq <| funext fun x => IsLocalization.mk'_eq_iff_eq_mul.2 <| by
    rw [RingHom.map_zero]
    exact (mul_eq_zero_of_left rfl ((algebraMap R (Localizations R x)) _)).symm
theorem const_self (f : R) (U hu) : const R f f U hu = 1 :=
  Subtype.eq <| funext fun _ => IsLocalization.mk'_self _ _
theorem const_one (U) : (const R 1 1 U fun _ _ => Submonoid.one_mem _) = 1 :=
  const_self R 1 U _
theorem const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
      const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U fun x hx =>
        Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <| funext fun x => Eq.symm <| IsLocalization.mk'_add _ _
    ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩
theorem const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
    const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
      const R (f₁ * f₂) (g₁ * g₂) U fun x hx => Submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx) :=
  Subtype.eq <|
    funext fun x =>
      Eq.symm <| IsLocalization.mk'_mul _ f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩
theorem const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) :
    const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
  Subtype.eq <|
    funext fun x =>
      IsLocalization.mk'_eq_of_eq (by rw [mul_comm, Subtype.coe_mk, ← h, mul_comm, Subtype.coe_mk])
theorem const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) := by substs hf hg; rfl
theorem const_mul_rev (f g : R) (U hu₁ hu₂) : const R f g U hu₁ * const R g f U hu₂ = 1 := by
  rw [const_mul, const_congr R rfl (mul_comm g f), const_self]
theorem const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
    const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ := by
  rw [const_mul, const_ext]; rw [mul_assoc]
theorem const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
    const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ := by
  rw [mul_comm, const_mul_cancel]
def toOpen (U : Opens (PrimeSpectrum.Top R)) :
    CommRingCat.of R ⟶ (structureSheaf R).1.obj (op U) where
  toFun f :=
    ⟨fun _ => algebraMap R _ f, fun x =>
      ⟨U, x.2, 𝟙 _, f, 1, fun y =>
        ⟨(Ideal.ne_top_iff_one _).1 y.1.2.1, by rw [RingHom.map_one, mul_one]⟩⟩⟩
  map_one' := Subtype.eq <| funext fun _ => RingHom.map_one _
  map_mul' _ _ := Subtype.eq <| funext fun _ => RingHom.map_mul _ _ _
  map_zero' := Subtype.eq <| funext fun _ => RingHom.map_zero _
  map_add' _ _ := Subtype.eq <| funext fun _ => RingHom.map_add _ _ _
@[simp]
theorem toOpen_res (U V : Opens (PrimeSpectrum.Top R)) (i : V ⟶ U) :
    toOpen R U ≫ (structureSheaf R).1.map i.op = toOpen R V :=
  rfl
@[simp]
theorem toOpen_apply (U : Opens (PrimeSpectrum.Top R)) (f : R) (x : U) :
    (toOpen R U f).1 x = algebraMap _ _ f :=
  rfl
theorem toOpen_eq_const (U : Opens (PrimeSpectrum.Top R)) (f : R) :
    toOpen R U f = const R f 1 U fun x _ => (Ideal.ne_top_iff_one _).1 x.2.1 :=
  Subtype.eq <| funext fun _ => Eq.symm <| IsLocalization.mk'_one _ f
def toStalk (x : PrimeSpectrum.Top R) : CommRingCat.of R ⟶ (structureSheaf R).presheaf.stalk x :=
  (toOpen R ⊤ ≫ (structureSheaf R).presheaf.germ _ x (by trivial))
@[simp]
theorem toOpen_germ (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    toOpen R U ≫ (structureSheaf R).presheaf.germ U x hx = toStalk R x := by
  rw [← toOpen_res R ⊤ U (homOfLE le_top : U ⟶ ⊤), Category.assoc, Presheaf.germ_res]; rfl
@[simp]
theorem germ_toOpen
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) (f : R) :
    (structureSheaf R).presheaf.germ U x hx (toOpen R U f) = toStalk R x f := by
  rw [← toOpen_germ]; rfl
theorem toOpen_Γgerm_apply (x : PrimeSpectrum.Top R) (f : R) :
    (structureSheaf R).presheaf.Γgerm x (toOpen R ⊤ f) = toStalk R x f :=
  rfl
@[deprecated (since := "2024-07-30")] alias germ_to_top := toOpen_Γgerm_apply
theorem isUnit_to_basicOpen_self (f : R) : IsUnit (toOpen R (PrimeSpectrum.basicOpen f) f) :=
  isUnit_of_mul_eq_one _ (const R 1 f (PrimeSpectrum.basicOpen f) fun _ => id) <| by
    rw [toOpen_eq_const, const_mul_rev]
theorem isUnit_toStalk (x : PrimeSpectrum.Top R) (f : x.asIdeal.primeCompl) :
    IsUnit (toStalk R x (f : R)) := by
  rw [← germ_toOpen R (PrimeSpectrum.basicOpen (f : R)) x f.2 (f : R)]
  exact RingHom.isUnit_map _ (isUnit_to_basicOpen_self R f)
def localizationToStalk (x : PrimeSpectrum.Top R) :
    CommRingCat.of (Localization.AtPrime x.asIdeal) ⟶ (structureSheaf R).presheaf.stalk x :=
  show Localization.AtPrime x.asIdeal →+* _ from IsLocalization.lift (isUnit_toStalk R x)
@[simp]
theorem localizationToStalk_of (x : PrimeSpectrum.Top R) (f : R) :
    localizationToStalk R x (algebraMap _ (Localization _) f) = toStalk R x f :=
  IsLocalization.lift_eq (S := Localization x.asIdeal.primeCompl) _ f
@[simp]
theorem localizationToStalk_mk' (x : PrimeSpectrum.Top R) (f : R) (s : x.asIdeal.primeCompl) :
    localizationToStalk R x (IsLocalization.mk' (Localization.AtPrime x.asIdeal) f s) =
      (structureSheaf R).presheaf.germ (PrimeSpectrum.basicOpen (s : R)) x s.2
        (const R f s (PrimeSpectrum.basicOpen s) fun _ => id) :=
  (IsLocalization.lift_mk'_spec (S := Localization.AtPrime x.asIdeal) _ _ _ _).2 <| by
    rw [← germ_toOpen R (PrimeSpectrum.basicOpen s) x s.2,
      ← germ_toOpen R (PrimeSpectrum.basicOpen s) x s.2, ← RingHom.map_mul, toOpen_eq_const,
      toOpen_eq_const, const_mul_cancel']
def openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structureSheaf R).1.obj (op U) ⟶ CommRingCat.of (Localization.AtPrime x.asIdeal) where
  toFun s := (s.1 ⟨x, hx⟩ : _)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
@[simp]
theorem coe_openToLocalization (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) :
    (openToLocalization R U x hx :
        (structureSheaf R).1.obj (op U) → Localization.AtPrime x.asIdeal) =
      fun s => (s.1 ⟨x, hx⟩ : _) :=
  rfl
theorem openToLocalization_apply (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R)
    (hx : x ∈ U) (s : (structureSheaf R).1.obj (op U)) :
    openToLocalization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
  rfl
def stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    (structureSheaf R).presheaf.stalk x ⟶ CommRingCat.of (Localization.AtPrime x.asIdeal) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (structureSheaf R).1)
    { pt := _
      ι := { app := fun U =>
        openToLocalization R ((OpenNhds.inclusion _).obj (unop U)) x (unop U).2 } }
@[simp]
theorem germ_comp_stalkToFiberRingHom
    (U : Opens (PrimeSpectrum.Top R)) (x : PrimeSpectrum.Top R) (hx : x ∈ U) :
    (structureSheaf R).presheaf.germ U x hx ≫ stalkToFiberRingHom R x =
      openToLocalization R U x hx :=
  Limits.colimit.ι_desc _ _
@[simp]
theorem stalkToFiberRingHom_germ (U : Opens (PrimeSpectrum.Top R))
    (x : PrimeSpectrum.Top R) (hx : x ∈ U) (s : (structureSheaf R).1.obj (op U)) :
    stalkToFiberRingHom R x ((structureSheaf R).presheaf.germ U x hx s) = s.1 ⟨x, hx⟩ :=
  RingHom.ext_iff.mp (germ_comp_stalkToFiberRingHom R U x hx) s
@[deprecated (since := "2024-07-30")] alias stalkToFiberRingHom_germ' := stalkToFiberRingHom_germ
@[simp]
theorem toStalk_comp_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    toStalk R x ≫ stalkToFiberRingHom R x = algebraMap R (Localization.AtPrime x.asIdeal) := by
  rw [toStalk, Category.assoc, germ_comp_stalkToFiberRingHom]; rfl
@[simp]
theorem stalkToFiberRingHom_toStalk (x : PrimeSpectrum.Top R) (f : R) :
    stalkToFiberRingHom R x (toStalk R x f) = algebraMap R (Localization.AtPrime x.asIdeal) f :=
  RingHom.ext_iff.1 (toStalk_comp_stalkToFiberRingHom R x) _
@[simps]
def stalkIso (x : PrimeSpectrum.Top R) :
    (structureSheaf R).presheaf.stalk x ≅ CommRingCat.of (Localization.AtPrime x.asIdeal) where
  hom := stalkToFiberRingHom R x
  inv := localizationToStalk R x
  hom_inv_id := by
    ext U hxU s
    dsimp only [Category.comp_id, CommRingCat.forget_obj,
      CommRingCat.coe_of, CommRingCat.comp_apply]
    rw [stalkToFiberRingHom_germ]
    obtain ⟨V, hxV, iVU, f, g, (hg : V ≤ PrimeSpectrum.basicOpen _), hs⟩ :=
      exists_const _ _ s x hxU
    rw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localizationToStalk_mk']
    refine (structureSheaf R).presheaf.germ_ext V hxV (homOfLE hg) iVU ?_
    rw [← hs, res_const']
  inv_hom_id :=
    @IsLocalization.ringHom_ext R _ x.asIdeal.primeCompl (Localization.AtPrime x.asIdeal) _ _
      (Localization.AtPrime x.asIdeal) _ _
      (RingHom.comp (stalkToFiberRingHom R x) (localizationToStalk R x))
      (RingHom.id (Localization.AtPrime _)) <| by
        ext f
        rw [RingHom.comp_apply, RingHom.comp_apply, localizationToStalk_of,
          stalkToFiberRingHom_toStalk, RingHom.comp_apply, RingHom.id_apply]
instance (x : PrimeSpectrum R) : IsIso (stalkToFiberRingHom R x) :=
  (stalkIso R x).isIso_hom
instance (x : PrimeSpectrum R) : IsLocalHom (stalkToFiberRingHom R x) :=
  isLocalHom_of_isIso _
instance (x : PrimeSpectrum R) : IsIso (localizationToStalk R x) :=
  (stalkIso R x).isIso_inv
instance (x : PrimeSpectrum R) : IsLocalHom (localizationToStalk R x) :=
  isLocalHom_of_isIso _
@[simp, reassoc]
theorem stalkToFiberRingHom_localizationToStalk (x : PrimeSpectrum.Top R) :
    stalkToFiberRingHom R x ≫ localizationToStalk R x = 𝟙 _ :=
  (stalkIso R x).hom_inv_id
@[simp, reassoc]
theorem localizationToStalk_stalkToFiberRingHom (x : PrimeSpectrum.Top R) :
    localizationToStalk R x ≫ stalkToFiberRingHom R x = 𝟙 _ :=
  (stalkIso R x).inv_hom_id
def toBasicOpen (f : R) :
    Localization.Away f →+* (structureSheaf R).1.obj (op <| PrimeSpectrum.basicOpen f) :=
  IsLocalization.Away.lift f (isUnit_to_basicOpen_self R f)
@[simp]
theorem toBasicOpen_mk' (s f : R) (g : Submonoid.powers s) :
    toBasicOpen R s (IsLocalization.mk' (Localization.Away s) f g) =
      const R f g (PrimeSpectrum.basicOpen s) fun _ hx => Submonoid.powers_le.2 hx g.2 :=
  (IsLocalization.lift_mk'_spec _ _ _ _).2 <| by
    rw [toOpen_eq_const, toOpen_eq_const, const_mul_cancel']
@[simp]
theorem localization_toBasicOpen (f : R) :
    RingHom.comp (toBasicOpen R f) (algebraMap R (Localization.Away f)) =
    toOpen R (PrimeSpectrum.basicOpen f) :=
  RingHom.ext fun g => by
    rw [toBasicOpen, IsLocalization.Away.lift, RingHom.comp_apply, IsLocalization.lift_eq]
@[simp]
theorem toBasicOpen_to_map (s f : R) :
    toBasicOpen R s (algebraMap R (Localization.Away s) f) =
      const R f 1 (PrimeSpectrum.basicOpen s) fun _ _ => Submonoid.one_mem _ :=
  (IsLocalization.lift_eq _ _).trans <| toOpen_eq_const _ _ _
theorem toBasicOpen_injective (f : R) : Function.Injective (toBasicOpen R f) := by
  intro s t h_eq
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) s
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) t
  simp only [toBasicOpen_mk'] at h_eq
  rw [IsLocalization.eq]
  let I : Ideal R :=
    { carrier := { r : R | r * (d * a) = r * (b * c) }
      zero_mem' := by simp only [Set.mem_setOf_eq, zero_mul]
      add_mem' := fun {r₁ r₂} hr₁ hr₂ => by dsimp at hr₁ hr₂ ⊢; simp only [add_mul, hr₁, hr₂]
      smul_mem' := fun {r₁ r₂} hr₂ => by dsimp at hr₂ ⊢; simp only [mul_assoc, hr₂] }
  suffices f ∈ I.radical by
    cases' this with n hn
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro p hfp
  contrapose hfp
  rw [PrimeSpectrum.mem_zeroLocus, Set.not_subset]
  have := congr_fun (congr_arg Subtype.val h_eq) ⟨p, hfp⟩
  dsimp at this
  rw [IsLocalization.eq (S := Localization.AtPrime p.asIdeal)] at this
  cases' this with r hr
  exact ⟨r.1, hr, r.2⟩
theorem locally_const_basicOpen (U : Opens (PrimeSpectrum.Top R))
    (s : (structureSheaf R).1.obj (op U)) (x : U) :
    ∃ (f g : R) (i : PrimeSpectrum.basicOpen g ⟶ U), x.1 ∈ PrimeSpectrum.basicOpen g ∧
      (const R f g (PrimeSpectrum.basicOpen g) fun _ hy => hy) =
      (structureSheaf R).1.map i.op s := by
  obtain ⟨V, hxV : x.1 ∈ V.1, iVU, f, g, hVDg : V ≤ PrimeSpectrum.basicOpen g, s_eq⟩ :=
    exists_const R U s x.1 x.2
  obtain ⟨_, ⟨h, rfl⟩, hxDh, hDhV : PrimeSpectrum.basicOpen h ≤ V⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  cases' (PrimeSpectrum.basicOpen_le_basicOpen_iff h g).mp (Set.Subset.trans hDhV hVDg) with n hn
  replace hn := Ideal.mul_mem_right h (Ideal.span {g}) hn
  rw [← pow_succ, Ideal.mem_span_singleton'] at hn
  cases' hn with c hc
  have basic_opens_eq := PrimeSpectrum.basicOpen_pow h (n + 1) (by omega)
  have i_basic_open := eqToHom basic_opens_eq ≫ homOfLE hDhV
  use f * c, h ^ (n + 1), i_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh
  rw [op_comp, Functor.map_comp] 
  change const R _ _ _ _ = (structureSheaf R).1.map i_basic_open.op
    ((structureSheaf R).1.map iVU.op s)
  rw [← s_eq, res_const]
  swap
  · intro y hy
    rw [basic_opens_eq] at hy
    exact (Set.Subset.trans hDhV hVDg : _) hy
  apply const_ext
  rw [mul_assoc f c g, hc]
theorem normalize_finite_fraction_representation (U : Opens (PrimeSpectrum.Top R))
    (s : (structureSheaf R).1.obj (op U)) {ι : Type*} (t : Finset ι) (a h : ι → R)
    (iDh : ∀ i : ι, PrimeSpectrum.basicOpen (h i) ⟶ U)
    (h_cover : U ≤ ⨆ i ∈ t, PrimeSpectrum.basicOpen (h i))
    (hs :
      ∀ i : ι,
        (const R (a i) (h i) (PrimeSpectrum.basicOpen (h i)) fun _ hy => hy) =
          (structureSheaf R).1.map (iDh i).op s) :
    ∃ (a' h' : ι → R) (iDh' : ∀ i : ι, PrimeSpectrum.basicOpen (h' i) ⟶ U),
      (U ≤ ⨆ i ∈ t, PrimeSpectrum.basicOpen (h' i)) ∧
        (∀ (i) (_ : i ∈ t) (j) (_ : j ∈ t), a' i * h' j = h' i * a' j) ∧
          ∀ i ∈ t,
            (structureSheaf R).1.map (iDh' i).op s =
              const R (a' i) (h' i) (PrimeSpectrum.basicOpen (h' i)) fun _ hy => hy := by
  have fractions_eq :
    ∀ i j : ι,
      IsLocalization.mk' (Localization.Away (h i * h j))
        (a i * h j) ⟨h i * h j, Submonoid.mem_powers _⟩ =
      IsLocalization.mk' _ (h i * a j) ⟨h i * h j, Submonoid.mem_powers _⟩ := by
    intro i j
    let D := PrimeSpectrum.basicOpen (h i * h j)
    let iDi : D ⟶ PrimeSpectrum.basicOpen (h i) := homOfLE (PrimeSpectrum.basicOpen_mul_le_left _ _)
    let iDj : D ⟶ PrimeSpectrum.basicOpen (h j) :=
      homOfLE (PrimeSpectrum.basicOpen_mul_le_right _ _)
    apply toBasicOpen_injective R (h i * h j)
    rw [toBasicOpen_mk', toBasicOpen_mk']
    simp only []
    trans
    on_goal 1 =>
      convert congr_arg ((structureSheaf R).1.map iDj.op) (hs j).symm using 1
      convert congr_arg ((structureSheaf R).1.map iDi.op) (hs i) using 1
    all_goals rw [res_const]; apply const_ext; ring
    exacts [PrimeSpectrum.basicOpen_mul_le_left _ _, PrimeSpectrum.basicOpen_mul_le_right _ _]
  have exists_power :
    ∀ i j : ι, ∃ n : ℕ, a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n := by
    intro i j
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := IsLocalization.eq.mp (fractions_eq i j)
    use n + 1
    rw [pow_succ]
    dsimp at hc
    convert hc using 1 <;> ring
  let n := fun p : ι × ι => (exists_power p.1 p.2).choose
  have n_spec := fun p : ι × ι => (exists_power p.fst p.snd).choose_spec
  let N := (t ×ˢ t).sup n
  have basic_opens_eq : ∀ i : ι, PrimeSpectrum.basicOpen (h i ^ (N + 1)) =
    PrimeSpectrum.basicOpen (h i) := fun i => PrimeSpectrum.basicOpen_pow _ _ (by omega)
  refine
    ⟨fun i => a i * h i ^ N, fun i => h i ^ (N + 1), fun i => eqToHom (basic_opens_eq i) ≫ iDh i,
      ?_, ?_, ?_⟩
  · simpa only [basic_opens_eq] using h_cover
  · intro i hi j hj
    have n_le_N : n (i, j) ≤ N := Finset.le_sup (Finset.mem_product.mpr ⟨hi, hj⟩)
    cases' Nat.le.dest n_le_N with k hk
    simp only [← hk, pow_add, pow_one]
    convert congr_arg (fun z => z * (h i * h j) ^ k) (n_spec (i, j)) using 1 <;>
      · simp only [n, mul_pow]; ring
  intro i _
  rw [op_comp, Functor.map_comp]
  change (structureSheaf R).1.map (eqToHom (basic_opens_eq _)).op
    ((structureSheaf R).1.map (iDh i).op s) = _
  rw [← hs, res_const]
  swap
  · exact (basic_opens_eq i).le
  apply const_ext
  dsimp
  rw [pow_succ]
  ring
set_option linter.unusedVariables false in
theorem toBasicOpen_surjective (f : R) : Function.Surjective (toBasicOpen R f) := by
  intro s
  let ι : Type u := PrimeSpectrum.basicOpen f
  choose a' h' iDh' hxDh' s_eq' using locally_const_basicOpen R (PrimeSpectrum.basicOpen f) s
  obtain ⟨t, ht_cover'⟩ :=
    (PrimeSpectrum.isCompact_basicOpen f).elim_finite_subcover
      (fun i : ι => PrimeSpectrum.basicOpen (h' i)) (fun i => PrimeSpectrum.isOpen_basicOpen)
      fun x hx => by rw [Set.mem_iUnion]; exact ⟨⟨x, hx⟩, hxDh' ⟨x, hx⟩⟩
  simp only [← Opens.coe_iSup, SetLike.coe_subset_coe] at ht_cover'
  obtain ⟨a, h, iDh, ht_cover, ah_ha, s_eq⟩ :=
    normalize_finite_fraction_representation R (PrimeSpectrum.basicOpen f)
      s t a' h' iDh' ht_cover' s_eq'
  clear s_eq' iDh' hxDh' ht_cover' a' h'
  rw [← SetLike.coe_subset_coe, Opens.coe_iSup] at ht_cover
  replace ht_cover : (PrimeSpectrum.basicOpen f : Set <| PrimeSpectrum R) ⊆
      ⋃ (i : ι) (x : i ∈ t), (PrimeSpectrum.basicOpen (h i) : Set _) := by
    convert ht_cover using 2
    exact funext fun j => by rw [Opens.coe_iSup]
  obtain ⟨n, hn⟩ : f ∈ (Ideal.span (h '' ↑t)).radical := by
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.zeroLocus_span]
    replace ht_cover : (PrimeSpectrum.zeroLocus {f})ᶜ ⊆
        ⋃ (i : ι) (x : i ∈ t), (PrimeSpectrum.zeroLocus {h i})ᶜ := by
      convert ht_cover
      · rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
      · simp only [Opens.iSup_mk, Opens.carrier_eq_coe, PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    rw [Set.compl_subset_comm] at ht_cover
    simp_rw [Set.compl_iUnion, compl_compl, ← PrimeSpectrum.zeroLocus_iUnion,
      ← Finset.set_biUnion_coe, ← Set.image_eq_iUnion] at ht_cover
    apply PrimeSpectrum.vanishingIdeal_anti_mono ht_cover
    exact PrimeSpectrum.subset_vanishingIdeal_zeroLocus {f} (Set.mem_singleton f)
  replace hn := Ideal.mul_mem_right f _ hn
  erw [← pow_succ, Finsupp.mem_span_image_iff_linearCombination] at hn
  rcases hn with ⟨b, b_supp, hb⟩
  rw [Finsupp.linearCombination_apply_of_mem_supported R b_supp] at hb
  dsimp at hb
  use
    IsLocalization.mk' (Localization.Away f) (∑ i ∈ t, b i * a i)
      (⟨f ^ (n + 1), n + 1, rfl⟩ : Submonoid.powers _)
  rw [toBasicOpen_mk']
  let tt := ((t : Set (PrimeSpectrum.basicOpen f)) : Type u)
  apply
    (structureSheaf R).eq_of_locally_eq' (fun i : tt => PrimeSpectrum.basicOpen (h i))
      (PrimeSpectrum.basicOpen f) fun i : tt => iDh i
  · 
    intro x hx
    erw [TopologicalSpace.Opens.mem_iSup]
    have := ht_cover hx
    rw [← Finset.set_biUnion_coe, Set.mem_iUnion₂] at this
    rcases this with ⟨i, i_mem, x_mem⟩
    exact ⟨⟨i, i_mem⟩, x_mem⟩
  rintro ⟨i, hi⟩
  dsimp
  change (structureSheaf R).1.map _ _ = (structureSheaf R).1.map _ _
  rw [s_eq i hi, res_const]
  swap
  · intro y hy
    change y ∈ PrimeSpectrum.basicOpen (f ^ (n + 1))
    rw [PrimeSpectrum.basicOpen_pow f (n + 1) (by omega)]
    exact (leOfHom (iDh i) : _) hy
  apply const_ext
  rw [← hb, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, ah_ha j hj i hi]
  ring
instance isIso_toBasicOpen (f : R) :
    IsIso (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f) :=
  haveI : IsIso ((forget CommRingCat).map
      (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f)) :=
    (isIso_iff_bijective _).mpr ⟨toBasicOpen_injective R f, toBasicOpen_surjective R f⟩
  isIso_of_reflects_iso _ (forget CommRingCat)
def basicOpenIso (f : R) :
    (structureSheaf R).1.obj (op (PrimeSpectrum.basicOpen f)) ≅
    CommRingCat.of (Localization.Away f) :=
  (asIso (show CommRingCat.of (Localization.Away f) ⟶ _ from toBasicOpen R f)).symm
instance stalkAlgebra (p : PrimeSpectrum R) : Algebra R ((structureSheaf R).presheaf.stalk p) :=
  (toStalk R p).toAlgebra
@[simp]
theorem stalkAlgebra_map (p : PrimeSpectrum R) (r : R) :
    algebraMap R ((structureSheaf R).presheaf.stalk p) r = toStalk R p r :=
  rfl
instance IsLocalization.to_stalk (p : PrimeSpectrum R) :
    IsLocalization.AtPrime ((structureSheaf R).presheaf.stalk p) p.asIdeal := by
  convert (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.AtPrime p.asIdeal) _
          (stalkIso R p).symm.commRingCatIsoToRingEquiv).mp
      Localization.isLocalization
  apply Algebra.algebra_ext
  intro
  rw [stalkAlgebra_map]
  congr 1
  change toStalk R p = _ ≫ (stalkIso R p).inv
  rw [Iso.eq_comp_inv]
  exact toStalk_comp_stalkToFiberRingHom R p
instance openAlgebra (U : (Opens (PrimeSpectrum R))ᵒᵖ) : Algebra R ((structureSheaf R).val.obj U) :=
  (toOpen R (unop U)).toAlgebra
@[simp]
theorem openAlgebra_map (U : (Opens (PrimeSpectrum R))ᵒᵖ) (r : R) :
    algebraMap R ((structureSheaf R).val.obj U) r = toOpen R (unop U) r :=
  rfl
instance IsLocalization.to_basicOpen (r : R) :
    IsLocalization.Away r ((structureSheaf R).val.obj (op <| PrimeSpectrum.basicOpen r)) := by
  convert (IsLocalization.isLocalization_iff_of_ringEquiv (S := Localization.Away r) _
      (basicOpenIso R r).symm.commRingCatIsoToRingEquiv).mp
      Localization.isLocalization
  apply Algebra.algebra_ext
  intro x
  congr 1
  exact (localization_toBasicOpen R r).symm
instance to_basicOpen_epi (r : R) : Epi (toOpen R (PrimeSpectrum.basicOpen r)) :=
  ⟨fun _ _ h => IsLocalization.ringHom_ext (Submonoid.powers r) h⟩
@[elementwise]
theorem to_global_factors :
    toOpen R ⊤ =
      CommRingCat.ofHom (algebraMap R (Localization.Away (1 : R))) ≫
        toBasicOpen R (1 : R) ≫
        (structureSheaf R).1.map (eqToHom PrimeSpectrum.basicOpen_one.symm).op := by
  rw [← Category.assoc]
  change toOpen R ⊤ =
    (CommRingCat.ofHom <| (toBasicOpen R 1).comp (algebraMap R (Localization.Away 1))) ≫
    (structureSheaf R).1.map (eqToHom _).op
  unfold CommRingCat.ofHom
  rw [localization_toBasicOpen R, toOpen_res]
instance isIso_to_global : IsIso (toOpen R ⊤) := by
  let hom := CommRingCat.ofHom (algebraMap R (Localization.Away (1 : R)))
  haveI : IsIso hom :=
    (IsLocalization.atOne R (Localization.Away (1 : R))).toRingEquiv.toCommRingCatIso.isIso_hom
  rw [to_global_factors R]
  infer_instance
@[simps!]
def globalSectionsIso : CommRingCat.of R ≅ (structureSheaf R).1.obj (op ⊤) :=
  asIso (toOpen R ⊤)
attribute [nolint simpNF] AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom_apply_coe
@[simp]
theorem globalSectionsIso_hom (R : CommRingCat) : (globalSectionsIso R).hom = toOpen R ⊤ :=
  rfl
@[simp, reassoc, elementwise]
theorem toStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R} (h : x ⤳ y) :
    toStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h = toStalk R x := by
  dsimp [toStalk]; simp [-toOpen_germ]
@[simp, reassoc, elementwise]
theorem localizationToStalk_stalkSpecializes {R : Type*} [CommRing R] {x y : PrimeSpectrum R}
    (h : x ⤳ y) :
    StructureSheaf.localizationToStalk R y ≫ (structureSheaf R).presheaf.stalkSpecializes h =
      CommRingCat.ofHom (PrimeSpectrum.localizationMapOfSpecializes h) ≫
        StructureSheaf.localizationToStalk R x := by
  apply IsLocalization.ringHom_ext (S := Localization.AtPrime y.asIdeal) y.asIdeal.primeCompl
  erw [RingHom.comp_assoc]
  conv_rhs => erw [RingHom.comp_assoc]
  dsimp [CommRingCat.ofHom, localizationToStalk, PrimeSpectrum.localizationMapOfSpecializes]
  rw [IsLocalization.lift_comp, IsLocalization.lift_comp, IsLocalization.lift_comp]
  exact toStalk_stalkSpecializes h
@[simp, reassoc, elementwise]
theorem stalkSpecializes_stalk_to_fiber {R : Type*} [CommRing R] {x y : PrimeSpectrum R}
    (h : x ⤳ y) :
    (structureSheaf R).presheaf.stalkSpecializes h ≫ StructureSheaf.stalkToFiberRingHom R x =
      StructureSheaf.stalkToFiberRingHom R y ≫
      (show CommRingCat.of (Localization.AtPrime y.asIdeal) ⟶
        CommRingCat.of (Localization.AtPrime x.asIdeal)
        from PrimeSpectrum.localizationMapOfSpecializes h) := by
  change _ ≫ (StructureSheaf.stalkIso R x).hom = (StructureSheaf.stalkIso R y).hom ≫ _
  rw [← Iso.eq_comp_inv, Category.assoc, ← Iso.inv_comp_eq]
  exact localizationToStalk_stalkSpecializes h
section Comap
variable {R} {S : Type u} [CommRing S] {P : Type u} [CommRing P]
def comapFun (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (s : ∀ x : U, Localizations R x) (y : V) :
    Localizations S y :=
  Localization.localRingHom (PrimeSpectrum.comap f y.1).asIdeal _ f rfl
    (s ⟨PrimeSpectrum.comap f y.1, hUV y.2⟩ : _)
theorem comapFunIsLocallyFraction (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : ∀ x : U, Localizations R x) (hs : (isLocallyFraction R).toPrelocalPredicate.pred s) :
    (isLocallyFraction S).toPrelocalPredicate.pred (comapFun f U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨PrimeSpectrum.comap f p, hUV hpV⟩ with ⟨W, m, iWU, a, b, h_frac⟩
  refine ⟨Opens.comap (PrimeSpectrum.comap f) W ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, f a, f b, ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  specialize h_frac ⟨PrimeSpectrum.comap f q, hqW⟩
  refine ⟨h_frac.1, ?_⟩
  dsimp only [comapFun]
  erw [← Localization.localRingHom_to_map (PrimeSpectrum.comap f q).asIdeal, ← RingHom.map_mul,
    h_frac.2, Localization.localRingHom_to_map]
  rfl
def comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) (V : Opens (PrimeSpectrum.Top S))
    (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (structureSheaf R).1.obj (op U) →+* (structureSheaf S).1.obj (op V) where
  toFun s := ⟨comapFun f U V hUV s.1, comapFunIsLocallyFraction f U V hUV s.1 s.2⟩
  map_one' :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_one, Pi.one_apply, RingHom.map_one]
        rfl
  map_zero' :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_zero, Pi.zero_apply, RingHom.map_zero]
        rfl
  map_add' s t :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_add, Pi.add_apply, RingHom.map_add]
        rfl
  map_mul' s t :=
    Subtype.ext <|
      funext fun p => by
        dsimp
        rw [comapFun, (sectionsSubring R (op U)).coe_mul, Pi.mul_apply, RingHom.map_mul]
        rfl
@[simp]
theorem comap_apply (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1)
    (s : (structureSheaf R).1.obj (op U)) (p : V) :
    (comap f U V hUV s).1 p =
      Localization.localRingHom (PrimeSpectrum.comap f p.1).asIdeal _ f rfl
        (s.1 ⟨PrimeSpectrum.comap f p.1, hUV p.2⟩ : _) :=
  rfl
theorem comap_const (f : R →+* S) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (hUV : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) (a b : R)
    (hb : ∀ x : PrimeSpectrum R, x ∈ U → b ∈ x.asIdeal.primeCompl) :
    comap f U V hUV (const R a b U hb) =
      const S (f a) (f b) V fun p hpV => hb (PrimeSpectrum.comap f p) (hUV hpV) :=
  Subtype.eq <|
    funext fun p => by
      rw [comap_apply, const_apply, const_apply, Localization.localRingHom_mk']
theorem comap_id_eq_map (U V : Opens (PrimeSpectrum.Top R)) (iVU : V ⟶ U) :
    (comap (RingHom.id R) U V fun _ hpV => leOfHom iVU <| hpV) =
      (structureSheaf R).1.map iVU.op :=
  RingHom.ext fun s => Subtype.eq <| funext fun p => by
    rw [comap_apply]
    obtain ⟨W, hpW, iWU, h⟩ := s.2 (iVU p)
    obtain ⟨a, b, h'⟩ := h.eq_mk'
    obtain ⟨hb₁, s_eq₁⟩ := h' ⟨p, hpW⟩
    obtain ⟨hb₂, s_eq₂⟩ :=
      h' ⟨PrimeSpectrum.comap (RingHom.id _) p.1, hpW⟩
    dsimp only at s_eq₁ s_eq₂
    erw [s_eq₂, Localization.localRingHom_mk', ← s_eq₁, ← res_apply _ _ _ iVU]
theorem comap_id {U V : Opens (PrimeSpectrum.Top R)} (hUV : U = V) :
    (comap (RingHom.id R) U V fun p hpV => by rwa [hUV, PrimeSpectrum.comap_id]) =
      eqToHom (show (structureSheaf R).1.obj (op U) = _ by rw [hUV]) := by
  rw [comap_id_eq_map U V (eqToHom hUV.symm), eqToHom_op, eqToHom_map]
@[simp]
theorem comap_id' (U : Opens (PrimeSpectrum.Top R)) :
    (comap (RingHom.id R) U U fun p hpU => by rwa [PrimeSpectrum.comap_id]) = RingHom.id _ := by
  rw [comap_id rfl]; rfl
theorem comap_comp (f : R →+* S) (g : S →+* P) (U : Opens (PrimeSpectrum.Top R))
    (V : Opens (PrimeSpectrum.Top S)) (W : Opens (PrimeSpectrum.Top P))
    (hUV : ∀ p ∈ V, PrimeSpectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, PrimeSpectrum.comap g p ∈ V) :
    (comap (g.comp f) U W fun p hpW => hUV (PrimeSpectrum.comap g p) (hVW p hpW)) =
      (comap g V W hVW).comp (comap f U V hUV) :=
  RingHom.ext fun s =>
    Subtype.eq <|
      funext fun p => by
        rw [comap_apply]
        rw [Localization.localRingHom_comp _ (PrimeSpectrum.comap g p.1).asIdeal] <;>
        rfl
@[elementwise, reassoc]
theorem toOpen_comp_comap (f : R →+* S) (U : Opens (PrimeSpectrum.Top R)) :
    (toOpen R U ≫ comap f U (Opens.comap (PrimeSpectrum.comap f) U) fun _ => id) =
      CommRingCat.ofHom f ≫ toOpen S _ :=
  RingHom.ext fun _ => Subtype.eq <| funext fun _ => Localization.localRingHom_to_map _ _ _ _ _
lemma comap_basicOpen (f : R →+* S) (x : R) :
    comap f (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (f x))
        (PrimeSpectrum.comap_basicOpen f x).le =
      IsLocalization.map (M := .powers x) (T := .powers (f x)) _ f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _)) :=
  IsLocalization.ringHom_ext (.powers x) <| by simpa using toOpen_comp_comap f _
end Comap
end StructureSheaf
end AlgebraicGeometry