import Mathlib.Data.Int.Cast.Prod
import Mathlib.Algebra.GroupWithZero.Prod
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Equiv
variable {R R' S S' T : Type*}
namespace Prod
instance instDistrib [Distrib R] [Distrib S] : Distrib (R × S) :=
  { left_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨left_distrib _ _ _, left_distrib _ _ _⟩
    right_distrib := fun _ _ _ => mk.inj_iff.mpr ⟨right_distrib _ _ _, right_distrib _ _ _⟩ }
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] :
    NonUnitalNonAssocSemiring (R × S) :=
  { inferInstanceAs (AddCommMonoid (R × S)),
    inferInstanceAs (Distrib (R × S)),
    inferInstanceAs (MulZeroClass (R × S)) with }
instance instNonUnitalSemiring [NonUnitalSemiring R] [NonUnitalSemiring S] :
    NonUnitalSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (SemigroupWithZero (R × S)) with }
instance instNonAssocSemiring [NonAssocSemiring R] [NonAssocSemiring S] :
    NonAssocSemiring (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocSemiring (R × S)),
    inferInstanceAs (MulZeroOneClass (R × S)),
    inferInstanceAs (AddMonoidWithOne (R × S)) with }
instance instSemiring [Semiring R] [Semiring S] : Semiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (MonoidWithZero (R × S)) with }
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] [NonUnitalCommSemiring S] :
    NonUnitalCommSemiring (R × S) :=
  { inferInstanceAs (NonUnitalSemiring (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }
instance instCommSemiring [CommSemiring R] [CommSemiring S] : CommSemiring (R × S) :=
  { inferInstanceAs (Semiring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S] :
    NonUnitalNonAssocRing (R × S) :=
  { inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (NonUnitalNonAssocSemiring (R × S)) with }
instance instNonUnitalRing [NonUnitalRing R] [NonUnitalRing S] : NonUnitalRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonUnitalSemiring (R × S)) with }
instance instNonAssocRing [NonAssocRing R] [NonAssocRing S] : NonAssocRing (R × S) :=
  { inferInstanceAs (NonUnitalNonAssocRing (R × S)),
    inferInstanceAs (NonAssocSemiring (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }
instance instRing [Ring R] [Ring S] : Ring (R × S) :=
  { inferInstanceAs (Semiring (R × S)),
    inferInstanceAs (AddCommGroup (R × S)),
    inferInstanceAs (AddGroupWithOne (R × S)) with }
instance instNonUnitalCommRing [NonUnitalCommRing R] [NonUnitalCommRing S] :
    NonUnitalCommRing (R × S) :=
  { inferInstanceAs (NonUnitalRing (R × S)), inferInstanceAs (CommSemigroup (R × S)) with }
instance instCommRing [CommRing R] [CommRing S] : CommRing (R × S) :=
  { inferInstanceAs (Ring (R × S)), inferInstanceAs (CommMonoid (R × S)) with }
end Prod
namespace NonUnitalRingHom
variable (R S) [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
def fst : R × S →ₙ+* R :=
  { MulHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
def snd : R × S →ₙ+* S :=
  { MulHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
variable {R S}
@[simp]
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl
@[simp]
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl
section Prod
variable [NonUnitalNonAssocSemiring T] (f : R →ₙ+* S) (g : R →ₙ+* T)
protected def prod (f : R →ₙ+* S) (g : R →ₙ+* T) : R →ₙ+* S × T :=
  { MulHom.prod (f : MulHom R S) (g : MulHom R T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
@[simp]
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl
@[simp]
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl
@[simp]
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
theorem prod_unique (f : R →ₙ+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]
end Prod
section prodMap
variable [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring S'] [NonUnitalNonAssocSemiring T]
variable (f : R →ₙ+* R') (g : S →ₙ+* S')
def prodMap : R × S →ₙ+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
@[simp]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
theorem prod_comp_prodMap (f : T →ₙ+* R) (g : T →ₙ+* S) (f' : R →ₙ+* R') (g' : S →ₙ+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
end prodMap
end NonUnitalRingHom
namespace RingHom
variable (R S) [NonAssocSemiring R] [NonAssocSemiring S]
def fst : R × S →+* R :=
  { MonoidHom.fst R S, AddMonoidHom.fst R S with toFun := Prod.fst }
def snd : R × S →+* S :=
  { MonoidHom.snd R S, AddMonoidHom.snd R S with toFun := Prod.snd }
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (fst R S) := ⟨(⟨⟨·, 0⟩, rfl⟩)⟩
instance (R S) [Semiring R] [Semiring S] : RingHomSurjective (snd R S) := ⟨(⟨⟨0, ·⟩, rfl⟩)⟩
variable {R S}
@[simp]
theorem coe_fst : ⇑(fst R S) = Prod.fst :=
  rfl
@[simp]
theorem coe_snd : ⇑(snd R S) = Prod.snd :=
  rfl
section Prod
variable [NonAssocSemiring T] (f : R →+* S) (g : R →+* T)
protected def prod (f : R →+* S) (g : R →+* T) : R →+* S × T :=
  { MonoidHom.prod (f : R →* S) (g : R →* T), AddMonoidHom.prod (f : R →+ S) (g : R →+ T) with
    toFun := fun x => (f x, g x) }
@[simp]
theorem prod_apply (x) : f.prod g x = (f x, g x) :=
  rfl
@[simp]
theorem fst_comp_prod : (fst S T).comp (f.prod g) = f :=
  ext fun _ => rfl
@[simp]
theorem snd_comp_prod : (snd S T).comp (f.prod g) = g :=
  ext fun _ => rfl
theorem prod_unique (f : R →+* S × T) : ((fst S T).comp f).prod ((snd S T).comp f) = f :=
  ext fun x => by simp only [prod_apply, coe_fst, coe_snd, comp_apply]
end Prod
section prodMap
variable [NonAssocSemiring R'] [NonAssocSemiring S'] [NonAssocSemiring T]
variable (f : R →+* R') (g : S →+* S')
def prodMap : R × S →+* R' × S' :=
  (f.comp (fst R S)).prod (g.comp (snd R S))
theorem prodMap_def : prodMap f g = (f.comp (fst R S)).prod (g.comp (snd R S)) :=
  rfl
@[simp]
theorem coe_prodMap : ⇑(prodMap f g) = Prod.map f g :=
  rfl
theorem prod_comp_prodMap (f : T →+* R) (g : T →+* S) (f' : R →+* R') (g' : S →+* S') :
    (f'.prodMap g').comp (f.prod g) = (f'.comp f).prod (g'.comp g) :=
  rfl
end prodMap
end RingHom
namespace RingEquiv
variable [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring R'] [NonAssocSemiring S']
def prodComm : R × S ≃+* S × R :=
  { AddEquiv.prodComm, MulEquiv.prodComm with }
@[simp]
theorem coe_prodComm : ⇑(prodComm : R × S ≃+* S × R) = Prod.swap :=
  rfl
@[simp]
theorem coe_prodComm_symm : ⇑(prodComm : R × S ≃+* S × R).symm = Prod.swap :=
  rfl
@[simp]
theorem fst_comp_coe_prodComm :
    (RingHom.fst S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.snd R S :=
  RingHom.ext fun _ => rfl
@[simp]
theorem snd_comp_coe_prodComm :
    (RingHom.snd S R).comp ↑(prodComm : R × S ≃+* S × R) = RingHom.fst R S :=
  RingHom.ext fun _ => rfl
section
variable (R R' S S')
@[simps apply]
def prodProdProdComm : (R × R') × S × S' ≃+* (R × S) × R' × S' :=
  { AddEquiv.prodProdProdComm R R' S S', MulEquiv.prodProdProdComm R R' S S' with
    toFun := fun rrss => ((rrss.1.1, rrss.2.1), (rrss.1.2, rrss.2.2))
    invFun := fun rsrs => ((rsrs.1.1, rsrs.2.1), (rsrs.1.2, rsrs.2.2)) }
@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm R R' S S').symm = prodProdProdComm R S R' S' :=
  rfl
@[simp]
theorem prodProdProdComm_toAddEquiv :
    (prodProdProdComm R R' S S' : _ ≃+ _) = AddEquiv.prodProdProdComm R R' S S' :=
  rfl
@[simp]
theorem prodProdProdComm_toMulEquiv :
    (prodProdProdComm R R' S S' : _ ≃* _) = MulEquiv.prodProdProdComm R R' S S' :=
  rfl
@[simp]
theorem prodProdProdComm_toEquiv :
    (prodProdProdComm R R' S S' : _ ≃ _) = Equiv.prodProdProdComm R R' S S' :=
  rfl
end
variable (R S) [Subsingleton S]
@[simps]
def prodZeroRing : R ≃+* R × S where
  toFun x := (x, 0)
  invFun := Prod.fst
  map_add' := by simp
  map_mul' := by simp
  left_inv _ := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
@[simps]
def zeroRingProd : R ≃+* S × R where
  toFun x := (0, x)
  invFun := Prod.snd
  map_add' := by simp
  map_mul' := by simp
  left_inv _ := rfl
  right_inv x := by cases x; simp [eq_iff_true_of_subsingleton]
end RingEquiv
theorem false_of_nontrivial_of_product_domain (R S : Type*) [Ring R] [Ring S] [IsDomain (R × S)]
    [Nontrivial R] [Nontrivial S] : False := by
  have :=
    NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero (show ((0 : R), (1 : S)) * (1, 0) = 0 by simp)
  rw [Prod.mk_eq_zero, Prod.mk_eq_zero] at this
  rcases this with (⟨_, h⟩ | ⟨h, _⟩)
  · exact zero_ne_one h.symm
  · exact zero_ne_one h.symm