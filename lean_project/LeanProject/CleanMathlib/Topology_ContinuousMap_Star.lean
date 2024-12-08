import Mathlib.Topology.Algebra.Star
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Topology.ContinuousMap.Algebra
namespace ContinuousMap
section StarStructure
variable {R α β : Type*}
variable [TopologicalSpace α] [TopologicalSpace β]
section Star
variable [Star β] [ContinuousStar β]
instance : Star C(α, β) where star f := starContinuousMap.comp f
@[simp]
theorem coe_star (f : C(α, β)) : ⇑(star f) = star (⇑f) :=
  rfl
@[simp]
theorem star_apply (f : C(α, β)) (x : α) : star f x = star (f x) :=
  rfl
instance instTrivialStar [TrivialStar β] : TrivialStar C(α, β) where
  star_trivial _ := ext fun _ => star_trivial _
end Star
instance [InvolutiveStar β] [ContinuousStar β] : InvolutiveStar C(α, β) where
  star_involutive _ := ext fun _ => star_star _
instance starAddMonoid [AddMonoid β] [ContinuousAdd β] [StarAddMonoid β] [ContinuousStar β] :
    StarAddMonoid C(α, β) where
  star_add _ _ := ext fun _ => star_add _ _
instance starMul [Mul β] [ContinuousMul β] [StarMul β] [ContinuousStar β] :
    StarMul C(α, β) where
  star_mul _ _ := ext fun _ => star_mul _ _
instance [NonUnitalNonAssocSemiring β] [TopologicalSemiring β] [StarRing β] [ContinuousStar β] :
    StarRing C(α, β) :=
  { ContinuousMap.starAddMonoid, ContinuousMap.starMul with }
instance [Star R] [Star β] [SMul R β] [StarModule R β] [ContinuousStar β]
    [ContinuousConstSMul R β] : StarModule R C(α, β) where
  star_smul _ _ := ext fun _ => star_smul _ _
end StarStructure
section Precomposition
variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]
@[simps]
def compStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₐ[𝕜] C(X, A) where
  toFun g := g.comp f
  map_one' := one_comp _
  map_mul' _ _ := rfl
  map_zero' := zero_comp f
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl
theorem compStarAlgHom'_id : compStarAlgHom' 𝕜 A (ContinuousMap.id X) = StarAlgHom.id 𝕜 C(X, A) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
theorem compStarAlgHom'_comp (g : C(Y, Z)) (f : C(X, Y)) :
    compStarAlgHom' 𝕜 A (g.comp f) = (compStarAlgHom' 𝕜 A f).comp (compStarAlgHom' 𝕜 A g) :=
  StarAlgHom.ext fun _ => ContinuousMap.ext fun _ => rfl
end Precomposition
section Postcomposition
variable (X : Type*) {𝕜 A B C : Type*} [TopologicalSpace X] [CommSemiring 𝕜]
variable [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [Star A]
variable [ContinuousStar A] [Algebra 𝕜 A]
variable [TopologicalSpace B] [Semiring B] [TopologicalSemiring B] [Star B]
variable [ContinuousStar B] [Algebra 𝕜 B]
variable [TopologicalSpace C] [Semiring C] [TopologicalSemiring C] [Star C]
variable [ContinuousStar C] [Algebra 𝕜 C]
@[simps]
def compStarAlgHom (φ : A →⋆ₐ[𝕜] B) (hφ : Continuous φ) :
    C(X, A) →⋆ₐ[𝕜] C(X, B) where
  toFun f := (⟨φ, hφ⟩ : C(A, B)).comp f
  map_one' := ext fun _ => map_one φ
  map_mul' f g := ext fun x => map_mul φ (f x) (g x)
  map_zero' := ext fun _ => map_zero φ
  map_add' f g := ext fun x => map_add φ (f x) (g x)
  commutes' r := ext fun _x => AlgHomClass.commutes φ r
  map_star' f := ext fun x => map_star φ (f x)
lemma compStarAlgHom_id : compStarAlgHom X (.id 𝕜 A) continuous_id = .id 𝕜 C(X, A) := rfl
lemma compStarAlgHom_comp (φ : A →⋆ₐ[𝕜] B) (ψ : B →⋆ₐ[𝕜] C) (hφ : Continuous φ)
    (hψ : Continuous ψ) : compStarAlgHom X (ψ.comp φ) (hψ.comp hφ) =
      (compStarAlgHom X ψ hψ).comp (compStarAlgHom X φ hφ) :=
  rfl
end Postcomposition
end ContinuousMap
namespace Homeomorph
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (𝕜 : Type*) [CommSemiring 𝕜]
variable (A : Type*) [TopologicalSpace A] [Semiring A] [TopologicalSemiring A] [StarRing A]
variable [ContinuousStar A] [Algebra 𝕜 A]
@[simps]
def compStarAlgEquiv' (f : X ≃ₜ Y) : C(Y, A) ≃⋆ₐ[𝕜] C(X, A) :=
  { (f : C(X, Y)).compStarAlgHom' 𝕜 A with
    toFun := (f : C(X, Y)).compStarAlgHom' 𝕜 A
    invFun := (f.symm : C(Y, X)).compStarAlgHom' 𝕜 A
    left_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        toContinuousMap_comp_symm, ContinuousMap.comp_id]
    right_inv := fun g => by
      simp only [ContinuousMap.compStarAlgHom'_apply, ContinuousMap.comp_assoc,
        symm_comp_toContinuousMap, ContinuousMap.comp_id]
    map_smul' := fun k a => map_smul ((f : C(X, Y)).compStarAlgHom' 𝕜 A) k a }
end Homeomorph
variable {X : Type*} (S R : Type*) [TopologicalSpace X] [CommSemiring S] [CommSemiring R]
variable [Algebra S R] [TopologicalSpace R] [TopologicalSemiring R]
@[simps!]
def ContinuousMap.evalStarAlgHom [StarRing R] [ContinuousStar R] (x : X) :
    C(X, R) →⋆ₐ[S] R :=
  { ContinuousMap.evalAlgHom S R x with
    map_star' := fun _ => rfl }