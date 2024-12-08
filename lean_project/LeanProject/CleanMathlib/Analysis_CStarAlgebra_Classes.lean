import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Star.NonUnitalSubalgebra
class NonUnitalCStarAlgebra (A : Type*) extends NonUnitalNormedRing A, StarRing A, CompleteSpace A,
    CStarRing A, NormedSpace ℂ A, IsScalarTower ℂ A A, SMulCommClass ℂ A A, StarModule ℂ A where
class NonUnitalCommCStarAlgebra (A : Type*) extends
    NonUnitalNormedCommRing A, NonUnitalCStarAlgebra A
class CStarAlgebra (A : Type*) extends NormedRing A, StarRing A, CompleteSpace A, CStarRing A,
    NormedAlgebra ℂ A, StarModule ℂ A where
class CommCStarAlgebra (A : Type*) extends NormedCommRing A, CStarAlgebra A
instance (priority := 100) CStarAlgebra.toNonUnitalCStarAlgebra (A : Type*) [CStarAlgebra A] :
    NonUnitalCStarAlgebra A where
instance (priority := 100) CommCStarAlgebra.toNonUnitalCommCStarAlgebra (A : Type*)
    [CommCStarAlgebra A] : NonUnitalCommCStarAlgebra A where
noncomputable instance StarSubalgebra.cstarAlgebra {S A : Type*} [CStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
noncomputable instance StarSubalgebra.commCStarAlgebra {S A : Type*} [CommCStarAlgebra A]
    [SetLike S A] [SubringClass S A] [SMulMemClass S ℂ A] [StarMemClass S A]
    (s : S) [h_closed : IsClosed (s : Set A)] : CommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _
noncomputable instance NonUnitalStarSubalgebra.nonUnitalCStarAlgebra {S A : Type*}
    [NonUnitalCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
noncomputable instance NonUnitalStarSubalgebra.nonUnitalCommCStarAlgebra {S A : Type*}
    [NonUnitalCommCStarAlgebra A] [SetLike S A] [NonUnitalSubringClass S A] [SMulMemClass S ℂ A]
    [StarMemClass S A] (s : S) [h_closed : IsClosed (s : Set A)] : NonUnitalCommCStarAlgebra s where
  toCompleteSpace := h_closed.completeSpace_coe
  norm_mul_self_le x := CStarRing.norm_star_mul_self (x := (x : A)) |>.symm.le
  mul_comm _ _ := Subtype.ext <| mul_comm _ _
noncomputable instance : CommCStarAlgebra ℂ where
  mul_comm := mul_comm
section Pi
variable {ι : Type*} {A : ι → Type*} [Fintype ι]
instance [(i : ι) → NonUnitalCStarAlgebra (A i)] : NonUnitalCStarAlgebra (Π i, A i) where
instance [(i : ι) → NonUnitalCommCStarAlgebra (A i)] : NonUnitalCommCStarAlgebra (Π i, A i) where
  mul_comm := mul_comm
noncomputable instance [(i : ι) → CStarAlgebra (A i)] : CStarAlgebra (Π i, A i) where
noncomputable instance [(i : ι) → CommCStarAlgebra (A i)] : CommCStarAlgebra (Π i, A i) where
  mul_comm := mul_comm
end Pi
section Prod
variable {A B : Type*}
instance [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] : NonUnitalCStarAlgebra (A × B) where
instance [NonUnitalCommCStarAlgebra A] [NonUnitalCommCStarAlgebra B] :
    NonUnitalCommCStarAlgebra (A × B) where
  mul_comm := mul_comm
noncomputable instance [CStarAlgebra A] [CStarAlgebra B] : CStarAlgebra (A × B) where
noncomputable instance [CommCStarAlgebra A] [CommCStarAlgebra B] : CommCStarAlgebra (A × B) where
  mul_comm := mul_comm
end Prod