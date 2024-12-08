import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Multilinear.Basic
universe uι uκ uS uR uM uN
variable {ι : Type uι} {κ : ι → Type uκ}
variable {S : Type uS} {R : Type uR}
namespace MultilinearMap
section Semiring
variable {M : ∀ i, κ i → Type uM} {N : Type uN}
variable [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [AddCommMonoid N]
variable [∀ i k, Module R (M i k)] [Module R N]
@[ext]
theorem pi_ext [Finite ι] [∀ i, Finite (κ i)] [∀ i, DecidableEq (κ i)]
    ⦃f g : MultilinearMap R (fun i ↦ Π j : κ i, M i j) N⦄
    (h : ∀ p : Π i, κ i,
      f.compLinearMap (fun i => LinearMap.single R _ (p i)) =
      g.compLinearMap (fun i => LinearMap.single R _ (p i))) : f = g := by
  ext x
  show f (fun i ↦ x i) = g (fun i ↦ x i)
  obtain ⟨i⟩ := nonempty_fintype ι
  have (i) := (nonempty_fintype (κ i)).some
  have := Classical.decEq ι
  rw [funext (fun i ↦ Eq.symm (Finset.univ_sum_single (x i)))]
  simp_rw [MultilinearMap.map_sum_finset]
  congr! 1 with p
  simp_rw [MultilinearMap.ext_iff] at h
  exact h _ _
end Semiring
section piFamily
variable {M : ∀ i, κ i → Type uM} {N : (Π i, κ i) → Type uN}
section Semiring
variable [Semiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]
@[simps]
def piFamily (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun x := fun p => f p (fun i => x i (p i))
  map_update_add' {dec} m i x y := funext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.add_apply, (f p).map_update_add]
  map_update_smul' {dec} m i c x := funext fun p => by
    cases Subsingleton.elim dec (by infer_instance)
    dsimp
    simp_rw [Function.apply_update (fun i m => m (p i)) m, Pi.smul_apply, (f p).map_update_smul]
@[simp]
theorem piFamily_single [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
    (p : ∀ i, κ i) (m : ∀ i, M i (p i)) :
    piFamily f (fun i => Pi.single (p i) (m i)) = Pi.single p (f p m) := by
  ext q
  obtain rfl | hpq := eq_or_ne p q
  · simp
  · rw [Pi.single_eq_of_ne' hpq]
    rw [Function.ne_iff] at hpq
    obtain ⟨i, hpqi⟩ := hpq
    apply (f q).map_coord_zero i
    simp_rw [Pi.single_eq_of_ne' hpqi]
@[simp]
theorem piFamily_single_left_apply [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) (x : Π i j, M i j) :
    piFamily (Pi.single p f) x = Pi.single p (f fun i => x i (p i)) := by
  ext p'
  obtain rfl | hp := eq_or_ne p p'
  · simp
  · simp [hp]
theorem piFamily_single_left [Fintype ι] [∀ i, DecidableEq (κ i)]
    (p : Π i, κ i) (f : MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (Pi.single p f) =
      (LinearMap.single R _ p).compMultilinearMap (f.compLinearMap fun i => .proj (p i)) :=
  ext <| piFamily_single_left_apply _ _
@[simp]
theorem piFamily_compLinearMap_lsingle [Fintype ι] [∀ i, DecidableEq (κ i)]
    (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) (p : ∀ i, κ i) :
    (piFamily f).compLinearMap (fun i => LinearMap.single _ _ (p i))
      = (LinearMap.single _ _ p).compMultilinearMap (f p) :=
  MultilinearMap.ext <| piFamily_single f p
@[simp]
theorem piFamily_zero :
    piFamily (0 : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) = 0 := by
  ext; simp
@[simp]
theorem piFamily_add (f g : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (f + g) = piFamily f + piFamily g := by
  ext; simp
@[simp]
theorem piFamily_smul
    [Monoid S] [∀ p, DistribMulAction S (N p)] [∀ p, SMulCommClass R S (N p)]
    (s : S) (f : Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p)) :
    piFamily (s • f) = s • piFamily f := by
  ext; simp
end Semiring
section CommSemiring
variable [CommSemiring R]
variable [∀ i k, AddCommMonoid (M i k)] [∀ p, AddCommMonoid (N p)]
variable [∀ i k, Module R (M i k)] [∀ p, Module R (N p)]
@[simps]
def piFamilyₗ :
    (Π (p : Π i, κ i), MultilinearMap R (fun i ↦ M i (p i)) (N p))
      →ₗ[R] MultilinearMap R (fun i => Π j : κ i, M i j) (Π t : Π i, κ i, N t) where
  toFun := piFamily
  map_add' := piFamily_add
  map_smul' := piFamily_smul
end CommSemiring
end piFamily
end MultilinearMap