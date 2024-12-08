import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.ConcreteCategory.BundledHom
open CategoryTheory
universe u v
def ωCPO : Type (u + 1) :=
  Bundled OmegaCompletePartialOrder
namespace ωCPO
open OmegaCompletePartialOrder
instance : BundledHom @ContinuousHom where
  toFun := @ContinuousHom.Simps.apply
  id := @ContinuousHom.id
  comp := @ContinuousHom.comp
  hom_ext := @ContinuousHom.coe_inj
deriving instance LargeCategory for ωCPO
instance : ConcreteCategory ωCPO := by unfold ωCPO; infer_instance
instance : CoeSort ωCPO Type* :=
  Bundled.coeSort
def of (α : Type*) [OmegaCompletePartialOrder α] : ωCPO :=
  Bundled.of α
@[simp]
theorem coe_of (α : Type*) [OmegaCompletePartialOrder α] : ↥(of α) = α :=
  rfl
instance : Inhabited ωCPO :=
  ⟨of PUnit⟩
instance (α : ωCPO) : OmegaCompletePartialOrder α :=
  α.str
section
open CategoryTheory.Limits
namespace HasProducts
def product {J : Type v} (f : J → ωCPO.{v}) : Fan f :=
  Fan.mk (of (∀ j, f j)) fun j => .mk (Pi.evalOrderHom j) fun _ => rfl
def isProduct (J : Type v) (f : J → ωCPO) : IsLimit (product f) where
  lift s :=
    ⟨⟨fun t j => (s.π.app ⟨j⟩).toFun t, fun _ _ h j => (s.π.app ⟨j⟩).monotone h⟩,
      fun x => funext fun j => (s.π.app ⟨j⟩).continuous x⟩
  uniq s m w := by
    ext t; funext j 
    change m.toFun t j = (s.π.app ⟨j⟩).toFun t
    rw [← w ⟨j⟩]
    rfl
  fac _ _ := rfl
instance (J : Type v) (f : J → ωCPO.{v}) : HasProduct f :=
  HasLimit.mk ⟨_, isProduct _ f⟩
end HasProducts
instance omegaCompletePartialOrderEqualizer {α β : Type*} [OmegaCompletePartialOrder α]
    [OmegaCompletePartialOrder β] (f g : α →𝒄 β) :
    OmegaCompletePartialOrder { a : α // f a = g a } :=
  OmegaCompletePartialOrder.subtype _ fun c hc => by
    rw [f.continuous, g.continuous]
    congr 1
    apply OrderHom.ext; funext x 
    apply hc _ ⟨_, rfl⟩
namespace HasEqualizers
def equalizerι {α β : Type*} [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
    (f g : α →𝒄 β) : { a : α // f a = g a } →𝒄 α :=
  .mk (OrderHom.Subtype.val _) fun _ => rfl
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : Fork f g :=
  Fork.ofι (P := ωCPO.of { a // f.toFun a = g.toFun a }) (equalizerι f g)
    (ContinuousHom.ext _ _ fun x => x.2)
def isEqualizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : IsLimit (equalizer f g) :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨{  toFun := fun x => ⟨s.ι.toFun x, by apply ContinuousHom.congr_fun s.condition⟩
        monotone' := fun _ _ h => s.ι.monotone h
        map_ωSup' := fun x => Subtype.ext (s.ι.continuous x)
      }, by ext; rfl, fun hm => by
      apply ContinuousHom.ext _ _ fun x => Subtype.ext ?_ 
      apply ContinuousHom.congr_fun hm⟩
end HasEqualizers
instance : HasProducts.{v} ωCPO.{v} :=
  fun _ => { has_limit := fun _ => hasLimitOfIso Discrete.natIsoFunctor.symm }
instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : HasLimit (parallelPair f g) :=
  HasLimit.mk ⟨_, HasEqualizers.isEqualizer f g⟩
instance : HasEqualizers ωCPO.{v} :=
  hasEqualizers_of_hasLimit_parallelPair _
instance : HasLimits ωCPO.{v} :=
  has_limits_of_hasEqualizers_and_products
end
end ωCPO