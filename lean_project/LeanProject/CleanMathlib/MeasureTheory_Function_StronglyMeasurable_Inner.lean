import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
variable {α : Type*}
namespace MeasureTheory
namespace StronglyMeasurable
protected theorem inner {𝕜 : Type*} {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {_ : MeasurableSpace α} {f g : α → E} (hf : StronglyMeasurable f)
    (hg : StronglyMeasurable g) : StronglyMeasurable fun t => @inner 𝕜 _ _ (f t) (g t) :=
  Continuous.comp_stronglyMeasurable continuous_inner (hf.prod_mk hg)
end StronglyMeasurable
namespace AEStronglyMeasurable
variable {m : MeasurableSpace α} {μ : Measure α} {𝕜 : Type*} {E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y
protected theorem re {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => RCLike.re (f x)) μ :=
  RCLike.continuous_re.comp_aestronglyMeasurable hf
protected theorem im {f : α → 𝕜} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => RCLike.im (f x)) μ :=
  RCLike.continuous_im.comp_aestronglyMeasurable hf
protected theorem inner {_ : MeasurableSpace α} {μ : Measure α} {f g : α → E}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => ⟪f x, g x⟫) μ :=
  continuous_inner.comp_aestronglyMeasurable (hf.prod_mk hg)
end AEStronglyMeasurable
end MeasureTheory