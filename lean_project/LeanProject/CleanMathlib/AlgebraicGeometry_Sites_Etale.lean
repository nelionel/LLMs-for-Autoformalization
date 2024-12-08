import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.BigZariski
universe v u
open CategoryTheory MorphismProperty Limits
namespace AlgebraicGeometry.Scheme
def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @IsEtale
abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  etalePretopology.toGrothendieck
lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_le_grothendieckTopology
  intro X Y f hf
  infer_instance
end AlgebraicGeometry.Scheme