import Mathlib.AlgebraicTopology.SimplicialSet.Basic
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic
open CategoryTheory
noncomputable def TopCat.toSSet : TopCat ⥤ SSet :=
  Presheaf.restrictedYoneda SimplexCategory.toTop
noncomputable def SSet.toTop : SSet ⥤ TopCat :=
  yoneda.leftKanExtension SimplexCategory.toTop
noncomputable def sSetTopAdj : SSet.toTop ⊣ TopCat.toSSet :=
  Presheaf.yonedaAdjunction (yoneda.leftKanExtension SimplexCategory.toTop)
    (yoneda.leftKanExtensionUnit SimplexCategory.toTop)
noncomputable def SSet.toTopSimplex :
    (yoneda : SimplexCategory ⥤ _) ⋙ SSet.toTop ≅ SimplexCategory.toTop :=
  Presheaf.isExtensionAlongYoneda _