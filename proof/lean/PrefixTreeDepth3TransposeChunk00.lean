import PrefixTreeDepth3TransposeBase
namespace HGP13.PrefixTreeDepth3Transpose
open HGP13.PrefixTreeCertificate HGP13.Catalogues
set_option maxRecDepth 20000
set_option maxHeartbeats 100000000
theorem parent0 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(5 : Value)] layer3 = true := by decide +kernel
theorem parent1 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(6 : Value)] layer3 = true := by decide +kernel
theorem parent2 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(7 : Value)] layer3 = true := by decide +kernel
theorem parent3 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(9 : Value)] layer3 = true := by decide +kernel
theorem parent4 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(10 : Value)] layer3 = true := by decide +kernel
theorem parent5 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(11 : Value)] layer3 = true := by decide +kernel
theorem parent6 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(12 : Value)] layer3 = true := by decide +kernel
theorem parent7 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(18 : Value)] layer3 = true := by decide +kernel
theorem parent8 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(19 : Value)] layer3 = true := by decide +kernel
theorem parent9 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(20 : Value)] layer3 = true := by decide +kernel
theorem parent10 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(22 : Value)] layer3 = true := by decide +kernel
theorem parent11 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(23 : Value)] layer3 = true := by decide +kernel
theorem parent12 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(24 : Value)] layer3 = true := by decide +kernel
theorem parent13 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(25 : Value)] layer3 = true := by decide +kernel
theorem parent14 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(29 : Value)] layer3 = true := by decide +kernel
theorem parent15 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(33 : Value)] layer3 = true := by decide +kernel
theorem parent16 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(34 : Value)] layer3 = true := by decide +kernel
theorem parent17 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(35 : Value)] layer3 = true := by decide +kernel
theorem parent18 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(36 : Value)] layer3 = true := by decide +kernel
theorem parent19 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(40 : Value)] layer3 = true := by decide +kernel
theorem parent20 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(43 : Value)] layer3 = true := by decide +kernel
theorem parent21 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(48 : Value)] layer3 = true := by decide +kernel
theorem parent22 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(49 : Value)] layer3 = true := by decide +kernel
theorem parent23 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(53 : Value)] layer3 = true := by decide +kernel
theorem parent24 : nodeStepOK FreeXor.maskBasis TransposeFree.goals [(3 : Value),(65 : Value)] layer3 = true := by decide +kernel
def group00 : List (List Value) := [[(3 : Value),(5 : Value)],[(3 : Value),(6 : Value)],[(3 : Value),(7 : Value)],[(3 : Value),(9 : Value)],[(3 : Value),(10 : Value)],[(3 : Value),(11 : Value)],[(3 : Value),(12 : Value)],[(3 : Value),(18 : Value)],[(3 : Value),(19 : Value)],[(3 : Value),(20 : Value)],[(3 : Value),(22 : Value)],[(3 : Value),(23 : Value)],[(3 : Value),(24 : Value)],[(3 : Value),(25 : Value)],[(3 : Value),(29 : Value)],[(3 : Value),(33 : Value)],[(3 : Value),(34 : Value)],[(3 : Value),(35 : Value)],[(3 : Value),(36 : Value)],[(3 : Value),(40 : Value)],[(3 : Value),(43 : Value)],[(3 : Value),(48 : Value)],[(3 : Value),(49 : Value)],[(3 : Value),(53 : Value)],[(3 : Value),(65 : Value)]]
theorem group00_all : (group00.all fun xs => nodeStepOK FreeXor.maskBasis TransposeFree.goals xs layer3) = true := by
  simp only [group00, List.all_cons, List.all_nil, Bool.and_true, parent0, parent1, parent2, parent3, parent4, parent5, parent6, parent7, parent8, parent9, parent10, parent11, parent12, parent13, parent14, parent15, parent16, parent17, parent18, parent19, parent20, parent21, parent22, parent23, parent24]
end HGP13.PrefixTreeDepth3Transpose
