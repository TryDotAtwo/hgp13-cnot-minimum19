import PrefixPackedFourth
import SectorGraph359
namespace HGP13.PackedFourthFinalNode
open HGP13.PrefixPackedFourth HGP13.Catalogues
set_option maxRecDepth 20000
set_option maxHeartbeats 100000000
def mask : BitVec 128 := BitVec.ofNat 128 46705972664197194632545054416432848896
theorem final_hit : finalNodeOK TransposeFree.goals (SectorGraph359.lookup SectorGraph359.prefix4) [(3 : Value),(5 : Value),(12 : Value)] mask = true := by decide +kernel
theorem deleted_zero_rejected : finalNodeOK TransposeFree.goals (fun k => (k != 0) && SectorGraph359.lookup SectorGraph359.prefix4 k) [(3 : Value),(5 : Value),(12 : Value)] mask = false := by decide +kernel
end HGP13.PackedFourthFinalNode
