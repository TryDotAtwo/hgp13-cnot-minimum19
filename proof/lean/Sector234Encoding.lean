import FullPackedPotential
import SectorCoordinates

namespace HGP13.Sector234Encoding
open SectorCover SectorCoordinates PackedRows

def sector : Sector := ⟨true,[0,2],[10]⟩

theorem sector_at_234 : SectorCover.sectors[234]? = some sector := by decide +kernel

def liftMask (v : BitVec 8) : Row :=
  BitVec.ofNat 13 ((v.toNat &&& 63) |||
    ((v.toNat &&& 64) <<< 2) ||| ((v.toNat &&& 128) <<< 3))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lift_supported : ∀ v : BitVec 8,
    RowSupported (embed sector) (liftMask v) := by
  unfold RowSupported
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lift_pack : ∀ v : BitVec 8,
    pack (embed sector) (liftMask v) = v := by
  change ∀ v : BitVec 8, (pack (embed sector) (liftMask v) : BitVec 8) = v
  decide +kernel

theorem unpack_actual (r : Row)
    (hr : RowSupported (embed sector) r) :
    liftMask (pack (embed sector) r) = r := by
  apply (pack_faithful (embed sector) _ r (lift_supported _) hr).mp
  exact lift_pack _

theorem high_form_249_keeps_carrier_bit :
    liftMask (249 : BitVec 8) ≠ liftMask (121 : BitVec 8) := by decide +kernel

end HGP13.Sector234Encoding
