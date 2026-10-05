import SharedSearch

namespace HGP13.Sector359Encoding
open SectorCover SectorCoordinates PackedRows
set_option maxRecDepth 20000
set_option synthInstance.maxSize 256

def sector : Sector := ⟨true,[2],[]⟩
theorem sector_member : sector ∈ sectors := by
  unfold sectors
  exact List.mem_append_right _
    (family_member true (singles Budget.sources) [[]] [2] [] (by decide) (by decide))

def liftMask (v : BitVec 7) : Row :=
  BitVec.ofNat 13 ((v.toNat &&& 63) ||| ((v.toNat &&& 64) <<< 2))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lift_supported : ∀ v : BitVec 7, RowSupported (embed sector) (liftMask v) := by
  unfold RowSupported
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lift_pack : ∀ v : BitVec 7, pack (embed sector) (liftMask v) = v := by
  change ∀ v : BitVec 7, (pack (embed sector) (liftMask v) : BitVec 7) = v
  decide

theorem unpack_actual (r : Row) (hr : RowSupported (embed sector) r) :
    liftMask (pack (embed sector) r) = r := by
  apply (pack_faithful (embed sector) _ r (lift_supported _) hr).mp
  exact lift_pack _

end HGP13.Sector359Encoding
