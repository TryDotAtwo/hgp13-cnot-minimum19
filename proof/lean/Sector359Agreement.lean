import SectorCost359
import Sector359Encoding

namespace HGP13.Sector359Agreement

def lookup359 (k x : Nat) : Bool :=
  SectorGraph359.lookup
    (if k ≤ 3 then SectorGraph359.prefix3 else SectorGraph359.prefix4) x

theorem config_agrees :
    SectorGraph359.config =
      SharedSearch.ofSector Sector359Encoding.sector lookup359 := by
  rfl

theorem passive_targets_agree :
    (SectorCoordinates.passive Sector359Encoding.sector).map
      (fun j => identity j ^^^ SectorCoordinates.goal Sector359Encoding.sector j) =
      SectorTerminal359.targets := by
  decide +kernel

end HGP13.Sector359Agreement
