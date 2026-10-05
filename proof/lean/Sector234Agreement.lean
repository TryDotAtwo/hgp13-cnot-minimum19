import SectorCost234
import SectorCoordinates

namespace HGP13.Sector234Agreement
open Sector234Encoding SectorCoordinates

theorem config_agrees :
    SectorGraph234.config = SharedSearch.ofSector sector
      (fun k x => SectorGraph234.lookup
        (if k ≤ 3 then SectorGraph234.prefix3 else SectorGraph234.prefix4) x) := by
  rfl

theorem passive_targets_agree :
    (passive sector).map (fun j => identity j ^^^ goal sector j) =
      Sector234Potentials.targets := by
  decide +kernel

end HGP13.Sector234Agreement
