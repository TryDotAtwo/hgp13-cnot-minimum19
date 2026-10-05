import FullPackedPotential
import SectorCoordinates
namespace HGP13.SectorScalePotential0
set_option maxRecDepth 20000
set_option maxHeartbeats 100000000
def sector : SectorCover.Sector := ⟨false,[0, 1],[6, 7]⟩
def history : List Row := [1, 2, 4, 8, 9, 16, 18, 32, 256, 260, 292, 64, 320, 329, 128, 146, 402]
def targets : List Row := [3, 6, 27, 54]
def table : Nat := 179769313486231590772921002134383953318292550178683170166994489540580348914023731040008488130947712501856723522939538370934244344624732679281677425363839348508720284476669725501858558735671207271887421957105016534906552033647061633698572725779285223832174720723855166563626276755175822995671623396419686492564
theorem checked : FullPackedPotential.check (SectorCoordinates.embed sector) history table = true := by decide
theorem bound : 18 < 10 +
  (targets.map (fun r => FullPackedPotential.tableWeight table
    (PackedRows.pack (SectorCoordinates.embed sector) r))).sum := by decide
end HGP13.SectorScalePotential0
