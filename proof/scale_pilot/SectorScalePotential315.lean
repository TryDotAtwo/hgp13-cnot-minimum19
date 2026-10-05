import FullPackedPotential
import SectorCoordinates
namespace HGP13.SectorScalePotential315
set_option maxRecDepth 20000
set_option maxHeartbeats 100000000
def sector : SectorCover.Sector := ⟨false,[0],[6]⟩
def history : List Row := [1, 2, 4, 8, 9, 16, 32, 256, 260, 292, 64, 320, 329]
def targets : List Row := [274, 3, 6, 27, 54]
def table : Nat := 13407807929942406376365886743774990094244776243035276731123522862018431470424434232102443891375908165583939721050639378746109665864456502979509777259162004
theorem checked : FullPackedPotential.check (SectorCoordinates.embed sector) history table = true := by decide
theorem bound : 18 < 6 +
  (targets.map (fun r => FullPackedPotential.tableWeight table
    (PackedRows.pack (SectorCoordinates.embed sector) r))).sum := by decide
end HGP13.SectorScalePotential315
