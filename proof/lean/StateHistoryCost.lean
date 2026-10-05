import IndexedHistoryBits
import CostSetInvariant

namespace HGP13.StateHistoryCost
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows

/-- All full 13-bit rows, used only as a mathematical decoding domain. -/
def allRows : List Row :=
  (List.range (2^13)).map (BitVec.ofNat 13)

theorem mem_allRows (r : Row) : r ∈ allRows := by
  apply List.mem_map.mpr
  exact ⟨r.toNat, List.mem_range.mpr r.isLt, by simp⟩

/-- Full supported rows selected by a search state's historical bitset. -/
def decode (s : Sector) (history : Nat) : List Row :=
  allRows.filter (fun r =>
    decide (RowSupported (embed s) r) &&
      has history (pack (embed s) r).toNat)

theorem mem_decode_iff (s : Sector) (history : Nat) (r : Row) :
    r ∈ decode s history ↔
      RowSupported (embed s) r ∧
      has history (pack (embed s) r).toNat = true := by
  simp [decode, mem_allRows, decide_eq_true_eq]

/-- For every indexed sector path, full passive cost is a function of the
    terminal state's exact history bits alone. -/
theorem indexed_cost_eq_decoded (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (z : Row) :
    PassiveCost.cost (PassiveInsertion.historyRows (keep s) identity
      (q.map (fullGate (changing s) (fixedWires s)))) z =
    PassiveCost.cost (decode s
      (rawRun (ofSector s lookup) (initial (ofSector s lookup))
        (q.map label)).history) z := by
  apply CostSetInvariant.cost_eq_of_mem_iff
  intro r
  constructor
  · intro hr
    have hret := SectorPackedCost.indexed_gates_retained s hs q
    have hsup := SectorPackedCost.history_rows_supported s identity _
      (CoordinateRestriction.identity_supported (embed s)) hret r hr
    apply (mem_decode_iff s _ r).mpr
    exact ⟨hsup, (IndexedHistoryBits.indexed_history_bit_iff s hs lookup q r hsup).mpr hr⟩
  · intro hr
    obtain ⟨hsup,hbit⟩ := (mem_decode_iff s _ r).mp hr
    exact (IndexedHistoryBits.indexed_history_bit_iff s hs lookup q r hsup).mp hbit

end HGP13.StateHistoryCost
