import SectorPackedCost

namespace HGP13.IndexedHistoryBits
open SectorCover SectorCoordinates SectorIndexing CoreRowEncoding
open SharedSearch TransitionChecks PackedRows ProjectedHistory

theorem indexed_history_bit_iff (s : Sector) (hs : s ∈ sectors)
    (lookup : Nat → Nat → Bool)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (r : Row) (hr : RowSupported (embed s) r) :
    has (rawRun (ofSector s lookup) (initial (ofSector s lookup))
      (q.map label)).history (pack (embed s) r).toNat = true ↔
    r ∈ PassiveInsertion.historyRows (keep s) identity
      (q.map (fullGate (changing s) (fixedWires s))) := by
  let c := ofSector s lookup
  let p := q.map (fullGate (changing s) (fixedWires s))
  obtain ⟨hd,_,hj⟩ := partition_properties s hs
  obtain ⟨hrows,hh,hfixed,_⟩ := initial_matches_full_matrix s hs lookup
  have rh := raw_history_run (embed s) (changing s) (fixedWires s)
    hd hj c (count_matches s lookup) q identity (initial c) hrows hfixed
  change has (rawRun c (initial c) (q.map label)).history
    (pack (embed s) r).toNat = true ↔ _
  rw [rh, hh]
  change has (traceHistory (embed s) identity p
    (encodeHistory ((PassiveInsertion.currentRows (keep s) identity).map
      (fun a => (pack (embed s) a).toNat)))) (pack (embed s) r).toNat = true ↔ _
  have hret := SectorPackedCost.indexed_gates_retained s hs q
  have ht : ∀ g ∈ p, keep s g.2 = true := by
    intro g hg
    exact (hret g hg).2
  have hm := produced_history (keep s) p identity ht
  have hsupp := SectorPackedCost.history_rows_supported s identity p
    (CoordinateRestriction.identity_supported (embed s)) hret
  have supported : ∀ a ∈ PassiveInsertion.currentRows (keep s) identity ++
      produced identity p, RowSupported (embed s) a := by
    intro a ha
    exact hsupp a ((hm a).mp ha)
  rw [traceHistory_encode, ← List.map_append,
    packed_history_bits (embed s) _ r supported hr, hm r]

end HGP13.IndexedHistoryBits
