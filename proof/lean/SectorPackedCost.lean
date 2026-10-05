import PackedCostRefinement
import FullWordPath

namespace HGP13.SectorPackedCost
open SectorCover SectorCoordinates
open SectorIndexing
open CoreRowEncoding

instance rowSupportedDecidable {n : Nat} (e : Fin n → Wire) (r : Row) :
    Decidable (RowSupported e r) := by
  unfold RowSupported
  infer_instance

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem passive_delta_supported_checked :
    sectors.all (fun s => (passive s).all (fun j =>
      decide (RowSupported (embed s) (identity j ^^^ goal s j)))) = true := by
  decide +kernel

theorem passive_delta_supported (s : Sector) (hs : s ∈ sectors)
    (j : Wire) (hj : j ∈ passive s) :
    RowSupported (embed s) (identity j ^^^ goal s j) := by
  have h := List.all_eq_true.mp passive_delta_supported_checked s hs
  exact of_decide_eq_true (List.all_eq_true.mp h j hj)

theorem actual_core_cost_pack_eq (s : Sector) (hs : s ∈ sectors)
    (p : Program) (hc : Compatible s p) (j : Wire) (hj : j ∈ passive s) :
    PackedCostRefinement.cost
      ((PassiveInsertion.historyRows (keep s) identity (core s p)).map
        (fun r => (PackedRows.pack (embed s) r).toNat))
      (PackedRows.pack (embed s) (identity j ^^^ goal s j)).toNat =
    PassiveCost.cost (PassiveInsertion.historyRows (keep s) identity (core s p))
      (identity j ^^^ goal s j) := by
  exact PackedCostRefinement.cost_pack_eq (embed s) _ _
    (PackedRows.actual_history_supported s p hc)
    (passive_delta_supported s hs j hj)

theorem current_rows_supported (s : Sector) (x : Matrix)
    (hx : CoordinateRestriction.Supported (embed s) x) :
    ∀ r ∈ PassiveInsertion.currentRows (keep s) x,
      RowSupported (embed s) r := by
  intro r hr
  obtain ⟨i,hi,he⟩ :=
    (PassiveInsertion.currentRows_members (keep s) x r).mp hr
  have hm : i ∈ layout s := List.contains_iff_mem.mp hi
  obtain ⟨k,hk⟩ := (embed_image s i).mpr hm
  intro j hj
  have hb := hx k j hj
  simpa only [coefficient,hk,he] using hb

theorem step_supported_of_retained (s : Sector) (x : Matrix) (g : Gate)
    (hx : CoordinateRestriction.Supported (embed s) x)
    (hc : keep s g.1 = true) (ht : keep s g.2 = true) :
    CoordinateRestriction.Supported (embed s) (step x g) := by
  obtain ⟨c,hc'⟩ := (embed_image s g.1).mpr (List.contains_iff_mem.mp hc)
  obtain ⟨t,ht'⟩ := (embed_image s g.2).mpr (List.contains_iff_mem.mp ht)
  have hh := CoordinateRestriction.step_supported (embed s) x (c,t) hx
  simpa only [CoordinateRestriction.liftGate,hc',ht'] using hh

theorem history_rows_supported (s : Sector) (x : Matrix) (p : Program)
    (hx : CoordinateRestriction.Supported (embed s) x)
    (hg : ∀ g ∈ p, keep s g.1 = true ∧ keep s g.2 = true) :
    ∀ r ∈ PassiveInsertion.historyRows (keep s) x p,
      RowSupported (embed s) r := by
  induction p generalizing x with
  | nil =>
    exact current_rows_supported s x hx
  | cons g p ih =>
    intro r hr
    simp only [PassiveInsertion.historyRows,List.mem_append] at hr
    rcases hr with hr | hr
    · exact current_rows_supported s x hx r hr
    · have hhead := hg g List.mem_cons_self
      have htail : ∀ h ∈ p, keep s h.1 = true ∧ keep s h.2 = true := by
          intro h hh
          exact hg h (List.mem_cons_of_mem _ hh)
      exact ih (step x g) (step_supported_of_retained s x g hx hhead.1 hhead.2)
        htail r hr

theorem indexed_gates_retained (s : Sector) (hs : s ∈ sectors)
    (q : List (IndexedGate (changing s) (fixedWires s))) :
    ∀ g ∈ q.map (fullGate (changing s) (fixedWires s)),
      keep s g.1 = true ∧ keep s g.2 = true := by
  intro g hg
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hg
  constructor
  · exact KnownControls.input_retained s hs _
      (List.getElem_mem (by simpa using a.1.isLt))
  · exact changing_retained s hs _ (List.getElem_mem a.2.isLt)

theorem indexed_history_cost_pack_eq (s : Sector) (hs : s ∈ sectors)
    (q : List (IndexedGate (changing s) (fixedWires s)))
    (j : Wire) (hj : j ∈ passive s) :
    PackedCostRefinement.cost
      ((PassiveInsertion.historyRows (keep s) identity
        (q.map (fullGate (changing s) (fixedWires s)))).map
        (fun r => (PackedRows.pack (embed s) r).toNat))
      (PackedRows.pack (embed s) (identity j ^^^ goal s j)).toNat =
    PassiveCost.cost (PassiveInsertion.historyRows (keep s) identity
      (q.map (fullGate (changing s) (fixedWires s))))
      (identity j ^^^ goal s j) := by
  exact PackedCostRefinement.cost_pack_eq (embed s) _ _
    (history_rows_supported s identity _
      (CoordinateRestriction.identity_supported (embed s))
      (indexed_gates_retained s hs q))
    (passive_delta_supported s hs j hj)

end HGP13.SectorPackedCost
