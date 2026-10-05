import PackedRows
import PassiveCost

namespace HGP13.PackedCostRefinement

/-- The same 0/1 recurrence used for passive costs, on packed Nat masks. -/
def cost : List Nat → Nat → Option Nat
  | [], z => if z = 0 then some 0 else none
  | v :: d, z => PassiveCost.best (cost d z) ((cost d (z ^^^ v)).map Nat.succ)

theorem supported_xor {n : Nat} (e : Fin n → Wire) (a b : Row)
    (ha : SectorCoordinates.RowSupported e a)
    (hb : SectorCoordinates.RowSupported e b) :
    SectorCoordinates.RowSupported e (a ^^^ b) := by
  intro j hj
  simp only [BitVec.getLsbD_xor]
  rw [ha j hj, hb j hj]
  rfl

theorem pack_nat_zero_iff {n : Nat} (e : Fin n → Wire) (a : Row)
    (ha : SectorCoordinates.RowSupported e a) :
    (PackedRows.pack e a).toNat = 0 ↔ a = 0 := by
  have hh := PackedRows.pack_zero_iff e a ha
  have hn : (PackedRows.pack e a).toNat = (0#n).toNat ↔
      PackedRows.pack e a = 0 := BitVec.toNat_inj
  simpa only [BitVec.toNat_zero] using hn.trans hh

/-- Exact cost preservation for every supported historical list and target.
    This is a mathematical refinement of the packed recurrence, not a proof
    about the imperative C++ array update. -/
theorem cost_pack_eq {n : Nat} (e : Fin n → Wire) (d : List Row) (z : Row)
    (hd : ∀ v ∈ d, SectorCoordinates.RowSupported e v)
    (hz : SectorCoordinates.RowSupported e z) :
    cost (d.map (fun v => (PackedRows.pack e v).toNat))
      (PackedRows.pack e z).toNat = PassiveCost.cost d z := by
  revert hd hz
  induction d generalizing z with
  | nil =>
    intro hd hz
    simp only [List.map_nil, cost, PassiveCost.cost]
    simp only [pack_nat_zero_iff e z hz]
  | cons v d ih =>
    intro hd hz
    have hv : SectorCoordinates.RowSupported e v := hd v List.mem_cons_self
    have hd' : ∀ w ∈ d, SectorCoordinates.RowSupported e w := by
      intro w hw
      exact hd w (List.mem_cons_of_mem _ hw)
    have hx := supported_xor e z v hz hv
    simp only [List.map_cons, cost, PassiveCost.cost]
    rw [ih z hd' hz]
    rw [← PackedRows.pack_nat_xor e z v]
    rw [ih (z ^^^ v) hd' hx]

end HGP13.PackedCostRefinement
