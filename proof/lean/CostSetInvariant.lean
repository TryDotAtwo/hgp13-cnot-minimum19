import PackedCostRefinement

namespace HGP13.CostSetInvariant
open PassiveCost

theorem atMost_mono_mem (d e : List Row) (z : Row) (k : Nat)
    (hmem : d ⊆ e) : AtMost (cost d z) k → AtMost (cost e z) k := by
  intro h
  obtain ⟨b,hb,hx,hk⟩ := (cost_atMost_iff d z k).mp h
  have hm : b ⊆ e := by
    intro x hxb
    exact hmem (hb.subset hxb)
  have he := cost_le_arbitrary e b hm
  rw [hx] at he
  obtain ⟨n,hn,hle⟩ := he
  exact ⟨n,hn,Nat.le_trans hle hk⟩

theorem cost_eq_of_mem_iff (d e : List Row) (z : Row)
    (hmem : ∀ v, v ∈ d ↔ v ∈ e) : cost d z = cost e z := by
  have both (k : Nat) : AtMost (cost d z) k ↔ AtMost (cost e z) k := by
    constructor
    · exact atMost_mono_mem d e z k (fun v hv => (hmem v).mp hv)
    · exact atMost_mono_mem e d z k (fun v hv => (hmem v).mpr hv)
  cases hd : cost d z with
  | none =>
    cases he : cost e z with
    | none => rfl
    | some m =>
      have hh := (both m).mpr ⟨m, he, Nat.le_refl m⟩
      simp [AtMost, hd] at hh
  | some n =>
    cases he : cost e z with
    | none =>
      have hh := (both n).mp ⟨n, hd, Nat.le_refl n⟩
      simp [AtMost, he] at hh
    | some m =>
      have hnm := (both n).mp ⟨n, hd, Nat.le_refl n⟩
      have hmn := (both m).mpr ⟨m, he, Nat.le_refl m⟩
      simp only [AtMost, he, Option.some.injEq] at hnm
      simp only [AtMost, hd, Option.some.injEq] at hmn
      have hmle : m ≤ n := by obtain ⟨_, rfl, h⟩ := hnm; exact h
      have hnle : n ≤ m := by obtain ⟨_, rfl, h⟩ := hmn; exact h
      have : n = m := Nat.le_antisymm hnle hmle
      simp [this]

theorem packed_cost_eraseDups {n : Nat} (e : Fin n → Wire)
    (d : List Row) (z : Row)
    (hd : ∀ v ∈ d, SectorCoordinates.RowSupported e v)
    (hz : SectorCoordinates.RowSupported e z) :
    PackedCostRefinement.cost
      (d.map (fun v => (PackedRows.pack e v).toNat))
      (PackedRows.pack e z).toNat =
    PackedCostRefinement.cost
      (d.eraseDups.map (fun v => (PackedRows.pack e v).toNat))
      (PackedRows.pack e z).toNat := by
  rw [PackedCostRefinement.cost_pack_eq e d z hd hz,
    PackedCostRefinement.cost_pack_eq e d.eraseDups z
      (by intro v hv; exact hd v (List.mem_eraseDups.mp hv)) hz]
  exact cost_eq_of_mem_iff d d.eraseDups z (fun v => List.mem_eraseDups.symm)

end HGP13.CostSetInvariant
