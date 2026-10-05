import FullWordPath

namespace HGP13.IdealPrefixLookup

open HGP13

/-- Mathematical reference set of exactly the keys required by a catalogue
    prefix lookup at capacity three or four. This is a specification, not a
    finite executable implementation. -/
noncomputable def ideal (s : SectorCover.Sector) (capacity key : Nat) : Bool := by
  classical
  exact decide (∃ extra : List Catalogues.Value,
    Catalogues.Catalogued (ProjectedHistory.projectedGoals s) extra.length extra ∧
    3 ≤ extra.length ∧ extra.length ≤ capacity ∧
    ∃ observed : List Nat,
      observed.Nodup ∧ observed ⊆ extra.map BitVec.toNat ∧
      SharedSearch.encode observed = key)

theorem ideal_accepts (s : SectorCover.Sector)
    (extra : List Catalogues.Value) (observed : List Nat) (capacity : Nat)
    (hc : Catalogues.Catalogued (ProjectedHistory.projectedGoals s)
      extra.length extra) (hmin : 3 ≤ extra.length)
    (hmax : extra.length ≤ capacity) (hn : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat) :
    ideal s capacity (SharedSearch.encode observed) = true := by
  classical
  simp only [ideal, decide_eq_true_eq]
  exact ⟨extra, hc, hmin, hmax, observed, hn, hs, rfl⟩

theorem ideal_prefix_complete (s : SectorCover.Sector) :
    FullWordPath.PrefixComplete s (ideal s) := by
  intro extra observed capacity hc hmin hmax hcaplo hcaphi hn hs
  have heq : (if capacity ≤ 3 then 3 else 4) = capacity := by
    by_cases h : capacity ≤ 3 <;> simp [h] <;> omega
  rw [heq]
  exact ideal_accepts s extra observed capacity hc hmin hmax hn hs

/-- A concrete Boolean table is complete if it includes every key in the
    mathematical reference set. The reverse inclusion is not required for
    sound exclusion: false positives only make the search larger. -/
theorem prefix_complete_of_covers_ideal (s : SectorCover.Sector)
    (lookup : Nat → Nat → Bool)
    (cover : ∀ capacity key, 3 ≤ capacity → capacity ≤ 4 →
      ideal s capacity key = true → lookup capacity key = true) :
    FullWordPath.PrefixComplete s lookup := by
  intro extra observed capacity hc hmin hmax hcaplo hcaphi hn hs
  have heq : (if capacity ≤ 3 then 3 else 4) = capacity := by
    by_cases h : capacity ≤ 3 <;> simp [h] <;> omega
  rw [heq]
  exact cover capacity (SharedSearch.encode observed) hcaplo hcaphi
    (ideal_accepts s extra observed capacity hc hmin hmax hn hs)

theorem covers_ideal_of_prefix_complete (s : SectorCover.Sector)
    (lookup : Nat → Nat → Bool)
    (hpc : FullWordPath.PrefixComplete s lookup)
    (capacity key : Nat) (hlo : 3 ≤ capacity) (hhi : capacity ≤ 4)
    (hideal : ideal s capacity key = true) :
    lookup capacity key = true := by
  classical
  simp only [ideal, decide_eq_true_eq] at hideal
  obtain ⟨extra, hc, hmin, hmax, observed, hn, hs, heq⟩ := hideal
  have hlookup := hpc extra observed capacity hc hmin hmax hlo hhi hn hs
  have hcap : (if capacity ≤ 3 then 3 else 4) = capacity := by
    by_cases h : capacity ≤ 3 <;> simp [h] <;> omega
  simpa only [hcap, heq] using hlookup

theorem prefix_complete_iff_covers_ideal (s : SectorCover.Sector)
    (lookup : Nat → Nat → Bool) :
    FullWordPath.PrefixComplete s lookup ↔
      ∀ capacity key, 3 ≤ capacity → capacity ≤ 4 →
        ideal s capacity key = true → lookup capacity key = true := by
  constructor
  · exact covers_ideal_of_prefix_complete s lookup
  · exact prefix_complete_of_covers_ideal s lookup

/-- A missing admissible key is a genuine counterexample to prefix
    completeness, so a deletion test can target the specification itself. -/
theorem not_prefix_complete_of_missing_ideal (s : SectorCover.Sector)
    (lookup : Nat → Nat → Bool) (capacity key : Nat)
    (hlo : 3 ≤ capacity) (hhi : capacity ≤ 4)
    (hideal : ideal s capacity key = true)
    (hmiss : lookup capacity key = false) :
    ¬ FullWordPath.PrefixComplete s lookup := by
  classical
  simp only [ideal, decide_eq_true_eq] at hideal
  obtain ⟨extra, hc, hmin, hmax, observed, hn, hs, heq⟩ := hideal
  intro hpc
  have hlookup := hpc extra observed capacity hc hmin hmax hlo hhi hn hs
  have hcap : (if capacity ≤ 3 then 3 else 4) = capacity := by
    by_cases h : capacity ≤ 3 <;> simp [h] <;> omega
  rw [hcap, heq, hmiss] at hlookup
  contradiction

end HGP13.IdealPrefixLookup
