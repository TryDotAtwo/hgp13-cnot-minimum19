import CoordinateRestriction
import SectorCover
import RemainingBound

namespace HGP13.SectorCoordinates
open Budget SectorCover CoordinateRestriction

/-- Column order: all six sources, centre, selected private outputs. -/
def layout (s : Sector) : List Wire := sources ++ [8] ++ s.carriers
def changing (s : Sector) : List Wire := s.active ++ [8] ++ s.carriers
def keep (s : Sector) (i : Wire) : Bool := (layout s).contains i
def embed (s : Sector) (i : Fin (layout s).length) : Wire := (layout s)[i.val]
def core (s : Sector) (p : Program) := (word s p).filter (fun g => keep s g.2)
def passive (s : Sector) := privateOutputs.filter (fun j => !s.carriers.contains j)
def goal (s : Sector) : Matrix := if s.transposed then TransposeTarget.matrix else target

theorem wire_partition : ∀ i : Wire, i ∈ sources ∨ i = 8 ∨ i ∈ privateOutputs := by decide

theorem layouts_checked : sectors.all (fun s => decide
    ((layout s).Nodup ∧ (layout s).length = 7 + s.carriers.length ∧
      s.carriers.length ≤ 2 ∧ s.active ⊆ sources ∧ s.carriers ⊆ privateOutputs)) = true := by
  decide +kernel

theorem layout_properties (s : Sector) (hs : s ∈ sectors) :
    (layout s).Nodup ∧ (layout s).length = 7 + s.carriers.length ∧
      s.carriers.length ≤ 2 ∧ s.active ⊆ sources ∧ s.carriers ⊆ privateOutputs := by
  exact of_decide_eq_true (List.all_eq_true.mp layouts_checked s hs)

theorem embed_injective (s : Sector) (hs : s ∈ sectors) : Function.Injective (embed s) := by
  intro i j h
  apply Fin.ext
  exact (layout_properties s hs).1.getElem_inj.mp h

theorem embed_image (s : Sector) (i : Wire) :
    (∃ k, embed s k = i) ↔ i ∈ layout s := by
  constructor
  · rintro ⟨k, rfl⟩
    exact List.getElem_mem _
  · intro h
    obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp h
    exact ⟨⟨k,hk⟩,he⟩

theorem control_retained (s : Sector) (p : Program) (h : Compatible s p)
    (g : Gate) (hg : g ∈ word s p) : keep s g.1 = true := by
  apply List.contains_iff_mem.mpr
  rcases wire_partition g.1 with hc | hc | hc
  · simp [layout,hc]
  · simp [layout,hc]
  · have hh := output_control_is_carrier s p h g hg hc
    simp [layout,hh]

theorem retained_target_changes (s : Sector) (p : Program) (h : Compatible s p)
    (g : Gate) (hg : g ∈ core s p) : g.2 ∈ changing s := by
  obtain ⟨hp,hk⟩ := List.mem_filter.mp hg
  have hm := List.contains_iff_mem.mp hk
  rcases (show g.2 ∈ sources ∨ g.2 = 8 ∨ g.2 ∈ s.carriers from by
    simpa [layout,keep] using hm) with ht | ht | ht
  · have ha := source_target_is_active s p h g hp ht
    simp [changing,ha]
  · simp [changing,ht]
  · simp [changing,ht]

/-- Inactive sources are fixed throughout the original word, not only at its endpoint. -/
theorem fixed_source_prefix (s : Sector) (p q r : Program) (h : Compatible s p)
    (hq : word s p = q ++ r) (i : Wire) (hi : i ∈ sources) (ha : i ∉ s.active) :
    run identity q i = identity i := by
  apply run_untargeted
  intro hm
  obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
  have hp : g ∈ word s p := by rw [hq]; exact List.mem_append_left _ hg
  exact ha (he ▸ source_target_is_active s p h g hp (he ▸ hi))

theorem core_endpoints (s : Sector) (p : Program) (h : Compatible s p)
    (g : Gate) (hg : g ∈ core s p) :
    (∃ c, embed s c = g.1) ∧ (∃ t, embed s t = g.2) := by
  obtain ⟨hp,ht⟩ := List.mem_filter.mp hg
  exact ⟨(embed_image s g.1).mpr (List.contains_iff_mem.mp (control_retained s p h g hp)),
    (embed_image s g.2).mpr (List.contains_iff_mem.mp ht)⟩

/-- Actual sector core, with all fixed controls retained, admits the smaller alphabet. -/
theorem normalized_core (s : Sector) (hs : s ∈ sectors) (p : Program)
    (hp : Legal p) (hc : Compatible s p) :
    ∃ q : List (SmallGate (layout s).length),
      q.map (liftGate (embed s)) = core s p ∧
      q.length = (core s p).length ∧ (∀ g ∈ q, g.1 ≠ g.2) ∧
      smallRun (fun i j => decide (i = j)) q = restrict (embed s) (run identity (word s p)) := by
  obtain ⟨q,hq⟩ := word_lifts (embed s) (core s p) (core_endpoints s p hc)
  have legal : Legal (core s p) := by
    intro g hg
    exact word_legal s p hp g (List.mem_filter.mp hg).1
  refine ⟨q,hq,?_,?_,?_⟩
  · rw [← hq, List.length_map]
  · apply (lifted_legal_iff (embed s) (embed_injective s hs) q).mp
    rwa [hq]
  · rw [← restrict_identity (embed s) (embed_injective s hs),
      ← restrict_run (embed s) (embed_injective s hs), hq]
    have agree := erase_passive_preserves_core (keep s) (word s p)
      (control_retained s p hc) identity identity (fun _ _ => rfl)
    funext i j
    have hk : keep s (embed s i) = true :=
      List.contains_iff_mem.mpr ((embed_image s _).mp ⟨i,rfl⟩)
    exact congrArg (fun r : Row => r.getLsbD (embed s j).val) (agree _ hk).symm

theorem core_supported (s : Sector) (p : Program) (hc : Compatible s p) :
    Supported (embed s) (run identity (core s p)) := by
  obtain ⟨q,hq⟩ := word_lifts (embed s) (core s p) (core_endpoints s p hc)
  rw [← hq]
  exact run_supported (embed s) identity q (identity_supported (embed s))

def RowSupported {n : Nat} (e : Fin n → Wire) (r : Row) : Prop :=
  ∀ j, (∀ k, e k ≠ j) → r.getLsbD j.val = false

theorem delta_supported {n : Nat} (e : Fin n → Wire) (x z : Matrix)
    (hx : Supported e x) (hz : Supported e z) (i : Fin n) :
    RowSupported e (x (e i) ^^^ z (e i)) := by
  intro j hj
  simp only [BitVec.getLsbD_xor]
  change (coefficient x (e i) j ^^ coefficient z (e i) j) = false
  rw [hx i j hj, hz i j hj]
  rfl

theorem supported_ne_outside_basis {n : Nat} (e : Fin n → Wire) (r : Row)
    (hr : RowSupported e r) (j : Wire) (hj : ∀ k, e k ≠ j) : r ≠ identity j := by
  intro he
  have hb := hr j hj
  rw [he] at hb
  have hi : (identity j).getLsbD j.val = true := by
    change coefficient identity j j = true
    simp [Transposition.coefficient_identity,Transposition.unit]
  rw [hi] at hb
  contradiction

/-- Discarded passive basis rows cannot make a supported delta available. -/
theorem full_row_available_iff {n : Nat} (e : Fin n → Wire) (x : Matrix) (r : Row)
    (hr : RowSupported e r)
    (outside : ∀ j, (∀ k, e k ≠ j) → x j = identity j) :
    (∃ j, x j = r) ↔ ∃ k, x (e k) = r := by
  constructor
  · rintro ⟨j,hj⟩
    by_cases hi : ∃ k, e k = j
    · obtain ⟨k,rfl⟩ := hi
      exact ⟨k,hj⟩
    · have hn : ∀ k, e k ≠ j := fun k hk => hi ⟨k,hk⟩
      exact False.elim (supported_ne_outside_basis e r hr j hn (hj.symm.trans (outside j hn)))
  · rintro ⟨k,hk⟩
    exact ⟨e k,hk⟩

theorem core_outside_identity (s : Sector) (p : Program) (j : Wire)
    (hj : ∀ k, embed s k ≠ j) : run identity (core s p) j = identity j := by
  apply run_untargeted
  rintro hm
  obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
  have ht := (List.mem_filter.mp hg).2
  have hm : j ∈ layout s := by simpa [keep,he] using ht
  obtain ⟨k,hk⟩ := (embed_image s j).mpr hm
  exact hj k hk

theorem core_prefix_invariants (s : Sector) (p q r : Program) (hc : Compatible s p)
    (hq : core s p = q ++ r) :
    Supported (embed s) (run identity q) ∧
      ∀ j, (∀ k, embed s k ≠ j) → run identity q j = identity j := by
  have endpoints : ∀ g ∈ q,
      (∃ c, embed s c = g.1) ∧ (∃ t, embed s t = g.2) := by
    intro g hg
    apply core_endpoints s p hc g
    rw [hq]
    exact List.mem_append_left _ hg
  obtain ⟨small,hsmall⟩ := word_lifts (embed s) q endpoints
  constructor
  · rw [← hsmall]
    exact run_supported (embed s) identity small (identity_supported (embed s))
  · intro j hj
    apply run_untargeted
    rintro hm
    obtain ⟨g,hg,he⟩ := List.mem_map.mp hm
    obtain ⟨k,hk⟩ := (endpoints g hg).2
    exact hj k (hk.trans he)

/-- Exact endpoint-row availability equivalence underlying the missing-delta bound. -/
theorem delta_available_iff {n : Nat} (e : Fin n → Wire) (x z : Matrix)
    (hx : Supported e x) (hz : Supported e z)
    (ox : ∀ j, (∀ k, e k ≠ j) → x j = identity j)
    (oz : ∀ j, (∀ k, e k ≠ j) → z j = identity j) (i : Fin n) :
    ((∃ j, x j = x (e i) ^^^ z (e i)) ∨ (∃ j, z j = x (e i) ^^^ z (e i))) ↔
    ((∃ k, x (e k) = x (e i) ^^^ z (e i)) ∨
      (∃ k, z (e k) = x (e i) ^^^ z (e i))) := by
  rw [full_row_available_iff e x _ (delta_supported e x z hx hz i) ox,
      full_row_available_iff e z _ (delta_supported e x z hx hz i) oz]

theorem passive_checked : sectors.all (fun s => decide
    ((passive s).Nodup ∧ (passive s).length + s.carriers.length = 6 ∧
      (∀ j, j ∈ passive s ↔ keep s j = false) ∧
      (∀ j ∈ passive s, goal s j ≠ identity j))) = true := by decide +kernel

theorem passive_properties (s : Sector) (hs : s ∈ sectors) :
    (passive s).Nodup ∧ (passive s).length + s.carriers.length = 6 ∧
      (∀ j, j ∈ passive s ↔ keep s j = false) ∧
      (∀ j ∈ passive s, goal s j ≠ identity j) :=
  of_decide_eq_true (List.all_eq_true.mp passive_checked s hs)

theorem core_depth_bound (s : Sector) (hs : s ∈ sectors) (p : Program)
    (real : run identity p = target) (hl : p.length ≤ 18) :
    (core s p).length ≤ 12 + s.carriers.length := by
  obtain ⟨hd,hlen,hcov,hchange⟩ := passive_properties s hs
  have hreal : run identity (word s p) = goal s := word_realizes s p real
  have hb := PassiveCost.core_length_bound (keep s) (passive s) (word s p) hd hcov
    (fun j hj => by rw [hreal]; exact hchange j hj)
  change (core s p).length + (passive s).length ≤ (word s p).length at hb
  rw [word_length] at hb
  omega

/-- Uniform concrete reduction for every hypothetical short realization.
    This closes coordinate/alphabet/depth obligations, not history/pruning completeness. -/
theorem every_short_normalized (p : Program) (hp : Legal p)
    (real : run identity p = target) (hl : p.length ≤ 18) :
    ∃ s ∈ sectors, Compatible s p ∧
      ∃ q : List (SmallGate (layout s).length),
        q.map (liftGate (embed s)) = core s p ∧
        q.length ≤ 12 + s.carriers.length ∧ (∀ g ∈ q, g.1 ≠ g.2) ∧
        smallRun (fun i j => decide (i = j)) q = restrict (embed s) (goal s) := by
  obtain ⟨s,hs,hc⟩ := every_short_word_covered p hp real hl
  obtain ⟨q,hq,hlen,hleg,hrun⟩ := normalized_core s hs p hp hc
  refine ⟨s,hs,hc,q,hq,?_,hleg,?_⟩
  · rw [hlen]
    exact core_depth_bound s hs p real hl
  · rw [word_realizes s p real] at hrun
    exact hrun

end HGP13.SectorCoordinates
