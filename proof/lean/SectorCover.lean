import ZeroSector
import TransposeBudget

namespace HGP13.SectorCover
open Budget Transposition TransposeTarget
set_option maxRecDepth 20000

theorem oriented_involution (p : Program) : oriented (oriented p) = p := by
  simp [oriented,rename,dual,List.map_reverse,List.map_map,Function.comp_def,
    renameGate,swap,perm_involution]

theorem used_outputs_swapped (p : Program) :
    (usedOutputs (oriented p)).length = (touchedSources p).length := by
  have hh := touched_sources_length (oriented p)
  rw [oriented_involution] at hh
  exact hh.symm

theorem touched_subset (p : Program) : touchedSources p ⊆ sources := by
  intro i hi
  exact (List.mem_filter.mp hi).1
theorem touched_nodup (p : Program) : (touchedSources p).Nodup := List.Pairwise.filter _ sources_nodup
theorem used_subset (p : Program) : usedOutputs p ⊆ privateOutputs := by
  intro i hi
  exact (List.mem_filter.mp hi).1
theorem used_nodup (p : Program) : (usedOutputs p).Nodup := List.Pairwise.filter _ private_nodup

def singles (u : List Wire) : List (List Wire) := u.map (fun x => [x])
def pairs (u : List Wire) : List (List Wire) :=
  u.flatMap (fun x => (u.filter (fun y => x.val < y.val)).map (fun y => [x,y]))
def SameSet (a b : List Wire) : Prop := ∀ z, z ∈ a ↔ z ∈ b
def pairCheck (a : List Wire) (x y : Wire) : Bool :=
  a.contains x && a.contains y && a.all (fun z => z == x || z == y)

theorem pair_check_same (a : List Wire) (x y : Wire) (h : pairCheck a x y = true) :
    SameSet a [x,y] := by
  simp only [pairCheck,Bool.and_eq_true] at h
  intro z
  constructor
  · intro hz
    have hh := List.all_eq_true.mp h.2 z hz
    simpa using hh
  · intro hz
    rcases (show z = x ∨ z = y from by simpa using hz) with rfl | rfl
    · exact List.contains_iff_mem.mp h.1.1
    · exact List.contains_iff_mem.mp h.1.2

theorem source_pair_complete : ∀ x y : Wire, x ∈ sources → y ∈ sources → x ≠ y →
    (pairs sources).any (fun a => pairCheck a x y) = true := by decide
theorem output_pair_complete : ∀ x y : Wire, x ∈ privateOutputs → y ∈ privateOutputs → x ≠ y →
    (pairs privateOutputs).any (fun a => pairCheck a x y) = true := by decide
theorem output_single_pad : ∀ x : Wire, x ∈ privateOutputs →
    (pairs privateOutputs).any (fun a => a.contains x) = true := by decide

theorem list_one (a : List Wire) (h : a.length = 1) : ∃ x, a = [x] := by
  cases a with
  | nil => simp at h
  | cons x a =>
    have hn : a.length = 0 := by simp only [List.length_cons] at h; omega
    exact ⟨x,by rw [List.eq_nil_of_length_eq_zero hn]⟩

theorem list_two (a : List Wire) (h : a.length = 2) : ∃ x y, a = [x,y] := by
  cases a with
  | nil => simp at h
  | cons x a =>
    have hn : a.length = 1 := by simp only [List.length_cons] at h; omega
    obtain ⟨y,rfl⟩ := list_one a hn
    exact ⟨x,y,rfl⟩

theorem choose_one (u a : List Wire) (hs : a ⊆ u) (hl : a.length = 1) :
    ∃ b ∈ singles u, SameSet b a := by
  obtain ⟨x,rfl⟩ := list_one a hl
  refine ⟨[x],List.mem_map.mpr ⟨x,hs (by simp),rfl⟩,?_⟩
  intro z
  rfl

theorem choose_two (u a : List Wire)
    (complete : ∀ x y : Wire, x ∈ u → y ∈ u → x ≠ y →
      (pairs u).any (fun b => pairCheck b x y) = true)
    (hs : a ⊆ u) (hn : a.Nodup) (hl : a.length = 2) :
    ∃ b ∈ pairs u, SameSet b a := by
  obtain ⟨x,y,rfl⟩ := list_two a hl
  have ne : x ≠ y := by simpa using hn
  obtain ⟨b,hb,hc⟩ := List.any_eq_true.mp (complete x y (hs (by simp)) (hs (by simp)) ne)
  exact ⟨b,hb,pair_check_same b x y hc⟩

theorem pad_two (a : List Wire) (hs : a ⊆ privateOutputs) (hn : a.Nodup) (hl : a.length ≤ 2) :
    ∃ b ∈ pairs privateOutputs, a ⊆ b := by
  by_cases hz : a.length = 0
  · rw [List.eq_nil_of_length_eq_zero hz]
    exact ⟨[6,7],by decide,by simp⟩
  · by_cases ho : a.length = 1
    · obtain ⟨x,rfl⟩ := list_one a ho
      obtain ⟨b,hb,hc⟩ := List.any_eq_true.mp (output_single_pad x (hs (by simp)))
      refine ⟨b,hb,?_⟩
      intro z hz
      have he : z = x := by simpa using hz
      rw [he]
      exact List.contains_iff_mem.mp hc
    · have ht : a.length = 2 := by omega
      obtain ⟨b,hb,he⟩ := choose_two privateOutputs a output_pair_complete hs hn ht
      exact ⟨b,hb,fun z hz => (he z).mpr hz⟩

theorem pad_one (a : List Wire) (hs : a ⊆ privateOutputs) (hl : a.length ≤ 1) :
    ∃ b ∈ singles privateOutputs, a ⊆ b := by
  by_cases hz : a.length = 0
  · rw [List.eq_nil_of_length_eq_zero hz]
    exact ⟨[6],by decide,by simp⟩
  · have ho : a.length = 1 := by omega
    obtain ⟨b,hb,he⟩ := choose_one privateOutputs a hs ho
    exact ⟨b,hb,fun z hz => (he z).mpr hz⟩

structure Sector where
  transposed : Bool
  active : List Wire
  carriers : List Wire
  deriving DecidableEq, BEq

def family (o : Bool) (aa rr : List (List Wire)) : List Sector :=
  aa.flatMap (fun a => rr.map (fun r => ⟨o,a,r⟩))
def family22 : List Sector := family false (pairs sources) (pairs privateOutputs)
def family21 : List Sector := family true (pairs sources) (singles privateOutputs)
def family11 : List Sector := family false (singles sources) (singles privateOutputs)
def family10 : List Sector := family false (singles sources) [[]]
def family01 : List Sector := family true (singles sources) [[]]
def sectors : List Sector := family22 ++ family21 ++ family11 ++ family10 ++ family01
def word (s : Sector) (p : Program) : Program := if s.transposed then oriented p else p
def Compatible (s : Sector) (p : Program) : Prop :=
  SameSet s.active (touchedSources (word s p)) ∧ usedOutputs (word s p) ⊆ s.carriers

theorem family22_length : family22.length = 225 := by decide
theorem family21_length : family21.length = 90 := by decide
theorem family11_length : family11.length = 36 := by decide
theorem family10_length : family10.length = 6 := by decide
theorem family01_length : family01.length = 6 := by decide
theorem sectors_length : sectors.length = 363 := by
  simp [sectors,family22_length,family21_length,family11_length,family10_length,family01_length]

set_option maxHeartbeats 2000000 in
theorem sectors_nodup : sectors.Nodup := by decide

theorem family_member (o : Bool) (aa rr : List (List Wire)) (a r : List Wire)
    (ha : a ∈ aa) (hr : r ∈ rr) : (⟨o,a,r⟩ : Sector) ∈ family o aa rr :=
  List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨r,hr,rfl⟩⟩

theorem cover22 (p : Program) (hu : (touchedSources p).length = 2)
    (hv : (usedOutputs p).length ≤ 2) : ∃ s ∈ sectors, Compatible s p := by
  obtain ⟨a,ha,he⟩ := choose_two sources (touchedSources p) source_pair_complete
    (touched_subset p) (touched_nodup p) hu
  obtain ⟨r,hr,hs⟩ := pad_two (usedOutputs p) (used_subset p) (used_nodup p) hv
  refine ⟨⟨false,a,r⟩,?_,he,hs⟩
  have hh : (⟨false,a,r⟩ : Sector) ∈ family22 := family_member false _ _ a r ha hr
  simp [sectors,hh]

theorem cover21 (p : Program) (hu : (touchedSources p).length ≤ 1)
    (hv : (usedOutputs p).length = 2) : ∃ s ∈ sectors, Compatible s p := by
  have ht : (touchedSources (oriented p)).length = 2 := by rw [touched_sources_length,hv]
  have hr : (usedOutputs (oriented p)).length ≤ 1 := by rw [used_outputs_swapped]; exact hu
  obtain ⟨a,ha,he⟩ := choose_two sources (touchedSources (oriented p)) source_pair_complete
    (touched_subset _) (touched_nodup _) ht
  obtain ⟨r,hrr,hs⟩ := pad_one (usedOutputs (oriented p)) (used_subset _) hr
  refine ⟨⟨true,a,r⟩,?_,he,hs⟩
  have hh : (⟨true,a,r⟩ : Sector) ∈ family21 := family_member true _ _ a r ha hrr
  simp [sectors,hh]

theorem cover11 (p : Program) (hu : (touchedSources p).length = 1)
    (hv : (usedOutputs p).length ≤ 1) : ∃ s ∈ sectors, Compatible s p := by
  obtain ⟨a,ha,he⟩ := choose_one sources (touchedSources p) (touched_subset p) hu
  obtain ⟨r,hr,hs⟩ := pad_one (usedOutputs p) (used_subset p) hv
  refine ⟨⟨false,a,r⟩,?_,he,hs⟩
  have hh : (⟨false,a,r⟩ : Sector) ∈ family11 := family_member false _ _ a r ha hr
  simp [sectors,hh]

theorem cover10 (p : Program) (hu : (touchedSources p).length = 1)
    (hv : (usedOutputs p).length = 0) : ∃ s ∈ sectors, Compatible s p := by
  obtain ⟨a,ha,he⟩ := choose_one sources (touchedSources p) (touched_subset p) hu
  refine ⟨⟨false,a,[]⟩,?_,he,?_⟩
  · have hh : (⟨false,a,[]⟩ : Sector) ∈ family10 := family_member false _ _ a [] ha (by simp)
    simp [sectors,hh]
  · change usedOutputs p ⊆ []
    rw [List.eq_nil_of_length_eq_zero hv]
    exact List.Subset.refl _

theorem cover01 (p : Program) (hu : (touchedSources p).length = 0)
    (hv : (usedOutputs p).length = 1) : ∃ s ∈ sectors, Compatible s p := by
  have ht : (touchedSources (oriented p)).length = 1 := by rw [touched_sources_length,hv]
  obtain ⟨a,ha,he⟩ := choose_one sources (touchedSources (oriented p)) (touched_subset _) ht
  refine ⟨⟨true,a,[]⟩,?_,he,?_⟩
  · have hh : (⟨true,a,[]⟩ : Sector) ∈ family01 := family_member true _ _ a [] ha (by simp)
    simp [sectors,hh]
  · change usedOutputs (oriented p) ⊆ []
    have hz : (usedOutputs (oriented p)).length = 0 := by rw [used_outputs_swapped,hu]
    rw [List.eq_nil_of_length_eq_zero hz]
    exact List.Subset.refl _

theorem every_short_word_covered (p : Program) (hp : Legal p) (real : run identity p = target)
    (hl : p.length ≤ 18) : ∃ s ∈ sectors, Compatible s p := by
  have small := TransposeBudget.short_program_small_sector p real hl
  by_cases hu2 : (touchedSources p).length = 2
  · exact cover22 p hu2 small.2
  · have hu1 : (touchedSources p).length ≤ 1 := by omega
    by_cases hv2 : (usedOutputs p).length = 2
    · exact cover21 p hu1 hv2
    · have hv1 : (usedOutputs p).length ≤ 1 := by omega
      by_cases hu : (touchedSources p).length = 1
      · by_cases hv : (usedOutputs p).length = 0
        · exact cover10 p hu hv
        · exact cover11 p hu hv1
      · have hu0 : (touchedSources p).length = 0 := by omega
        have hv : (usedOutputs p).length = 1 := by
          by_cases hz : (usedOutputs p).length = 0
          · have bad := ZeroSector.zero_sector_lower_bound p hp real hu0 hz
            omega
          · omega
        exact cover01 p hu0 hv

theorem word_length (s : Sector) (p : Program) : (word s p).length = p.length := by
  cases hs : s.transposed <;> simp [word,hs,oriented_length]
theorem word_legal (s : Sector) (p : Program) (hp : Legal p) : Legal (word s p) := by
  cases hs : s.transposed <;> simp only [word,hs,↓reduceIte]
  · exact hp
  · exact oriented_legal p hp
theorem word_realizes (s : Sector) (p : Program) (h : run identity p = target) :
    run identity (word s p) = if s.transposed then TransposeTarget.matrix else target := by
  cases hs : s.transposed <;> simp only [word,hs,↓reduceIte]
  · exact h
  · exact realizes_oriented p h

theorem active_is_used (s : Sector) (p : Program) (h : Compatible s p) (i : Wire)
    (hi : i ∈ s.active) : ∃ g ∈ word s p, g.2 = i := by
  have ht := (h.1 i).mp hi
  have hm := List.contains_iff_mem.mp (List.mem_filter.mp ht).2
  exact List.mem_map.mp hm

theorem source_target_is_active (s : Sector) (p : Program) (h : Compatible s p) (g : Gate)
    (hg : g ∈ word s p) (ht : g.2 ∈ sources) : g.2 ∈ s.active := by
  apply (h.1 g.2).mpr
  exact List.mem_filter.mpr ⟨ht,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g,hg,rfl⟩)⟩

theorem output_control_is_carrier (s : Sector) (p : Program) (h : Compatible s p) (g : Gate)
    (hg : g ∈ word s p) (hc : g.1 ∈ privateOutputs) : g.1 ∈ s.carriers := by
  apply h.2
  exact List.mem_filter.mpr ⟨hc,List.contains_iff_mem.mpr (List.mem_map.mpr ⟨g,hg,rfl⟩)⟩

/-- Full source coverage statement: the chosen sector describes a legal
word of the same length realizing the appropriate full operator. This does
not yet prove completeness of the later normalized search representation. -/
theorem full_sector_cover (p : Program) (hp : Legal p) (real : run identity p = target)
    (hl : p.length ≤ 18) : ∃ s ∈ sectors,
      Compatible s p ∧ Legal (word s p) ∧ (word s p).length = p.length ∧
      run identity (word s p) = (if s.transposed then TransposeTarget.matrix else target) := by
  obtain ⟨s,hs,hc⟩ := every_short_word_covered p hp real hl
  exact ⟨s,hs,hc,word_legal s p hp,word_length s p,word_realizes s p real⟩

end HGP13.SectorCover
