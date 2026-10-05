import SortEncoding
import Catalogues

namespace HGP13.PrefixBridge
open HGP13.Catalogues

theorem accepts_perm_todo (available todo₁ todo₂ : List Value)
    (hp : List.Perm todo₁ todo₂) :
    accepts available todo₁ = accepts available todo₂ := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨p,hv,hr,hg⟩ := (accepts_iff_program available todo₁).mp h
    apply (accepts_iff_program available todo₂).mpr
    refine ⟨p,hv,?_,?_⟩
    · intro z hz
      exact hp.mem_iff.mp (hr hz)
    · intro z hz
      exact hg (hp.mem_iff.mpr hz)
  · intro h
    obtain ⟨p,hv,hr,hg⟩ := (accepts_iff_program available todo₂).mp h
    apply (accepts_iff_program available todo₁).mpr
    refine ⟨p,hv,?_,?_⟩
    · intro z hz
      exact hp.mem_iff.mpr (hr hz)
    · intro z hz
      exact hg (hp.mem_iff.mp hz)

theorem catalogued_perm (goals extra₁ extra₂ : List Value) (k : Nat)
    (hp : List.Perm extra₁ extra₂)
    (hc : Catalogued goals k extra₁) : Catalogued goals k extra₂ := by
  obtain ⟨hn,hl,hd,ha⟩ := hc
  refine ⟨hp.nodup_iff.mp hn,?_,?_,?_⟩
  · exact hp.length_eq.symm.trans hl
  · intro z hz
    exact hd z (hp.mem_iff.mpr hz)
  · rw [← accepts_perm_todo FreeXor.maskBasis (goals ++ extra₁)
      (goals ++ extra₂) (hp.append_left goals)]
    exact ha

theorem sorted_value_perm (extra : List Value) :
    List.Perm ((HGP13.SharedSearch.sort (extra.map BitVec.toNat)).map
      (BitVec.ofNat 7)) extra := by
  have hp := (HGP13.SortEncoding.sort_perm (extra.map BitVec.toNat)).map
    (BitVec.ofNat 7)
  have hround : (extra.map BitVec.toNat).map (BitVec.ofNat 7) = extra := by
    rw [List.map_map]
    have hfun : (BitVec.ofNat 7 ∘ BitVec.toNat : Value → Value) = id := by
      funext v
      simp [BitVec.ofNat_toNat]
    rw [hfun,List.map_id]
  rw [hround] at hp
  exact hp

theorem sorted_catalogued (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    Catalogued goals k ((HGP13.SharedSearch.sort (extra.map BitVec.toNat)).map
      (BitVec.ofNat 7)) := by
  exact catalogued_perm goals extra _ k (sorted_value_perm extra).symm hc

theorem numeric_full_shape (goals extra : List Value) (k : Nat)
    (hc : Catalogued goals k extra) :
    (HGP13.SharedSearch.sort (extra.map BitVec.toNat)).Nodup ∧
      (HGP13.SharedSearch.sort (extra.map BitVec.toNat)).length = k := by
  obtain ⟨hn,hl,_,_⟩ := hc
  have hnum : (extra.map BitVec.toNat).Nodup :=
    hn.map BitVec.toNat (fun a b hab heq => hab (BitVec.toNat_inj.mp heq))
  have hp := HGP13.SortEncoding.sort_perm (extra.map BitVec.toNat)
  exact ⟨hp.nodup_iff.mpr hnum, hp.length_eq.trans (by simpa using hl)⟩

theorem observed_catalogued_three (goals extra : List Value) (observed : List Nat)
    (hc : Catalogued goals 3 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat) :
    ∃ m : Nat, m < 8 ∧ HGP13.SharedSearch.encode observed =
      HGP13.SharedSearch.encode (HGP13.SortEncoding.subset
        (HGP13.SharedSearch.sort (extra.map BitVec.toNat)) m) := by
  obtain ⟨hn,hl⟩ := numeric_full_shape goals extra 3 hc
  exact HGP13.SortEncoding.observed_length_three_mask observed _ ho hn
    (fun z hz => (HGP13.SortEncoding.sort_perm (extra.map BitVec.toNat)).mem_iff.mpr
      (hs hz)) hl

theorem observed_catalogued_four (goals extra : List Value) (observed : List Nat)
    (hc : Catalogued goals 4 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat) :
    ∃ m : Nat, m < 16 ∧ HGP13.SharedSearch.encode observed =
      HGP13.SharedSearch.encode (HGP13.SortEncoding.subset
        (HGP13.SharedSearch.sort (extra.map BitVec.toNat)) m) := by
  obtain ⟨hn,hl⟩ := numeric_full_shape goals extra 4 hc
  exact HGP13.SortEncoding.observed_length_four_mask observed _ ho hn
    (fun z hz => (HGP13.SortEncoding.sort_perm (extra.map BitVec.toNat)).mem_iff.mpr
      (hs hz)) hl

end HGP13.PrefixBridge
