import PrefixTreeCertificate

namespace HGP13.PrefixPackedFourth
open HGP13.Catalogues HGP13.PrefixCertificate

inductive Tree4 where
  | nil : Tree4
  | node : Tree4 → List Value → BitVec 128 → Tree4 → Tree4

def children (triple : List Value) (mask : BitVec 128) : List (List Value) :=
  ((List.range 128).filter fun z => mask.toNat.testBit z).map fun z =>
    triple ++ [BitVec.ofNat 7 z]

def entries : Tree4 → List (List Value)
  | .nil => []
  | .node left triple mask right =>
      entries left ++ children triple mask ++ entries right

def key (xs : List Value) : Nat :=
  SharedSearch.encode (xs.map BitVec.toNat)

def lookup : Tree4 → List Value → Value → Bool
  | .nil, _, _ => false
  | .node left triple mask right, query, z =>
      if query = triple then mask.toNat.testBit z.toNat
      else if key query < key triple then lookup left query z
      else lookup right query z

def has (tree : Tree4) : List Value → Bool
  | [a,b,c,d] => lookup tree [a,b,c] d
  | _ => false

theorem bit_child_mem (triple : List Value) (mask : BitVec 128) (z : Value)
    (h : mask.toNat.testBit z.toNat = true) :
    triple ++ [z] ∈ children triple mask := by
  apply List.mem_map.mpr
  refine ⟨z.toNat,List.mem_filter.mpr ⟨List.mem_range.mpr z.isLt,h⟩,?_⟩
  simp

theorem lookup_mem (tree : Tree4) (triple : List Value) (z : Value)
    (h : lookup tree triple z = true) :
    triple ++ [z] ∈ entries tree := by
  induction tree with
  | nil => simp [lookup] at h
  | node left value mask right ihLeft ihRight =>
    by_cases heq : triple = value
    · subst value
      have hb : mask.toNat.testBit z.toNat = true := by
        simpa [lookup] using h
      exact List.mem_append_left _
        (List.mem_append_right _ (bit_child_mem triple mask z hb))
    · by_cases hlt : key triple < key value
      · have hl : lookup left triple z = true := by simpa [lookup,heq,hlt] using h
        exact List.mem_append_left _ (List.mem_append_left _ (ihLeft hl))
      · have hr : lookup right triple z = true := by simpa [lookup,heq,hlt] using h
        exact List.mem_append_right _ (ihRight hr)

theorem has_mem (tree : Tree4) (xs : List Value)
    (h : has tree xs = true) : xs ∈ entries tree := by
  match xs with
  | [a,b,c,d] => exact lookup_mem tree [a,b,c] d h
  | [] => simp [has] at h
  | [_] => simp [has] at h
  | [_,_] => simp [has] at h
  | [_,_,_] => simp [has] at h
  | _ :: _ :: _ :: _ :: _ :: _ => simp [has] at h

def nodeStepOK (base goals xs : List Value) (next : Tree4) : Bool :=
  (PrefixCertificate.options base goals xs).all fun z =>
    has next (CanonicalPaths.normalize (xs ++ [z]))

def stepOK (base goals : List Value)
    (current : PrefixTreeCertificate.Tree) (next : Tree4) : Bool :=
  (PrefixTreeCertificate.entries current).all fun xs => nodeStepOK base goals xs next

theorem stepOK_of_nodes (base goals : List Value)
    (current : PrefixTreeCertificate.Tree) (next : Tree4)
    (h : ∀ xs ∈ PrefixTreeCertificate.entries current,
      nodeStepOK base goals xs next = true) :
    stepOK base goals current next = true := List.all_eq_true.mpr h

theorem stepOK_refines (base goals : List Value)
    (current : PrefixTreeCertificate.Tree) (next : Tree4)
    (h : stepOK base goals current next = true) :
    PrefixCertificate.stepOK base goals
      (PrefixTreeCertificate.entries current) (entries next) = true := by
  apply List.all_eq_true.mpr
  intro xs hxs
  apply List.all_eq_true.mpr
  intro z hz
  have hx := List.all_eq_true.mp h xs hxs
  change (PrefixCertificate.options base goals xs).all
    (fun z => has next (CanonicalPaths.normalize (xs ++ [z]))) = true at hx
  have hz' := List.all_eq_true.mp hx z hz
  exact List.contains_iff_mem.mpr (has_mem next _ hz')

def finalLeaf (goals : List Value) (lookup : Nat → Bool)
    (xs : List Value) : Bool :=
  if accepts FreeXor.maskBasis (goals ++ xs) then
    (List.range 16).all fun m =>
      lookup (SharedSearch.encode (SortEncoding.subset
        (SharedSearch.sort (xs.map BitVec.toNat)) m))
  else true

def finalNodeOK (goals : List Value) (lookup : Nat → Bool)
    (triple : List Value) (mask : BitVec 128) : Bool :=
  ((List.range 128).filter fun z => mask.toNat.testBit z).all fun z =>
    finalLeaf goals lookup (triple ++ [BitVec.ofNat 7 z])

def finalTreeOK (goals : List Value) (lookup : Nat → Bool) : Tree4 → Bool
  | .nil => true
  | .node left triple mask right =>
      finalTreeOK goals lookup left &&
      finalNodeOK goals lookup triple mask &&
      finalTreeOK goals lookup right

theorem finalNodeOK_member (goals : List Value) (lookup : Nat → Bool)
    (triple : List Value) (mask : BitVec 128)
    (h : finalNodeOK goals lookup triple mask = true)
    (xs : List Value) (hx : xs ∈ children triple mask) :
    finalLeaf goals lookup xs = true := by
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
  exact List.all_eq_true.mp h z hz

theorem finalTreeOK_member (goals : List Value) (lookup : Nat → Bool)
    (tree : Tree4) (h : finalTreeOK goals lookup tree = true) :
    ∀ xs ∈ entries tree, finalLeaf goals lookup xs = true := by
  induction tree with
  | nil => simp [entries]
  | node left triple mask right ihLeft ihRight =>
    simp only [finalTreeOK,Bool.and_eq_true] at h
    obtain ⟨⟨hl,hm⟩,hr⟩ := h
    intro xs hx
    rcases List.mem_append.mp hx with hleft | hright
    · rcases List.mem_append.mp hleft with hleft | hmid
      · exact ihLeft hl xs hleft
      · exact finalNodeOK_member goals lookup triple mask hm xs hmid
    · exact ihRight hr xs hright

theorem finalTreeOK_refines (goals : List Value) (lookup : Nat → Bool)
    (tree : Tree4) (h : finalTreeOK goals lookup tree = true) :
    finalFourOK goals lookup (entries tree) = true := by
  apply List.all_eq_true.mpr
  intro xs hx
  exact finalTreeOK_member goals lookup tree h xs hx

theorem finalFourOK_implies_finalTreeOK (goals : List Value)
    (lookup : Nat → Bool) (tree : Tree4)
    (h : finalFourOK goals lookup (entries tree) = true) :
    finalTreeOK goals lookup tree = true := by
  induction tree with
  | nil => rfl
  | node left triple mask right ihLeft ihRight =>
    have hall := List.all_eq_true.mp h
    have hl : finalFourOK goals lookup (entries left) = true := by
      apply List.all_eq_true.mpr
      intro xs hx
      exact hall xs (List.mem_append_left _ (List.mem_append_left _ hx))
    have hr : finalFourOK goals lookup (entries right) = true := by
      apply List.all_eq_true.mpr
      intro xs hx
      exact hall xs (List.mem_append_right _ hx)
    have hm : finalNodeOK goals lookup triple mask = true := by
      apply List.all_eq_true.mpr
      intro z hz
      apply hall
      apply List.mem_append_left
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨z,hz,rfl⟩
    simp only [finalTreeOK,Bool.and_eq_true]
    exact ⟨⟨ihLeft hl,hm⟩,ihRight hr⟩

theorem finalTreeOK_iff (goals : List Value) (lookup : Nat → Bool)
    (tree : Tree4) :
    finalTreeOK goals lookup tree = true ↔
      finalFourOK goals lookup (entries tree) = true :=
  ⟨finalTreeOK_refines goals lookup tree,
    finalFourOK_implies_finalTreeOK goals lookup tree⟩

structure Cert4 where
  l0 : PrefixTreeCertificate.Tree
  l1 : PrefixTreeCertificate.Tree
  l2 : PrefixTreeCertificate.Tree
  l3 : PrefixTreeCertificate.Tree
  l4 : Tree4

def asListCert (cert : Cert4) : PrefixCertificate.Cert4 :=
  ⟨PrefixTreeCertificate.entries cert.l0,
   PrefixTreeCertificate.entries cert.l1,
   PrefixTreeCertificate.entries cert.l2,
   PrefixTreeCertificate.entries cert.l3,
   entries cert.l4⟩

def verifyFour (goals : List Value) (lookup : Nat → Bool) (cert : Cert4) : Bool :=
  PrefixTreeCertificate.has cert.l0 [] &&
  PrefixTreeCertificate.stepOK FreeXor.maskBasis goals cert.l0 cert.l1 &&
  PrefixTreeCertificate.stepOK FreeXor.maskBasis goals cert.l1 cert.l2 &&
  PrefixTreeCertificate.stepOK FreeXor.maskBasis goals cert.l2 cert.l3 &&
  stepOK FreeXor.maskBasis goals cert.l3 cert.l4 &&
  finalTreeOK goals lookup cert.l4

theorem verifyFour_refines (goals : List Value) (lookup : Nat → Bool)
    (cert : Cert4) (h : verifyFour goals lookup cert = true) :
    PrefixCertificate.verifyFour goals lookup (asListCert cert) = true := by
  simp only [verifyFour,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0,h01⟩,h12⟩,h23⟩,h34⟩,hf⟩ := h
  simp only [PrefixCertificate.verifyFour,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨List.contains_iff_mem.mpr
      (PrefixTreeCertificate.has_mem cert.l0 [] h0),
    PrefixTreeCertificate.stepOK_refines _ _ _ _ h01⟩,
    PrefixTreeCertificate.stepOK_refines _ _ _ _ h12⟩,
    PrefixTreeCertificate.stepOK_refines _ _ _ _ h23⟩,
    stepOK_refines _ _ _ _ h34⟩,
    finalTreeOK_refines goals lookup cert.l4 hf⟩

theorem verifyFour_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (cert : Cert4)
    (hc : Catalogued goals 4 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hv : verifyFour goals lookup cert = true) :
    lookup (SharedSearch.encode observed) = true :=
  PrefixCertificate.verifyFour_lookup goals extra observed lookup (asListCert cert)
    hc ho hs (verifyFour_refines goals lookup cert hv)

def tinyMaskTree : Tree4 :=
  .node .nil [(3 : Value),(5 : Value),(7 : Value)] (BitVec.ofNat 128 (2^11)) .nil

theorem tiny_mask_hit :
    has tinyMaskTree [(3 : Value),(5 : Value),(7 : Value),(11 : Value)] = true :=
  by decide +kernel

theorem tiny_mask_miss :
    has tinyMaskTree [(3 : Value),(5 : Value),(7 : Value),(12 : Value)] = false :=
  by decide +kernel

end HGP13.PrefixPackedFourth
