import PrefixCertificate

namespace HGP13.PrefixTreeCertificate
open HGP13.Catalogues HGP13.PrefixCertificate

inductive Tree where
  | nil : Tree
  | node : Tree → List Value → Tree → Tree

def entries : Tree → List (List Value)
  | .nil => []
  | .node left value right => entries left ++ value :: entries right

def key (xs : List Value) : Nat :=
  SharedSearch.encode (xs.map BitVec.toNat)

def has : Tree → List Value → Bool
  | .nil, _ => false
  | .node left value right, xs =>
      if xs = value then true
      else if key xs < key value then has left xs else has right xs

theorem has_mem (tree : Tree) (xs : List Value)
    (h : has tree xs = true) : xs ∈ entries tree := by
  induction tree with
  | nil => simp [has] at h
  | node left value right ihLeft ihRight =>
    by_cases heq : xs = value
    · simp [entries,heq]
    · by_cases hlt : key xs < key value
      · have hl : has left xs = true := by simpa [has,heq,hlt] using h
        exact List.mem_append_left _ (ihLeft hl)
      · have hr : has right xs = true := by simpa [has,heq,hlt] using h
        exact List.mem_append_right _ (List.mem_cons_of_mem value (ihRight hr))

def nodeStepOK (base goals : List Value) (xs : List Value) (next : Tree) : Bool :=
  (PrefixCertificate.options base goals xs).all fun z =>
    has next (CanonicalPaths.normalize (xs ++ [z]))

def stepOK (base goals : List Value) (current next : Tree) : Bool :=
  (entries current).all fun xs => nodeStepOK base goals xs next

theorem stepOK_of_nodes (base goals : List Value) (current next : Tree)
    (h : ∀ xs ∈ entries current, nodeStepOK base goals xs next = true) :
    stepOK base goals current next = true := List.all_eq_true.mpr h

theorem stepOK_refines (base goals : List Value) (current next : Tree)
    (h : stepOK base goals current next = true) :
    PrefixCertificate.stepOK base goals (entries current) (entries next) = true := by
  apply List.all_eq_true.mpr
  intro xs hxs
  apply List.all_eq_true.mpr
  intro z hz
  have hx := List.all_eq_true.mp h xs hxs
  change (PrefixCertificate.options base goals xs).all
    (fun z => has next (CanonicalPaths.normalize (xs ++ [z]))) = true at hx
  have hz' := List.all_eq_true.mp hx z hz
  exact List.contains_iff_mem.mpr (has_mem next _ hz')

structure Cert4 where
  l0 : Tree
  l1 : Tree
  l2 : Tree
  l3 : Tree
  l4 : Tree

def asListCert (cert : Cert4) : PrefixCertificate.Cert4 :=
  ⟨entries cert.l0,entries cert.l1,entries cert.l2,
   entries cert.l3,entries cert.l4⟩

def verifyFour (goals : List Value) (lookup : Nat → Bool) (cert : Cert4) : Bool :=
  has cert.l0 [] &&
  stepOK FreeXor.maskBasis goals cert.l0 cert.l1 &&
  stepOK FreeXor.maskBasis goals cert.l1 cert.l2 &&
  stepOK FreeXor.maskBasis goals cert.l2 cert.l3 &&
  stepOK FreeXor.maskBasis goals cert.l3 cert.l4 &&
  finalFourOK goals lookup (entries cert.l4)

def verifyThree (goals : List Value) (lookup : Nat → Bool) (cert : Cert4) : Bool :=
  has cert.l0 [] &&
  stepOK FreeXor.maskBasis goals cert.l0 cert.l1 &&
  stepOK FreeXor.maskBasis goals cert.l1 cert.l2 &&
  stepOK FreeXor.maskBasis goals cert.l2 cert.l3 &&
  finalThreeOK goals lookup (entries cert.l3)

theorem verifyFour_refines (goals : List Value) (lookup : Nat → Bool)
    (cert : Cert4) (h : verifyFour goals lookup cert = true) :
    PrefixCertificate.verifyFour goals lookup (asListCert cert) = true := by
  simp only [verifyFour,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h0,h01⟩,h12⟩,h23⟩,h34⟩,hf⟩ := h
  simp only [PrefixCertificate.verifyFour,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨List.contains_iff_mem.mpr (has_mem cert.l0 [] h0),
    stepOK_refines _ _ _ _ h01⟩,
    stepOK_refines _ _ _ _ h12⟩,
    stepOK_refines _ _ _ _ h23⟩,
    stepOK_refines _ _ _ _ h34⟩,hf⟩

theorem verifyThree_refines (goals : List Value) (lookup : Nat → Bool)
    (cert : Cert4) (h : verifyThree goals lookup cert = true) :
    PrefixCertificate.verifyThree goals lookup (asListCert cert) = true := by
  simp only [verifyThree,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0,h01⟩,h12⟩,h23⟩,hf⟩ := h
  simp only [PrefixCertificate.verifyThree,Bool.and_eq_true]
  exact ⟨⟨⟨⟨List.contains_iff_mem.mpr (has_mem cert.l0 [] h0),
    stepOK_refines _ _ _ _ h01⟩,
    stepOK_refines _ _ _ _ h12⟩,
    stepOK_refines _ _ _ _ h23⟩,hf⟩

theorem verifyFour_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (cert : Cert4)
    (hc : Catalogued goals 4 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hv : verifyFour goals lookup cert = true) :
    lookup (SharedSearch.encode observed) = true :=
  PrefixCertificate.verifyFour_lookup goals extra observed lookup (asListCert cert)
    hc ho hs (verifyFour_refines goals lookup cert hv)

theorem verifyThree_lookup (goals extra : List Value) (observed : List Nat)
    (lookup : Nat → Bool) (cert : Cert4)
    (hc : Catalogued goals 3 extra) (ho : observed.Nodup)
    (hs : observed ⊆ extra.map BitVec.toNat)
    (hv : verifyThree goals lookup cert = true) :
    lookup (SharedSearch.encode observed) = true :=
  PrefixCertificate.verifyThree_lookup goals extra observed lookup (asListCert cert)
    hc ho hs (verifyThree_refines goals lookup cert hv)

def tinyStart : Tree := .node .nil [] .nil
def tinyNext : Tree := .node .nil [(3 : Value)] .nil

theorem tiny_step_accepted :
    stepOK [(1 : Value),(2 : Value)] [] tinyStart tinyNext = true := by decide +kernel

theorem tiny_deleted_successor_rejected :
    stepOK [(1 : Value),(2 : Value)] [] tinyStart .nil = false := by decide +kernel

end HGP13.PrefixTreeCertificate
