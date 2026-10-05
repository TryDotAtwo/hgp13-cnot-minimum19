import PrefixTreeCertificate

namespace HGP13.PrefixPathWitness
open HGP13.PrefixTreeCertificate HGP13.Catalogues

inductive Path where
  | here : Path
  | left : Path → Path
  | right : Path → Path
  deriving DecidableEq

def verify (tree : Tree) (value : List Value) : Path → Bool
  | .here => match tree with
    | .nil => false
    | .node _ v _ => decide (value = v)
  | .left p => match tree with
    | .nil => false
    | .node l _ _ => verify l value p
  | .right p => match tree with
    | .nil => false
    | .node _ _ r => verify r value p

theorem verify_mem (tree : Tree) (value : List Value) (path : Path)
    (h : verify tree value path = true) : value ∈ entries tree := by
  induction path generalizing tree with
  | here =>
    cases tree with
    | nil => simp [verify] at h
    | node l v r =>
      simp only [verify,decide_eq_true_eq] at h
      subst value
      simp [entries]
  | left p ih =>
    cases tree with
    | nil => simp [verify] at h
    | node l v r =>
      exact List.mem_append_left _ (ih l (by simpa [verify] using h))
  | right p ih =>
    cases tree with
    | nil => simp [verify] at h
    | node l v r =>
      exact List.mem_append_right _
        (List.mem_cons_of_mem v (ih r (by simpa [verify] using h)))

def checkOptions (next : Tree) (xs : List Value) :
    List Value → List Path → Bool
  | [], [] => true
  | z :: zs, p :: ps =>
      verify next (CanonicalPaths.normalize (xs ++ [z])) p &&
      checkOptions next xs zs ps
  | _, _ => false

theorem checkOptions_sound (next : Tree) (xs : List Value)
    (zs : List Value) (paths : List Path)
    (h : checkOptions next xs zs paths = true) :
    ∀ z ∈ zs, CanonicalPaths.normalize (xs ++ [z]) ∈ entries next := by
  induction zs generalizing paths with
  | nil => simp
  | cons z zs ih =>
    cases paths with
    | nil => simp [checkOptions] at h
    | cons p ps =>
      simp only [checkOptions,Bool.and_eq_true] at h
      obtain ⟨hv,hr⟩ := h
      intro v hvz
      rcases List.mem_cons.mp hvz with rfl | hvz
      · exact verify_mem next _ p hv
      · exact ih ps hr v hvz

def checkNode (base goals xs : List Value)
    (next : Tree) (paths : List Path) : Bool :=
  checkOptions next xs (PrefixCertificate.options base goals xs) paths

theorem checkNode_sound (base goals xs : List Value)
    (next : Tree) (paths : List Path)
    (h : checkNode base goals xs next paths = true) :
    ∀ z ∈ PrefixCertificate.options base goals xs,
      CanonicalPaths.normalize (xs ++ [z]) ∈ entries next := by
  exact checkOptions_sound next xs _ paths h

def checkLayer (base goals : List Value) (current next : Tree)
    (certs : List (List Value × List Path)) : Bool :=
  decide (certs.map Prod.fst = entries current) &&
    certs.all (fun c => checkNode base goals c.1 next c.2)

theorem checkLayer_sound (base goals : List Value) (current next : Tree)
    (certs : List (List Value × List Path))
    (h : checkLayer base goals current next certs = true) :
    PrefixCertificate.stepOK base goals (entries current) (entries next) = true := by
  simp only [checkLayer,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨heq,hall⟩ := h
  apply List.all_eq_true.mpr
  intro xs hxs
  have hc : xs ∈ certs.map Prod.fst := heq ▸ hxs
  obtain ⟨c,hcert,hfirst⟩ := List.mem_map.mp hc
  subst xs
  have hnode := List.all_eq_true.mp hall c hcert
  apply List.all_eq_true.mpr
  intro z hz
  exact List.contains_iff_mem.mpr
    (checkNode_sound base goals c.1 next c.2 hnode z hz)

end HGP13.PrefixPathWitness
