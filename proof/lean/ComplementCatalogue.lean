import Catalogues

namespace HGP13.ComplementCatalogue
open HGP13.Catalogues

def derivableAlt (available : List Value) (z : Value) : Bool :=
  available.any (fun a => available.contains (z ^^^ a))

theorem derivableAlt_eq (available : List Value) (z : Value) :
    derivableAlt available z = derivable available z := by
  apply Bool.eq_iff_iff.mpr
  exact (derivable_complement_test available z).symm

def readyAlt (available : List Value) (z : Value) : Bool :=
  !available.contains z && derivableAlt available z

theorem readyAlt_eq (available : List Value) (z : Value) :
    readyAlt available z = ready available z := by
  simp only [readyAlt,ready,derivableAlt_eq]

def buildAlt : Nat → List Value → List Value → List Value
  | 0, _, _ => []
  | n+1, todo, available =>
      match todo.find? (readyAlt available) with
      | none => []
      | some z => z :: buildAlt n (todo.erase z) (z :: available)

theorem buildAlt_eq (n : Nat) (todo available : List Value) :
    buildAlt n todo available = build n todo available := by
  induction n generalizing todo available with
  | zero => rfl
  | succ n ih =>
    have hf : todo.find? (readyAlt available) = todo.find? (ready available) := by
      congr 1
      funext z
      exact readyAlt_eq available z
    cases hfind : todo.find? (ready available) with
    | none =>
      have ha : todo.find? (readyAlt available) = none := hf.trans hfind
      simp only [buildAlt,build,ha,hfind]
    | some z =>
      have ha : todo.find? (readyAlt available) = some z := hf.trans hfind
      simpa only [buildAlt,build,ha,hfind,List.cons.injEq,true_and] using
        ih (todo.erase z) (z :: available)

def acceptsAlt (available todo : List Value) : Bool :=
  todo.all (endState available (buildAlt todo.length todo available)).contains

theorem acceptsAlt_eq (available todo : List Value) :
    acceptsAlt available todo = accepts available todo := by
  simp only [acceptsAlt,accepts,saturation,buildAlt_eq]

end HGP13.ComplementCatalogue
