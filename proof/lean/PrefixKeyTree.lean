import SharedSearch

namespace HGP13.PrefixKeyTree

inductive Tree where
  | nil
  | node : Tree → Nat → Tree → Tree

def lookup : Tree → Nat → Bool
  | .nil, _ => false
  | .node left value right, x =>
      if x == value then true
      else if x < value then lookup left x else lookup right x

end HGP13.PrefixKeyTree
