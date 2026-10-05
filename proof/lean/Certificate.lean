import Std

/-!
Soundness interface for complete layer certificates. This is independent
of a particular C++ implementation. No HGP13 layer data is certified here.
The model correspondence and the concrete certificate are separate duties.
-/
namespace LayerCertificate

inductive Reaches {State : Type} (next : State → List State)
    (initial : List State) : Nat → State → Prop
  | start {s} : s ∈ initial → Reaches next initial 0 s
  | advance {k s t} : Reaches next initial k s → t ∈ next s →
      Reaches next initial (k + 1) t

structure Certificate {State : Type} (next : State → List State)
    (initial : List State) (accept : State → Prop) (fuel : Nat) where
  layers : Nat → List State
  initial_covered : ∀ s ∈ initial, s ∈ layers 0
  successors_covered : ∀ k, k < fuel → ∀ s ∈ layers k,
    ∀ t ∈ next s, t ∈ layers (k + 1)
  no_accepting : ∀ k, k ≤ fuel → ∀ s ∈ layers k, ¬ accept s

theorem reachable_covered {State : Type} {next : State → List State}
    {initial : List State} {accept : State → Prop} {fuel : Nat}
    (cert : Certificate next initial accept fuel) {k : Nat} {s : State}
    (h : Reaches next initial k s) (hk : k ≤ fuel) : s ∈ cert.layers k := by
  induction h with
  | start hs => exact cert.initial_covered _ hs
  | @advance k s t h ht ih =>
    have hlt : k < fuel := by omega
    exact cert.successors_covered k hlt s (ih (by omega)) t ht

theorem excludes_all_paths {State : Type} {next : State → List State}
    {initial : List State} {accept : State → Prop} {fuel : Nat}
    (cert : Certificate next initial accept fuel) {k : Nat} {s : State}
    (h : Reaches next initial k s) (hk : k ≤ fuel) : ¬ accept s :=
  cert.no_accepting k hk s (reachable_covered cert h hk)

end LayerCertificate
