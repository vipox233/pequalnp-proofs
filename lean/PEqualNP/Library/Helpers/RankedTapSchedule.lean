import PEqualNP.Library.Helpers.RunIntervalBank
import PEqualNP.Library.Helpers.MarkedInversionRank
import Mathlib.Order.Prod.Lex.Basic

namespace PEqualNP.RankedTapSchedule

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover

abbrev Word (a : Nat) := Fin a → Bool
abbrev Level (n : Nat) := Fin (n+1)

def xs (n : Nat) (t : Level n) :=
  List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true]

abbrev State (a b : Nat) := Fin (2^b) ×ₗ Word a

def Fits (a n b : Nat) (ok : Level n → Word a → Prop) (S : Finset (Level n)) :=
  ∃ (C : Circuit) (tap : Fin a → Nat), FanInTwo C ∧ ReadsBack (n+2) C ∧
    NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i<n+2+C.size) ∧
    ∀ t ∈ S, ok t (fun i => (C.wires (xs n t)).getD (tap i) false)

private def bitInput (n : Nat) (t : Level n) (i : Fin n) := decide (i.val<t.val)

/-- Feasible original observations are exactly projections of monotone ranked schedules. -/
theorem fits_iff (ok : Level n → Word a → Prop) (S : Finset (Level n)) :
    Fits a n b ok S ↔ ∃ F : Level n → State a b,
      Monotone F ∧ ∀ t ∈ S, ok t (ofLex (F t)).2 := by
  constructor
  · rintro ⟨C,tap,fan,_,neg,_,_,pass⟩
    obtain ⟨r,mono,cap,same⟩ := MarkedInversionRank.circuit_rank (n:=n) C fan
    have up {s t : Level n} (h : s≤t) : bitInput n s ≤ bitInput n t := by
      intro j
      apply Bool.le_iff_imp.2
      simp only [bitInput,decide_eq_true_eq]
      exact fun p => lt_of_lt_of_le p h
    let rank (t : Level n) : Fin (2^b) :=
      ⟨r (bitInput n t),(cap _).trans_le (Nat.pow_le_pow_right (by decide) neg)⟩
    let word (t : Level n) (j : Fin a) := (C.wires (xs n t)).getD (tap j) false
    refine ⟨fun t => toLex (rank t,word t),?_,pass⟩
    intro s t h
    apply Prod.Lex.toLex_le_toLex'.2
    refine ⟨mono (up h),fun eq j => Bool.le_iff_imp.2 ?_⟩
    exact same _ _ (up h) (congrArg Fin.val eq) (tap j)
  · rintro ⟨F,m,pass⟩
    let idx (k : Nat) : Level n := ⟨min k n,by omega⟩
    let r (k : Nat) := (ofLex (F (idx k))).1.val
    let f (k : Nat) := (ofLex (F (idx k))).2
    have pair {s t : Nat} (h : s≤t) : F (idx s) ≤ F (idx t) :=
      m (show min s n ≤ min t n from min_le_min_right _ h)
    have rup : Monotone r := fun _ _ h => (Prod.Lex.le_iff'.1 (pair h)).1
    let cuts := RunIntervalBank.cuts n f
    have grow {s t : Nat} (h : s<t) (ht : t∈cuts) : r s < r t := by
      obtain ⟨_,pos,j,high,low⟩ := Finset.mem_filter.mp ht
      apply lt_of_le_of_ne (rup h.le)
      intro eq
      have eq' : r (t-1)=r t := le_antisymm (rup (by omega)) (eq ▸ rup (by omega : s≤t-1))
      have nonfall := (Prod.Lex.le_iff'.1 (pair (by omega : t-1≤t))).2 (Fin.ext eq') j
      have yes := Bool.le_iff_imp.mp nonfall high
      exact Bool.noConfusion (yes.symm.trans low)
    have zero : 0∉cuts := by simp [cuts,RunIntervalBank.cuts]
    let scope := insert 0 cuts
    have inject : (scope : Set Nat).InjOn r := by
      intro x hx y hy eq
      rcases lt_trichotomy x y with lt|e|gt
      · exact ((grow lt ((Finset.mem_insert.mp hy).resolve_left (by omega))).ne eq).elim
      · exact e
      · exact ((grow gt ((Finset.mem_insert.mp hx).resolve_left (by omega))).ne eq.symm).elim
    have bound := Finset.card_le_card_of_injOn (s:=scope) (t:=Finset.range (2^b)) r
      (fun k _ => Finset.mem_range.mpr (ofLex (F (idx k))).1.isLt) inject
    have room : cuts.card < 2^b := by simpa [scope,Finset.card_insert_of_notMem zero] using bound
    obtain ⟨C,tap,fan,back,valid,neg,_,eq⟩ := RunIntervalBank.upper n b f room
    refine ⟨C,fun j => (tap j).val,fan,back,neg.le,valid,fun j => (tap j).isLt,?_⟩
    intro t ht
    have it : idx t.val = t := Fin.ext (min_eq_left (by have := t.isLt; omega))
    convert pass t ht using 1
    exact funext fun j => (eq t j).trans (by simp [f,it])

def Affordable (a n b e : Nat) (cost : Fin (n+1) → (Fin a → Bool) → Nat)
    (S : Finset (Fin (n+1))) : Prop :=
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin a → Nat),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C ∧
    PEqualNP.NotBracket.notCount C ≤ b ∧ C.output < n+2+C.size ∧ (∀ i, tap i < n+2+C.size) ∧
    S.sum (fun t => cost t (fun i => (C.wires
      (List.ofFn (fun j : Fin n => decide (j.val < t.val)) ++ [false,true])).getD (tap i) false)) ≤ e

/-- A cost on the emitted joint word can be tested on the same original levels of a ranked schedule. -/
theorem affordable_iff {a n b : Nat} (cost : Level n → Word a → Nat)
    (S : Finset (Level n)) (e : Nat) :
    Affordable a n b e cost S ↔ ∃ F : Level n → State a b, Monotone F ∧
      S.sum (fun i => cost i (ofLex (F i)).2) ≤ e := by
  constructor
  · rintro ⟨C, tap, fan, back, neg, valid, taps, paid⟩
    let word (i : Level n) : Word a := fun j => (C.wires (xs n i)).getD (tap j) false
    have physical : Fits a n b (fun i v => v = word i) S :=
      ⟨C, tap, fan, back, neg, valid, taps, fun _ _ => rfl⟩
    obtain ⟨F, mono, same⟩ := (fits_iff _ _).mp physical
    refine ⟨F, mono, ?_⟩
    have equal : S.sum (fun i => cost i (ofLex (F i)).2) = S.sum (fun i => cost i (word i)) :=
      Finset.sum_congr rfl fun i hi => congrArg (cost i) (same i hi)
    exact equal.trans_le paid
  · rintro ⟨F, mono, paid⟩
    let word (i : Level n) : Word a := (ofLex (F i)).2
    have physical : Fits a n b (fun i v => v = word i) S :=
      (fits_iff _ _).mpr ⟨F, mono, fun _ _ => rfl⟩
    obtain ⟨C, tap, fan, back, neg, valid, taps, same⟩ := physical
    refine ⟨C, tap, fan, back, neg, valid, taps, ?_⟩
    have equal : S.sum (fun i => cost i (fun j => (C.wires (xs n i)).getD (tap j) false)) =
        S.sum (fun i => cost i (word i)) :=
      Finset.sum_congr rfl fun i hi => congrArg (cost i) (same i hi)
    exact equal.trans_le paid

end PEqualNP.RankedTapSchedule
