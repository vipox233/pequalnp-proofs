import PEqualNP.Defs
import PEqualNP.Library.Helpers.RankedTapSchedule

namespace PEqualNP.Outside.L_meta_53176

private theorem card_le_add_of_le_off {α : Type*} [DecidableEq α]
    (A B D : Finset α) (h : ∀ x ∈ A, x ∉ D → x ∈ B) :
    A.card ≤ B.card + D.card := by
  apply le_trans (Finset.card_le_card (t := B ∪ D) ?_) (Finset.card_union_le B D)
  intro x hx
  by_cases hd : x ∈ D
  · exact Finset.mem_union.mpr (Or.inr hd)
  · exact Finset.mem_union.mpr (Or.inl (h x hx hd))

private theorem charge_bound {R n B : Nat} (left right : Fin R → Fin (n+1))
    (ordered : ∀ r s, r < s → right r ≤ left s)
    (rank : Fin (n+1) → Nat) (up : Monotone rank) (cap : ∀ x, rank x < B)
    (U : Finset (Fin R)) :
    (U.filter (fun r => rank (left r) < rank (right r))).card ≤ min U.card (B-1) := by
  let D := U.filter (fun r => rank (left r) < rank (right r))
  apply le_min (Finset.card_le_card (Finset.filter_subset _ _))
  calc
    D.card ≤ (Finset.range (B-1)).card := by
      apply Finset.card_le_card_of_injOn (fun r => rank (left r))
      · intro r hr
        have h := (Finset.mem_filter.mp (show r ∈ D from hr)).2
        have hc := cap (right r)
        apply Finset.mem_range.mpr
        change rank (left r) < B-1
        omega
      · intro r hr s hs eq
        have strict {x y : Fin R} (hx : x ∈ D) (hxy : x < y) :
            rank (left x) < rank (left y) :=
          ((Finset.mem_filter.mp hx).2).trans_le (up (ordered x y hxy))
        rcases lt_trichotomy r s with h | h | h
        · exact ((strict hr h).ne eq).elim
        · exact h
        · exact ((strict hs h).ne eq.symm).elim
    _ = B-1 := Finset.card_range _

end PEqualNP.Outside.L_meta_53176

open PEqualNP.RankedTapSchedule

theorem PEqualNP.Outside.L_meta_53176 :
∀ (n T R a m : Nat) (b : Fin T → Nat)
    (left mid right : Fin R → Fin (n+1))
    (early late : Fin R → Fin m → Fin (n+1))
    (P : Fin R → Fin m → (Fin a → Bool) → Bool)
    (lo hi : Fin R → Fin m → Nat),
  (∀ r s, r < s → right r ≤ left s) →
  (∀ r, left r ≤ mid r ∧ mid r ≤ right r) →
  (∀ r j, left r ≤ early r j ∧ early r j ≤ mid r ∧
    mid r ≤ late r j ∧ late r j ≤ right r) →
  (∀ r j, Monotone (P r j)) →
  (∀ r j, lo r j ≤ hi r j ∧ hi r j ≤ T) →
  ∀ (C : Fin T → PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin T → Fin a → Nat),
  (∀ t, PEqualNP.MetaComplexity.FanInTwo (C t) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) (C t) ∧
    PEqualNP.NotBracket.notCount (C t) ≤ b t ∧ (C t).output < n+2+(C t).size ∧
    ∀ i, tap t i < n+2+(C t).size) →
  let word := fun (t : Fin T) (x : Fin (n+1)) (i : Fin a) =>
    ((C t).wires (List.ofFn (fun j : Fin n => decide (j.val < x.val)) ++ [false,true])).getD (tap t i) false
  let count := fun (r : Fin R) (j : Fin m) (x : Fin (n+1)) =>
    ((Finset.univ : Finset (Fin T)).filter (fun t => P r j (word t x) = true)).card
  (∀ r j, lo r j ≤ count r j (early r j) ∧ count r j (late r j) ≤ hi r j) →
  let err := fun (r : Fin R) => (Finset.univ : Finset (Fin m)).sup (fun j =>
    max (lo r j - count r j (mid r)) (count r j (mid r) - hi r j))
  ∀ U : Finset (Fin R), U.sum err ≤
    (Finset.univ : Finset (Fin T)).sum (fun t => min U.card (2^(b t)-1)) := by
  intro n T R a m b left mid right early late P lo hi ordered windows visits testMono _
    C tap valid word count bounds err U
  have scheduled (t : Fin T) :
      ∃ F : Level n → State a (b t), Monotone F ∧ ∀ x, (ofLex (F x)).2 = word t x := by
    have fits : Fits a n (b t) (fun x v => v = word t x) Finset.univ := by
      obtain ⟨fan, back, neg, out, taps⟩ := valid t
      exact ⟨C t, tap t, fan, back, neg, out, taps, fun _ _ => rfl⟩
    obtain ⟨F, up, same⟩ := (fits_iff _ _).mp fits
    exact ⟨F, up, fun x => same x (Finset.mem_univ x)⟩
  choose F Fmono Fword using scheduled
  let rank (t : Fin T) (x : Level n) := (ofLex (F t x)).1.val
  have rankMono (t : Fin T) : Monotone (rank t) := by
    intro x y h
    exact (Prod.Lex.le_iff'.mp (Fmono t h)).1
  have rankCap (t : Fin T) (x : Level n) : rank t x < 2^(b t) :=
    (ofLex (F t x)).1.isLt
  have wordMono (t : Fin T) {x y : Level n} (h : x ≤ y)
      (eq : rank t x = rank t y) : word t x ≤ word t y := by
    rw [← Fword t x, ← Fword t y]
    exact (Prod.Lex.le_iff'.mp (Fmono t h)).2 (Fin.ext eq)
  let charged (r : Fin R) (t : Fin T) := rank t (left r) < rank t (right r)
  let charges (r : Fin R) := (Finset.univ : Finset (Fin T)).filter (charged r)
  have word_le (r : Fin R) (t : Fin T) (ht : t ∉ charges r)
      {x y : Level n} (hx : left r ≤ x) (hxy : x ≤ y) (hy : y ≤ right r) :
      word t x ≤ word t y := by
    have hflat : ¬ charged r t := fun hc =>
      ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩)
    have hback : rank t (right r) ≤ rank t (left r) := le_of_not_gt hflat
    exact wordMono t hxy (le_antisymm (rankMono t hxy)
      ((rankMono t hy).trans (hback.trans (rankMono t hx))))
  have count_le (r : Fin R) (j : Fin m) {x y : Level n}
      (hx : left r ≤ x) (hxy : x ≤ y) (hy : y ≤ right r) :
      count r j x ≤ count r j y + (charges r).card := by
    apply PEqualNP.Outside.L_meta_53176.card_le_add_of_le_off
    intro t ht hd
    have positive := (Finset.mem_filter.mp ht).2
    have up := testMono r j (word_le r t hd hx hxy hy)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.le_iff_imp.mp up positive⟩
  have err_le (r : Fin R) : err r ≤ (charges r).card := by
    apply Finset.sup_le_iff.mpr
    intro j _
    obtain ⟨before, earlyMid, midLate, after⟩ := visits r j
    obtain ⟨lower, upper⟩ := bounds r j
    have hEarly := count_le r j before earlyMid (windows r).2
    have hLate := count_le r j (windows r).1 midLate after
    exact max_le (by omega) (by omega)
  calc
    U.sum err ≤ U.sum (fun r => (charges r).card) :=
      Finset.sum_le_sum fun r _ => err_le r
    _ = (Finset.univ : Finset (Fin T)).sum (fun t => (U.filter (fun r => charged r t)).card) := by
      calc
        _ = U.sum (fun r => (Finset.univ : Finset (Fin T)).sum
            (fun t => if charged r t then (1 : Nat) else 0)) := by
          exact Finset.sum_congr rfl fun r _ =>
            (Finset.sum_boole (R := Nat) (charged r) Finset.univ).symm
        _ = (Finset.univ : Finset (Fin T)).sum (fun t => U.sum
            (fun r => if charged r t then (1 : Nat) else 0)) := Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun t _ =>
          Finset.sum_boole (R := Nat) (fun r => charged r t) U
    _ ≤ _ := Finset.sum_le_sum fun t _ =>
      PEqualNP.Outside.L_meta_53176.charge_bound left right ordered
        (rank t) (rankMono t) (rankCap t) U
