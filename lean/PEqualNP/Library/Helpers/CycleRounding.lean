import PEqualNP.Defs

namespace PEqualNP.CycleRounding

/-- Number of marks of offset r strictly before position t. -/
private def marks (r : Fin (d+1)) (t : Nat) := (t+(d-r.val))/(d+1)

private theorem formula (r : Fin (d+1)) (t : Nat) :
    marks r t = t/(d+1) + (if r.val < t%(d+1) then 1 else 0) := by
  have lt : d-r.val < d+1 := by omega
  have rr := r.isLt
  simp only [marks,Nat.add_div (Nat.succ_pos d),Nat.div_eq_of_lt lt,Nat.mod_eq_of_lt lt,Nat.add_zero]
  by_cases h : r.val<t%(d+1)
  · rw [if_pos h,if_pos (show d+1≤t%(d+1)+(d-r.val) by omega)]
  · rw [if_neg h,if_neg (show ¬d+1≤t%(d+1)+(d-r.val) by omega)]

private theorem sumMarks (d t : Nat) : (∑ r : Fin (d+1), marks r t) = t := by
  let cut : Fin (d+1) := ⟨t%(d+1),Nat.mod_lt _ (Nat.succ_pos _)⟩
  have filter : Finset.univ.filter (fun r : Fin (d+1) => r.val<t%(d+1)) = Finset.Iio cut := by
    ext r
    simp [cut,Fin.lt_def]
  simp only [formula,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,Finset.sum_boole,filter,Fin.card_Iio,Nat.cast_id]
  exact Nat.div_add_mod _ _

private theorem marksMono (r : Fin (d+1)) : Monotone (marks r) :=
  fun _ _ h => Nat.div_le_div_right (Nat.add_le_add_right h _)

private theorem period (r : Fin (d+1)) (t : Nat) : marks r (t+(d+1))=marks r t+1 := by
  change (t+(d+1)+(d-r.val))/(d+1)=(t+(d-r.val))/(d+1)+1
  rw [show t+(d+1)+(d-r.val)=t+(d-r.val)+(d+1) by omega,Nat.add_div_right _ (Nat.succ_pos d)]

private abbrev hit (r : Fin (d+1)) (t a : Nat) := marks r t < marks r (t+a)

private theorem unit (r : Fin (d+1)) (t a : Nat) (ha : a≤d+1) :
    marks r (t+a) = marks r t + (if hit r t a then 1 else 0) := by
  have low := marksMono r (Nat.le_add_right t a)
  have high := marksMono r (Nat.add_le_add_left ha t)
  rw [period] at high
  by_cases wh : hit r t a
  · rw [if_pos wh]
    unfold hit at wh
    omega
  · rw [if_neg wh]
    unfold hit at wh
    omega

private theorem count (d t a : Nat) (ha : a≤d+1) :
    (Finset.univ.filter (fun r : Fin (d+1) => hit r t a)).card=a := by
  classical
  have eq := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin (d+1)))) rfl (fun r _ => unit r t a ha)
  rw [Finset.sum_add_distrib,sumMarks,sumMarks,←Finset.card_filter] at eq
  omega

private theorem adjacent (r : Fin (d+1)) (t a b : Nat) (h : a+b≤d+1) :
    ¬(hit r t a ∧ hit r (t+a) b) ∧ (a+b=d+1 → hit r t a ∨ hit r (t+a) b) := by
  have hi := marksMono r (Nat.add_le_add_left h t)
  rw [period,←Nat.add_assoc] at hi
  refine ⟨fun ⟨x,y⟩ => ?_,?_⟩
  · unfold hit at x y
    omega
  · intro tight
    have eq : marks r (t+a+b)=marks r t+1 := by rw [Nat.add_assoc,tight,period]
    unfold hit
    omega

theorem criterion (n d : Nat) (w : Fin (n+2) → Nat) :
    let D := d+1
    let T := Finset.univ.sum w
    (∀ i, w i ≤ D) →
    ∃ pick : Fin D → Finset (Fin (n+2)),
      (∀ i, (Finset.univ.filter (fun r => i ∈ pick r)).card = w i) ∧
      (∀ r, (pick r).card = T/D + (if r.val < T%D then 1 else 0)) ∧
      ∀ (r : Fin D) (i j : Fin (n+2)),
        (j.val = i.val+1 ∨ (i.val+1 = n+2 ∧ j.val = 0 ∧ (T%D = 0 ∨ w i = 0 ∨ w j = 0))) →
        w i + w j ≤ D →
        (¬ (i ∈ pick r ∧ j ∈ pick r)) ∧
        (w i + w j = D → i ∈ pick r ∨ j ∈ pick r) := by
  classical
  intro D T bound
  let weight (k : Nat) := if h : k<n+2 then w ⟨k,h⟩ else 0
  let start (k : Nat) := (Finset.range k).sum weight
  have step (k) : start (k+1)=start k+weight k := Finset.sum_range_succ ..
  have actual (i : Fin (n+2)) : weight i.val=w i := dif_pos i.isLt
  have endEq : start (n+2)=T := by
    rw [show T = ∑ i : Fin (n+2), weight i.val from Finset.sum_congr rfl fun i _ => (actual i).symm]
    exact (Fin.sum_univ_eq_sum_range weight (n+2)).symm
  let pick (r : Fin D) := Finset.univ.filter (fun i : Fin (n+2) => hit r (start i.val) (w i))
  have mem (r : Fin D) (i) : i∈pick r ↔ hit r (start i.val) (w i) := by simp [pick]
  refine ⟨pick,fun i => ?_,fun r => ?_,?_⟩
  · simpa only [mem] using count d (start i.val) (w i) (bound i)
  · have total (k : Nat) : (Finset.range k).sum (fun j => if hit r (start j) (weight j) then 1 else 0) =
        marks r (start k) := by
      induction k with
      | zero => simp [start,formula]
      | succ k ih =>
        have size : weight k≤d+1 := by
          dsimp only [weight]
          split
          · exact bound _
          · omega
        rw [Finset.sum_range_succ,ih,step]
        exact (unit r (start k) (weight k) size).symm
    change (Finset.univ.filter _).card=_
    rw [Finset.card_filter]
    calc
      _ = ∑ i : Fin (n+2), (if hit r (start i.val) (weight i.val) then 1 else 0) :=
        Finset.sum_congr rfl (fun i _ => by rw [actual])
      _ = _ := (Fin.sum_univ_eq_sum_range _ _).trans ((total (n+2)).trans (endEq ▸ formula r T))
  · intro r i j near small
    simp only [mem]
    rcases near with next|⟨last,first,seam⟩
    · rw [next,step,actual]
      exact adjacent r (start i.val) (w i) (w j) small
    · have endAt : start i.val+w i=T := by rw [←actual i,←step,last,endEq]
      have beginAt : start j.val=0 := by simp [first,start]
      have atEnd := adjacent r (start i.val) (w i) (w j) small
      rw [endAt] at atEnd
      rw [beginAt]
      rcases seam with divides|emptyI|emptyJ
      · have translate (a : Nat) : marks r (T+a) = T/D + marks r a := by
          have factor : D*(T/D)=T := by have := Nat.div_add_mod T D; omega
          change (T+a+(d-r.val))/D=_
          rw [show T+a+(d-r.val)=D*(T/D)+(a+(d-r.val)) by rw [factor]; omega,
            Nat.mul_add_div (show 0<D from Nat.succ_pos d)]
          rfl
        have same : hit r T (w j) ↔ hit r 0 (w j) := by
          unfold hit
          have z := translate 0
          simp only [Nat.add_zero] at z
          rw [translate,z]
          simp
        simpa only [same] using atEnd
      · rw [emptyI]
        simp only [hit,Nat.add_zero,lt_self_iff_false,false_and,not_false_eq_true,
          Nat.zero_add,false_or,true_and]
        intro full
        rw [full]
        have here := period r 0
        simp only [Nat.zero_add] at here
        change marks r 0 < marks r (d+1)
        omega
      · rw [emptyJ]
        simp only [hit,Nat.add_zero,lt_self_iff_false,and_false,not_false_eq_true,
          or_false,true_and]
        intro full
        rw [full,period]
        omega

end PEqualNP.CycleRounding
