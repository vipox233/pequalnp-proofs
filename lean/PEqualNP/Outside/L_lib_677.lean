import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_677_aux

open Classical

abbrev W (b : ℕ) : Type := Bool × (Fin b → Bool)
abbrev P (b : ℕ) : Type := Fin b → Option Bool

def supp {b : ℕ} (p : P b) : Finset (Fin b) :=
  Finset.univ.filter (fun i : Fin b => (p i).isSome = true)

def famSet (b r : ℕ) : Finset (P b) :=
  (Finset.univ : Finset (P b)).filter (fun v => (supp v).card = r)

def starFn {b : ℕ} (p : P b) (x : W b) : Bool :=
  decide (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i))

def histOf {b M : ℕ} (ask : Fin M → List Bool → W b) (f : W b → Bool) (seed : Fin M)
    (t : ℕ) : List Bool :=
  (List.range t).foldl (fun (past : List Bool) _ => past ++ [f (ask seed past)]) []

lemma histOf_zero {b M : ℕ} (ask : Fin M → List Bool → W b) (f : W b → Bool) (seed : Fin M) :
    histOf ask f seed 0 = [] := rfl

lemma histOf_succ {b M : ℕ} (ask : Fin M → List Bool → W b) (f : W b → Bool) (seed : Fin M)
    (t : ℕ) :
    histOf ask f seed (t + 1) = histOf ask f seed t ++ [f (ask seed (histOf ask f seed t))] := by
  unfold histOf
  rw [List.range_succ, List.foldl_append]
  rfl

lemma histOf_length {b M : ℕ} (ask : Fin M → List Bool → W b) (f : W b → Bool) (seed : Fin M)
    (t : ℕ) :
    (histOf ask f seed t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [histOf_succ, List.length_append, List.length_singleton, ih]

lemma histOf_take {b M : ℕ} (ask : Fin M → List Bool → W b) (f : W b → Bool) (seed : Fin M) :
    ∀ t s, s ≤ t → (histOf ask f seed t).take s = histOf ask f seed s := by
  intro t
  induction t with
  | zero =>
    intro s hs
    have hs0 : s = 0 := by omega
    subst hs0
    rfl
  | succ t ih =>
    intro s hs
    by_cases hseq : s = t + 1
    · subst hseq
      rw [List.take_of_length_le (by rw [histOf_length])]
    · have hst : s ≤ t := by omega
      rw [histOf_succ, List.take_append_of_le_length (by rw [histOf_length]; exact hst)]
      exact ih s hst

lemma histOf_first_diff {b M : ℕ} (ask : Fin M → List Bool → W b) (f g : W b → Bool)
    (seed : Fin M) :
    ∀ t, histOf ask f seed t ≠ histOf ask g seed t →
      ∃ s < t, histOf ask f seed s = histOf ask g seed s ∧
        f (ask seed (histOf ask g seed s)) ≠ g (ask seed (histOf ask g seed s)) := by
  intro t
  induction t with
  | zero =>
    intro hne
    exact absurd rfl hne
  | succ t ih =>
    intro hne
    by_cases heq : histOf ask f seed t = histOf ask g seed t
    · refine ⟨t, Nat.lt_succ_self t, heq, ?_⟩
      intro hfg
      apply hne
      rw [histOf_succ, histOf_succ, heq, hfg]
    · rcases ih heq with ⟨s, hst, hs_eq, hs_ne⟩
      exact ⟨s, Nat.lt_succ_of_lt hst, hs_eq, hs_ne⟩

lemma fam_card_eq (b r : ℕ) : (famSet b r).card = Nat.choose b r * 2 ^ r := by
  let Sset : Finset (Finset (Fin b)) := Finset.powersetCard r Finset.univ
  have hmaps : ∀ p ∈ famSet b r, supp p ∈ Sset := by
    intro p hp
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (Finset.mem_filter.mp hp).2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfiber : ∀ S ∈ Sset, ((famSet b r).filter (fun p => supp p = S)).card = 2 ^ r := by
    intro S hS
    have hScard : S.card = r := (Finset.mem_powersetCard.mp hS).2
    let fib := (famSet b r).filter (fun p => supp p = S)
    let toFun : {p : P b // p ∈ fib} → (S → Bool) := fun p i => (p.1 i.1).getD false
    have hbij : Function.Bijective toFun := by
      constructor
      · rintro ⟨p1, hp1⟩ ⟨p2, hp2⟩ heq
        apply Subtype.ext
        funext i
        have hs1 : supp p1 = S := (Finset.mem_filter.mp hp1).2
        have hs2 : supp p2 = S := (Finset.mem_filter.mp hp2).2
        by_cases hi : i ∈ S
        · have h1 : (p1 i).isSome = true := by
            have : i ∈ supp p1 := hs1.symm ▸ hi
            exact (Finset.mem_filter.mp this).2
          have h2 : (p2 i).isSome = true := by
            have : i ∈ supp p2 := hs2.symm ▸ hi
            exact (Finset.mem_filter.mp this).2
          have hv : (p1 i).getD false = (p2 i).getD false := congrFun heq ⟨i, hi⟩
          cases hp1i : p1 i <;> cases hp2i : p2 i <;> simp_all
        · have h1 : (p1 i).isSome ≠ true := by
            intro h
            apply hi
            rw [← hs1]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          have h2 : (p2 i).isSome ≠ true := by
            intro h
            apply hi
            rw [← hs2]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          cases hp1i : p1 i <;> cases hp2i : p2 i <;> simp_all
      · intro f
        let p : P b := fun i => if h : i ∈ S then some (f ⟨i, h⟩) else none
        have hsupp : supp p = S := by
          ext i
          simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and, p]
          by_cases h : i ∈ S <;> simp [h]
        have hmem : p ∈ fib := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hsupp⟩
          rw [hsupp, hScard]
        refine ⟨⟨p, hmem⟩, ?_⟩
        funext ⟨i, hi⟩
        simp [toFun, p, hi]
    have hcard := Fintype.card_of_bijective hbij
    rw [Fintype.card_coe, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, hScard] at hcard
    exact hcard
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul]
  have hSset_card : Sset.card = Nat.choose b r := by
    simp [Sset, Finset.card_powersetCard]
  rw [hSset_card]

lemma starFn_injective {b : ℕ} : Function.Injective (starFn (b := b)) := by
  intro p1 p2 heq
  have hdir : ∀ (q1 q2 : P b), starFn q1 = starFn q2 →
      ∀ i c, q1 i = some c → q2 i = some c := by
    intro q1 q2 hq i c hq1i
    cases hq2i : q2 i with
    | none =>
      let w : Fin b → Bool := fun j => if j = i then !c else (q2 j).getD false
      have h2 : starFn q2 (false, w) = true := by
        simp only [starFn, decide_eq_true_eq]
        right
        intro j
        by_cases hji : j = i
        · subst hji; left; exact hq2i
        · cases hq2j : q2 j with
          | none => left; rfl
          | some v => right; simp [w, hji, hq2j]
      have h1 : starFn q1 (false, w) = false := by
        simp only [starFn, decide_eq_false_iff_not, not_or, not_forall]
        refine ⟨Bool.false_ne_true, i, ?_⟩
        simp [hq1i, w]
      rw [hq] at h1
      rw [h1] at h2
      exact absurd h2 Bool.false_ne_true
    | some c' =>
      by_cases hcc : c' = c
      · rw [hcc]
      · let w : Fin b → Bool := fun j => (q1 j).getD false
        have h1 : starFn q1 (false, w) = true := by
          simp only [starFn, decide_eq_true_eq]
          right
          intro j
          cases hq1j : q1 j with
          | none => left; rfl
          | some v => right; simp [w, hq1j]
        have h2 : starFn q2 (false, w) = false := by
          simp only [starFn, decide_eq_false_iff_not, not_or, not_forall]
          refine ⟨Bool.false_ne_true, i, ?_⟩
          simp [hq2i, w, hq1i, hcc]
        rw [hq] at h1
        rw [h1] at h2
        cases h2
  funext i
  cases hp1 : p1 i with
  | none =>
    cases hp2 : p2 i with
    | none => rfl
    | some c =>
      have h1 := hdir p2 p1 heq.symm i c hp2
      rw [hp1] at h1
      cases h1
  | some c =>
    exact (hdir p1 p2 heq i c hp1).symm

lemma starFn_ne_base {b : ℕ} {p : P b} {x : W b} (hne : starFn p x ≠ x.1) :
    x.1 = false ∧ starFn p x = true ∧ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i) := by
  cases hx1 : x.1 with
  | true =>
    exfalso
    apply hne
    simp [starFn, hx1]
  | false =>
    have hst : starFn p x = true := by
      cases hs : starFn p x
      · exact absurd (hs.trans hx1.symm) hne
      · rfl
    refine ⟨rfl, hst, ?_⟩
    have h := of_decide_eq_true (by simpa [starFn] using hst)
    rcases h with htrue | hall
    · rw [hx1] at htrue; cases htrue
    · exact hall

lemma seed_hits_bound {b r M q : ℕ}
    (ask : Fin M → List Bool → W b) (report : Fin M → List Bool → Option (W b → Bool))
    (seed : Fin M) :
    let base : W b → Bool := fun z => z.1
    let output := fun (f : W b → Bool) => report seed (histOf ask f seed q)
    ((famSet b r).filter (fun p => output (starFn p) = some (starFn p))).card ≤
      (if (output base).isSome = true then 1 else 0) +
        ∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j) := by
  intro base output
  set Hit := (famSet b r).filter (fun p => output (starFn p) = some (starFn p))
  let Same := Hit.filter (fun p => histOf ask (starFn p) seed q = histOf ask base seed q)
  let Diff : ℕ → Finset (P b) := fun s =>
    Hit.filter (fun p =>
      histOf ask (starFn p) seed s = histOf ask base seed s ∧
      starFn p (ask seed (histOf ask base seed s)) ≠ base (ask seed (histOf ask base seed s)))
  have hcover : Hit ⊆ Same ∪ (Finset.range q).biUnion Diff := by
    intro p hp
    rw [Finset.mem_union]
    by_cases hsame : histOf ask (starFn p) seed q = histOf ask base seed q
    · left
      exact Finset.mem_filter.mpr ⟨hp, hsame⟩
    · right
      rcases histOf_first_diff ask (starFn p) base seed q hsame with ⟨s, hsq, hseq, hsne⟩
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_range.mpr hsq,
        Finset.mem_filter.mpr ⟨hp, hseq, hsne⟩⟩
  have hSame_le : Same.card ≤ if (output base).isSome = true then 1 else 0 := by
    by_cases hne : Same.Nonempty
    · rcases hne with ⟨p0, hp0⟩
      have hp0_hit := (Finset.mem_filter.mp hp0).1
      have hp0_eq := (Finset.mem_filter.mp hp0).2
      have hbase_out : output base = some (starFn p0) := by
        have h1 : output (starFn p0) = some (starFn p0) := (Finset.mem_filter.mp hp0_hit).2
        dsimp only [output] at h1 ⊢
        rw [← hp0_eq]
        exact h1
      have hisSome : (output base).isSome = true := by simp [hbase_out]
      simp only [hisSome, ↓reduceIte]
      refine Finset.card_le_one.mpr ?_
      intro p1 hp1 p2 hp2
      have h1_hit := (Finset.mem_filter.mp hp1).1
      have h1_eq := (Finset.mem_filter.mp hp1).2
      have h2_hit := (Finset.mem_filter.mp hp2).1
      have h2_eq := (Finset.mem_filter.mp hp2).2
      have ho1 : output (starFn p1) = some (starFn p1) := (Finset.mem_filter.mp h1_hit).2
      have ho2 : output (starFn p2) = some (starFn p2) := (Finset.mem_filter.mp h2_hit).2
      have hsame_out : some (starFn p1) = some (starFn p2) := by
        dsimp only [output] at ho1 ho2
        rw [← ho1, h1_eq, ← h2_eq, ho2]
      exact starFn_injective (Option.some.inj hsame_out)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hDiff_le_N : ∀ s < q, (Diff s).card ≤ Nat.choose b r := by
    intro s _
    set x := ask seed (histOf ask base seed s)
    let Sset : Finset (Finset (Fin b)) := Finset.powersetCard r Finset.univ
    have hcard_S : Sset.card = Nat.choose b r := by simp [Sset, Finset.card_powersetCard]
    rw [← hcard_S]
    refine Finset.card_le_card_of_injOn supp ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe] at hp ⊢
      have hpfam : p ∈ famSet b r := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (Finset.mem_filter.mp hpfam).2⟩
    · intro p1 hp1 p2 hp2 hseq
      simp only [Finset.mem_coe] at hp1 hp2
      have hne1 := (Finset.mem_filter.mp hp1).2.2
      have hne2 := (Finset.mem_filter.mp hp2).2.2
      have hall1 := (starFn_ne_base hne1).2.2
      have hall2 := (starFn_ne_base hne2).2.2
      funext i
      by_cases hi : i ∈ supp p1
      · have hi2 : i ∈ supp p2 := hseq ▸ hi
        have hs1 : (p1 i).isSome = true := (Finset.mem_filter.mp hi).2
        have hs2 : (p2 i).isSome = true := (Finset.mem_filter.mp hi2).2
        have h1 : p1 i = some (x.2 i) := by
          rcases hall1 i with hnone | hsome
          · rw [hnone] at hs1; simp at hs1
          · exact hsome
        have h2 : p2 i = some (x.2 i) := by
          rcases hall2 i with hnone | hsome
          · rw [hnone] at hs2; simp at hs2
          · exact hsome
        rw [h1, h2]
      · have hi2 : i ∉ supp p2 := hseq ▸ hi
        have h1 : p1 i = none := by
          cases hp1i : p1 i with
          | none => rfl
          | some v =>
            exfalso
            apply hi
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hp1i]⟩
        have h2 : p2 i = none := by
          cases hp2i : p2 i with
          | none => rfl
          | some v =>
            exfalso
            apply hi2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hp2i]⟩
        rw [h1, h2]
  have hDiff_le_pow : ∀ s < q, (Diff s).card ≤ 2 ^ (q - 1 - s) := by
    intro s hsq
    set j := q - 1 - s
    let tailFn : P b → (Fin j → Bool) := fun p i =>
      (histOf ask (starFn p) seed q).getD (s + 1 + i.val) false
    have hcard_fun : (Finset.univ : Finset (Fin j → Bool)).card = 2 ^ j := by
      simp
    rw [← hcard_fun]
    refine Finset.card_le_card_of_injOn tailFn (fun _ _ => Finset.mem_univ _) ?_
    intro p1 hp1 p2 hp2 hteq
    simp only [Finset.mem_coe] at hp1 hp2
    have h1_hit := (Finset.mem_filter.mp hp1).1
    have h1_eq := (Finset.mem_filter.mp hp1).2.1
    have h1_ne := (Finset.mem_filter.mp hp1).2.2
    have h2_hit := (Finset.mem_filter.mp hp2).1
    have h2_eq := (Finset.mem_filter.mp hp2).2.1
    have h2_ne := (Finset.mem_filter.mp hp2).2.2
    have hst1 : starFn p1 (ask seed (histOf ask base seed s)) = true := (starFn_ne_base h1_ne).2.1
    have hst2 : starFn p2 (ask seed (histOf ask base seed s)) = true := (starFn_ne_base h2_ne).2.1
    have htake1 : (histOf ask (starFn p1) seed q).take (s + 1) =
        histOf ask base seed s ++ [true] := by
      rw [histOf_take ask (starFn p1) seed q (s + 1) (by omega), histOf_succ, h1_eq, hst1]
    have htake2 : (histOf ask (starFn p2) seed q).take (s + 1) =
        histOf ask base seed s ++ [true] := by
      rw [histOf_take ask (starFn p2) seed q (s + 1) (by omega), histOf_succ, h2_eq, hst2]
    have hhist_eq : histOf ask (starFn p1) seed q = histOf ask (starFn p2) seed q := by
      apply List.ext_getElem
      · rw [histOf_length, histOf_length]
      · intro idx hi1 hi2
        by_cases hlt : idx < s + 1
        · have ht_eq : (histOf ask (starFn p1) seed q).take (s + 1) =
              (histOf ask (starFn p2) seed q).take (s + 1) := by rw [htake1, htake2]
          have hg1 : ((histOf ask (starFn p1) seed q).take (s + 1))[idx]'(by
              rw [List.length_take, histOf_length]; omega) =
              (histOf ask (starFn p1) seed q)[idx]'hi1 := List.getElem_take
          have hg2 : ((histOf ask (starFn p2) seed q).take (s + 1))[idx]'(by
              rw [List.length_take, histOf_length]; omega) =
              (histOf ask (starFn p2) seed q)[idx]'hi2 := List.getElem_take
          rw [← hg1, ← hg2]
          congr 1
        · have hidx_lt : idx - (s + 1) < j := by
            rw [histOf_length] at hi1
            omega
          have hget := congrFun hteq ⟨idx - (s + 1), hidx_lt⟩
          simp only [tailFn] at hget
          have hadd : s + 1 + (idx - (s + 1)) = idx := by omega
          rw [hadd, List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2] at hget
          exact hget
    have ho1 : output (starFn p1) = some (starFn p1) := (Finset.mem_filter.mp h1_hit).2
    have ho2 : output (starFn p2) = some (starFn p2) := (Finset.mem_filter.mp h2_hit).2
    have hsame_out : some (starFn p1) = some (starFn p2) := by
      dsimp only [output] at ho1 ho2
      rw [← ho1, hhist_eq, ho2]
    exact starFn_injective (Option.some.inj hsame_out)
  have hDiff_le : ∀ s ∈ Finset.range q, (Diff s).card ≤ min (Nat.choose b r) (2 ^ (q - 1 - s)) := by
    intro s hs
    have hsq : s < q := Finset.mem_range.mp hs
    exact le_min (hDiff_le_N s hsq) (hDiff_le_pow s hsq)
  have hreflect : (∑ s ∈ Finset.range q, min (Nat.choose b r) (2 ^ (q - 1 - s))) =
      ∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j) :=
    Finset.sum_range_reflect (fun j => min (Nat.choose b r) (2 ^ j)) q
  calc Hit.card
      ≤ (Same ∪ (Finset.range q).biUnion Diff).card := Finset.card_le_card hcover
    _ ≤ Same.card + ((Finset.range q).biUnion Diff).card := Finset.card_union_le _ _
    _ ≤ Same.card + ∑ s ∈ Finset.range q, (Diff s).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (if (output base).isSome = true then 1 else 0) +
          ∑ s ∈ Finset.range q, min (Nat.choose b r) (2 ^ (q - 1 - s)) :=
        Nat.add_le_add hSame_le (Finset.sum_le_sum hDiff_le)
    _ = (if (output base).isSome = true then 1 else 0) +
          ∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j) := by
        rw [hreflect]

lemma hits_bound {b r M q : ℕ}
    (ask : Fin M → List Bool → W b) (report : Fin M → List Bool → Option (W b → Bool)) :
    (∑ p ∈ famSet b r, (Finset.univ.filter (fun t : Fin M =>
      report t (histOf ask (starFn p) t q) = some (starFn p))).card) ≤
    (Finset.univ.filter (fun u : Fin M =>
      (report u (histOf ask (fun z : W b => z.1) u q)).isSome = true)).card +
    M * (∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j)) := by
  let output := fun (f : W b → Bool) (seed : Fin M) => report seed (histOf ask f seed q)
  let hits := ∑ p ∈ famSet b r, (Finset.univ.filter (fun t : Fin M =>
    output (starFn p) t = some (starFn p))).card
  let guesses := (Finset.univ.filter (fun u : Fin M =>
    (output (fun z : W b => z.1) u).isSome = true)).card
  change hits ≤ guesses + M * (∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j))
  have hswap : hits = ∑ seed : Fin M,
      ((famSet b r).filter (fun p => output (starFn p) seed = some (starFn p))).card := by
    simp only [hits, Finset.card_filter]
    rw [Finset.sum_comm]
  have hguess : guesses = ∑ seed : Fin M,
      if (output (fun z : W b => z.1) seed).isSome = true then 1 else 0 := by
    simp only [guesses, Finset.card_filter]
  have hmul : M * (∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j)) =
      ∑ _seed : Fin M, ∑ j ∈ Finset.range q, min (Nat.choose b r) (2 ^ j) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [hswap, hguess, hmul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro seed _
  exact seed_hits_bound ask report seed

lemma sum_two_pow (m : ℕ) : 1 + ∑ j ∈ Finset.range m, 2 ^ j = 2 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← Nat.add_assoc, ih, Nat.pow_succ, Nat.mul_two]

lemma part3_arith {r N M q hits guesses : ℕ}
    (hr : 0 < r) (hN : 0 < N) (hM : 0 < M)
    (hguesses : guesses ≤ M)
    (hhits : hits ≤ guesses + M * ∑ j ∈ Finset.range q, min N (2 ^ j))
    (hlow : 3 * M * (N * 2 ^ r) ≤ 4 * hits) :
    3 * 2 ^ r + 4 * Nat.clog 2 N ≤ 4 * (q + 2) := by
  set S := ∑ j ∈ Finset.range q, min N (2 ^ j)
  set L := Nat.clog 2 N
  have h4hits : 4 * hits ≤ M * (4 * (1 + S)) := by
    have h1 : hits ≤ M * (1 + S) := by
      have : guesses + M * S ≤ M + M * S := Nat.add_le_add_right hguesses _
      have : M + M * S = M * (1 + S) := by ring
      omega
    have h2 : 4 * hits ≤ 4 * (M * (1 + S)) := Nat.mul_le_mul_left 4 h1
    have h3 : 4 * (M * (1 + S)) = M * (4 * (1 + S)) := by ring
    omega
  have hlow' : M * (3 * N * 2 ^ r) ≤ M * (4 * (1 + S)) := by
    have heq : M * (3 * N * 2 ^ r) = 3 * M * (N * 2 ^ r) := by ring
    omega
  have hcancelM : 3 * N * 2 ^ r ≤ 4 * (1 + S) :=
    Nat.le_of_mul_le_mul_left hlow' hM
  have h2r : 2 ≤ 2 ^ r := by
    calc 2 = 2 ^ 1 := by decide
      _ ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) hr
  have h6N : 6 * N ≤ 4 * (1 + S) := by
    have : 3 * N * 2 ≤ 3 * N * 2 ^ r := Nat.mul_le_mul_left (3 * N) h2r
    omega
  have hLq : L ≤ q := by
    by_contra hgt
    have hqL : q < L := by omega
    have hpow_lt : 2 ^ q < N := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hqL
    have hS_le : 1 + S ≤ 2 ^ q := by
      have h1 : S ≤ ∑ j ∈ Finset.range q, 2 ^ j :=
        Finset.sum_le_sum (fun j _ => Nat.min_le_right _ _)
      have h2 := sum_two_pow q
      omega
    omega
  have hpowL_le : 2 ^ L ≤ 2 * N := by
    cases hL : L with
    | zero =>
      simp only [Nat.pow_zero]
      omega
    | succ L' =>
      have hlt : L' < Nat.clog 2 N := by omega
      have hp : 2 ^ L' < N := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp hlt
      rw [Nat.pow_succ]
      omega
  have hS_split : S = (∑ j ∈ Finset.range L, min N (2 ^ j)) +
      (∑ j ∈ Finset.range (q - L), min N (2 ^ (L + j))) := by
    have hqeq : q = L + (q - L) := by omega
    conv_lhs => rw [show S = ∑ j ∈ Finset.range (L + (q - L)), min N (2 ^ j) by rw [← hqeq]]
    exact Finset.sum_range_add (fun j => min N (2 ^ j)) L (q - L)
  have hpart1 : 1 + ∑ j ∈ Finset.range L, min N (2 ^ j) ≤ 2 * N := by
    have h1 : ∑ j ∈ Finset.range L, min N (2 ^ j) ≤ ∑ j ∈ Finset.range L, 2 ^ j :=
      Finset.sum_le_sum (fun j _ => Nat.min_le_right _ _)
    have h2 := sum_two_pow L
    omega
  have hpart2 : ∑ j ∈ Finset.range (q - L), min N (2 ^ (L + j)) ≤ (q - L) * N := by
    calc ∑ j ∈ Finset.range (q - L), min N (2 ^ (L + j))
        ≤ ∑ _j ∈ Finset.range (q - L), N := Finset.sum_le_sum (fun j _ => Nat.min_le_left _ _)
      _ = (q - L) * N := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h1S : 1 + S ≤ (q + 2 - L) * N := by
    have hrew : 2 * N + (q - L) * N = (q + 2 - L) * N := by
      have : 2 + (q - L) = q + 2 - L := by omega
      rw [← this, Nat.add_mul]
    omega
  have hmulN : N * (3 * 2 ^ r) ≤ N * (4 * (q + 2 - L)) := by
    have h1 : N * (3 * 2 ^ r) = 3 * N * 2 ^ r := by ring
    have h2 : N * (4 * (q + 2 - L)) = 4 * ((q + 2 - L) * N) := by ring
    omega
  have hcancelN : 3 * 2 ^ r ≤ 4 * (q + 2 - L) :=
    Nat.le_of_mul_le_mul_left hmulN hN
  omega

theorem main :
    (∀ (b r : ℕ), 0 < r → r ≤ b →
      let W := Bool × (Fin b → Bool)
      let P := Fin b → Option Bool
      let fam := (Finset.univ : Finset P).filter (fun v =>
        (Finset.univ.filter (fun i : Fin b => (v i).isSome = true)).card = r)
      let star := fun (p : P) (x : W) => decide
        (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i))
      let N := Nat.choose b r
      ∀ (M q : ℕ), 0 < M →
        ∀ (ask : Fin M → List Bool → W) (report : Fin M → List Bool → Option (W → Bool)),
          let output := fun (f : W → Bool) (seed : Fin M) =>
            let history := (List.range q).foldl (fun (past : List Bool) _ =>
              past ++ [f (ask seed past)]) []
            report seed history
          let hits := ∑ p ∈ fam, (Finset.univ.filter (fun t : Fin M =>
            output (star p) t = some (star p))).card
          let guesses := (Finset.univ.filter (fun u : Fin M =>
            (output (fun z : W => z.1) u).isSome = true)).card
          fam.card = N * 2 ^ r ∧
          hits ≤ guesses + M * (∑ j ∈ Finset.range q, min N (2 ^ j)) ∧
          (3 * M * fam.card ≤ 4 * hits →
            3 * 2 ^ r + 4 * Nat.clog 2 N ≤ 4 * (q + 2))) := by
  intro b r hr hrb
  dsimp only
  intro M q hM ask report
  have h1 : (famSet b r).card = Nat.choose b r * 2 ^ r := fam_card_eq b r
  have h2 := hits_bound (b := b) (r := r) (M := M) (q := q) ask report
  refine ⟨h1, h2, ?_⟩
  intro hlow
  have hlow' : 3 * M * (Nat.choose b r * 2 ^ r) ≤
      4 * ∑ p ∈ famSet b r, (Finset.univ.filter (fun t : Fin M =>
        report t (histOf ask (starFn p) t q) = some (starFn p))).card := by
    rw [← h1]
    exact hlow
  have hguesses : (Finset.univ.filter (fun u : Fin M =>
      (report u (histOf ask (fun z : W b => z.1) u q)).isSome = true)).card ≤ M := by
    calc _ ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_filter_le _ _
      _ = M := Fintype.card_fin M
  exact part3_arith hr (Nat.choose_pos hrb) hM hguesses h2 hlow'

end PEqualNP.Outside.L_lib_677_aux

theorem PEqualNP.Outside.L_lib_677 : (∀ (b r : ℕ), 0 < r → r ≤ b →
  let W := Bool × (Fin b → Bool)
  let P := Fin b → Option Bool
  let fam := (Finset.univ : Finset P).filter (fun v =>
    (Finset.univ.filter (fun i : Fin b => (v i).isSome = true)).card = r)
  let star := fun (p : P) (x : W) => decide
    (x.1 = true ∨ ∀ i : Fin b, p i = none ∨ p i = some (x.2 i))
  let N := Nat.choose b r
  ∀ (M q : ℕ), 0 < M →
    ∀ (ask : Fin M → List Bool → W) (report : Fin M → List Bool → Option (W → Bool)),
      let output := fun (f : W → Bool) (seed : Fin M) =>
        let history := (List.range q).foldl (fun (past : List Bool) _ =>
          past ++ [f (ask seed past)]) []
        report seed history
      let hits := ∑ p ∈ fam, (Finset.univ.filter (fun t : Fin M =>
        output (star p) t = some (star p))).card
      let guesses := (Finset.univ.filter (fun u : Fin M =>
        (output (fun z : W => z.1) u).isSome = true)).card
      fam.card = N * 2 ^ r ∧
      hits ≤ guesses + M * (∑ j ∈ Finset.range q, min N (2 ^ j)) ∧
      (3 * M * fam.card ≤ 4 * hits →
        3 * 2 ^ r + 4 * Nat.clog 2 N ≤ 4 * (q + 2))) := by
  exact PEqualNP.Outside.L_lib_677_aux.main
