import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic

namespace PEqualNP.Outside.L_lib_583

private def toZ2 (b : Bool) : ZMod 2 :=
  if b then 1 else 0

private lemma toZ2_injective : Function.Injective toZ2 := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : b = a := by
  calc
    b = 0 + b := (zero_add b).symm
    _ = (a + a) + b := by rw [zmod2_add_self]
    _ = a + (a + b) := add_assoc a a b
    _ = a + 0 := by rw [h]
    _ = a := add_zero a

private lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl
  · exact absurd rfl hx
  · rfl

private lemma toZ2_decide_eq_one (x : ZMod 2) : toZ2 (decide (x = 1)) = x := by
  rcases zmod2_eq_zero_or_one x with rfl | rfl <;> decide

private lemma toZ2_decide_eq_bool (b c : Bool) :
    toZ2 (decide (b = c)) = if c then toZ2 b else 1 + toZ2 b := by
  cases b <;> cases c <;> decide

private lemma toZ2_par (n : Nat) : toZ2 (n % 2 == 1) = (n : ZMod 2) := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hcast : (n : ZMod 2) = ((n % 2 : Nat) : ZMod 2) := by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    simp [Nat.cast_add, Nat.cast_mul, h2]
  rw [hcast]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, toZ2]

private def evalMon {V : Type*} [Fintype V] (mon : Finset V) (word : V → Bool) : ZMod 2 :=
  if ∀ j ∈ mon, word j = true then 1 else 0

private lemma evalMon_eq_one {V : Type*} [Fintype V] {mon : Finset V} {word : V → Bool}
    (h : ∀ j ∈ mon, word j = true) : evalMon mon word = 1 :=
  ite_eq_left_iff.mpr fun hn => absurd h hn

private lemma evalMon_eq_zero {V : Type*} [Fintype V] {mon : Finset V} {word : V → Bool}
    (h : ¬ ∀ j ∈ mon, word j = true) : evalMon mon word = 0 :=
  ite_eq_right_iff.mpr fun hp => absurd hp h

private lemma evalMon_empty {V : Type*} [Fintype V] (word : V → Bool) :
    evalMon (∅ : Finset V) word = 1 := by
  simp [evalMon]

private lemma evalMon_union {V : Type*} [Fintype V] [DecidableEq V] (a b : Finset V)
    (word : V → Bool) :
    evalMon (a ∪ b) word = evalMon a word * evalMon b word := by
  by_cases ha : ∀ j ∈ a, word j = true
  · by_cases hb : ∀ j ∈ b, word j = true
    · have hab : ∀ j ∈ a ∪ b, word j = true := fun j hj => by
        rcases Finset.mem_union.mp hj with hja | hjb
        · exact ha j hja
        · exact hb j hjb
      rw [evalMon_eq_one hab, evalMon_eq_one ha, evalMon_eq_one hb, one_mul]
    · have hab : ¬ ∀ j ∈ a ∪ b, word j = true :=
        fun h => hb fun j hj => h j (Finset.mem_union_right a hj)
      rw [evalMon_eq_zero hab, evalMon_eq_one ha, evalMon_eq_zero hb, mul_zero]
  · have hab : ¬ ∀ j ∈ a ∪ b, word j = true :=
      fun h => ha fun j hj => h j (Finset.mem_union_left b hj)
    rw [evalMon_eq_zero hab, evalMon_eq_zero ha, zero_mul]

private lemma sum_evalMon {V : Type*} [Fintype V] (terms : Finset (Finset V)) (word : V → Bool)
    (inst : DecidablePred (fun mon : Finset V => ∀ j ∈ mon, word j = true)) :
    (∑ mon ∈ terms, evalMon mon word) =
      ((@Finset.filter _ (fun mon => ∀ j ∈ mon, word j = true) inst terms).card : ZMod 2) := by
  have hcongr : (∑ mon ∈ terms, evalMon mon word)
      = ∑ mon ∈ terms, @ite (ZMod 2) (∀ j ∈ mon, word j = true) (inst mon) 1 0 := by
    refine Finset.sum_congr rfl fun mon _ => ?_
    by_cases h : ∀ j ∈ mon, word j = true
    · rw [evalMon_eq_one h, ite_eq_left_iff.mpr fun hn => absurd h hn]
    · rw [evalMon_eq_zero h, ite_eq_right_iff.mpr fun hp => absurd hp h]
  rw [hcongr, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, mul_one]

private def degCoeff {V : Type*} [Fintype V] (u : Nat) (F : (V → Bool) → ZMod 2) : Prop :=
  ∃ c : Finset V → ZMod 2, (∀ mon, c mon ≠ 0 → mon.card ≤ u) ∧
    ∀ word, F word = ∑ mon : Finset V, c mon * evalMon mon word

private lemma degCoeff_mono {V : Type*} [Fintype V] {u v : Nat} (huv : u ≤ v)
    {F : (V → Bool) → ZMod 2} (hF : degCoeff u F) : degCoeff v F := by
  rcases hF with ⟨c, hcdeg, hceval⟩
  exact ⟨c, fun mon hne => le_trans (hcdeg mon hne) huv, hceval⟩

private lemma degCoeff_zero {V : Type*} [Fintype V] (u : Nat) :
    degCoeff u (fun _ : V → Bool => (0 : ZMod 2)) :=
  ⟨fun _ => 0, fun _ h => absurd rfl h, fun _ => by simp⟩

private lemma degCoeff_one {V : Type*} [Fintype V] [DecidableEq V] (u : Nat) :
    degCoeff u (fun _ : V → Bool => (1 : ZMod 2)) := by
  refine ⟨fun mon => if mon = ∅ then 1 else 0, ?_, ?_⟩
  · intro mon hne
    have hm : mon = ∅ := by
      by_contra h
      simp [h] at hne
    subst hm
    exact Nat.zero_le u
  · intro word
    simp [evalMon_empty]

private lemma degCoeff_mon {V : Type*} [Fintype V] [DecidableEq V] (mon : Finset V) :
    degCoeff mon.card (evalMon mon) := by
  refine ⟨fun a => if a = mon then 1 else 0, ?_, ?_⟩
  · intro a hne
    have ha : a = mon := by
      by_contra h
      simp [h] at hne
    subst ha
    exact le_rfl
  · intro word
    simp

private lemma degCoeff_add {V : Type*} [Fintype V] {u : Nat}
    {F G : (V → Bool) → ZMod 2} (hF : degCoeff u F) (hG : degCoeff u G) :
    degCoeff u (fun word => F word + G word) := by
  rcases hF with ⟨c₁, h₁deg, h₁eval⟩
  rcases hG with ⟨c₂, h₂deg, h₂eval⟩
  refine ⟨fun mon => c₁ mon + c₂ mon, ?_, ?_⟩
  · intro mon hne
    by_cases h1 : c₁ mon = 0
    · have h2 : c₂ mon ≠ 0 := fun h2 => hne (by simp [h1, h2])
      exact h₂deg mon h2
    · exact h₁deg mon h1
  · intro word
    dsimp only
    rw [h₁eval word, h₂eval word, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun mon _ => (add_mul _ _ _).symm

private lemma degCoeff_mul {V : Type*} [Fintype V] [DecidableEq V] {u v : Nat}
    {F G : (V → Bool) → ZMod 2} (hF : degCoeff u F) (hG : degCoeff v G) :
    degCoeff (u + v) (fun word => F word * G word) := by
  rcases hF with ⟨c₁, h₁deg, h₁eval⟩
  rcases hG with ⟨c₂, h₂deg, h₂eval⟩
  refine ⟨fun mon => ∑ a : Finset V, ∑ b : Finset V,
      if a ∪ b = mon then c₁ a * c₂ b else 0, ?_, ?_⟩
  · intro mon hne
    rcases Finset.exists_ne_zero_of_sum_ne_zero hne with ⟨a, _, ha⟩
    rcases Finset.exists_ne_zero_of_sum_ne_zero ha with ⟨b, _, hab⟩
    have hunion : a ∪ b = mon := by
      by_contra h
      simp [h] at hab
    have hmul : c₁ a * c₂ b ≠ 0 := by
      simpa [hunion] using hab
    have hca : c₁ a ≠ 0 := left_ne_zero_of_mul hmul
    have hcb : c₂ b ≠ 0 := right_ne_zero_of_mul hmul
    rw [← hunion]
    exact le_trans (Finset.card_union_le a b) (Nat.add_le_add (h₁deg a hca) (h₂deg b hcb))
  · intro word
    dsimp only
    calc
      F word * G word
          = (∑ a : Finset V, c₁ a * evalMon a word) *
              (∑ b : Finset V, c₂ b * evalMon b word) := by
            rw [h₁eval word, h₂eval word]
      _ = ∑ a : Finset V, ∑ b : Finset V,
            (c₁ a * evalMon a word) * (c₂ b * evalMon b word) := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
      _ = ∑ a : Finset V, ∑ b : Finset V,
            (c₁ a * c₂ b) * evalMon (a ∪ b) word := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [evalMon_union, mul_mul_mul_comm]
      _ = ∑ a : Finset V, ∑ b : Finset V, ∑ mon : Finset V,
            (if a ∪ b = mon then c₁ a * c₂ b else 0) * evalMon mon word := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      _ = ∑ a : Finset V, ∑ mon : Finset V, ∑ b : Finset V,
            (if a ∪ b = mon then c₁ a * c₂ b else 0) * evalMon mon word := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ mon : Finset V, ∑ a : Finset V, ∑ b : Finset V,
            (if a ∪ b = mon then c₁ a * c₂ b else 0) * evalMon mon word :=
            Finset.sum_comm
      _ = ∑ mon : Finset V,
            (∑ a : Finset V, ∑ b : Finset V, if a ∪ b = mon then c₁ a * c₂ b else 0) *
              evalMon mon word := by
            refine Finset.sum_congr rfl fun mon _ => ?_
            simp only [Finset.sum_mul]

private lemma degCoeff_sum {V α : Type*} [Fintype V] [DecidableEq α]
    (s : Finset α) (u : Nat) (F : α → (V → Bool) → ZMod 2)
    (h : ∀ i ∈ s, degCoeff u (F i)) :
    degCoeff u (fun word => ∑ i ∈ s, F i word) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using degCoeff_zero (V := V) u
  | @insert a s ha ih =>
    have ha' : degCoeff u (F a) := h a (Finset.mem_insert_self a s)
    have hs' : degCoeff u (fun word => ∑ i ∈ s, F i word) :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hadd := degCoeff_add ha' hs'
    simpa [Finset.sum_insert ha] using hadd

private lemma degCoeff_prod {V α : Type*} [Fintype V] [DecidableEq V] [DecidableEq α]
    (s : Finset α) (d : α → Nat) (F : α → (V → Bool) → ZMod 2)
    (h : ∀ i ∈ s, degCoeff (d i) (F i)) :
    degCoeff (∑ i ∈ s, d i) (fun word => ∏ i ∈ s, F i word) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa using degCoeff_one (V := V) 0
  | @insert a s ha ih =>
    have ha' : degCoeff (d a) (F a) := h a (Finset.mem_insert_self a s)
    have hs' : degCoeff (∑ i ∈ s, d i) (fun word => ∏ i ∈ s, F i word) :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hmul := degCoeff_mul ha' hs'
    simpa [Finset.prod_insert ha, Finset.sum_insert ha] using hmul

private lemma degCoeff_of_par {V : Type*} [Fintype V] [DecidableEq V]
    {u : Nat} {f : (V → Bool) → Bool}
    (hf : ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1)) :
    degCoeff u (fun word => toZ2 (f word)) := by
  rcases hf with ⟨terms, hcard, heval⟩
  refine ⟨fun mon => if mon ∈ terms then 1 else 0, ?_, ?_⟩
  · intro mon hne
    have hm : mon ∈ terms := by
      by_contra h
      simp [h] at hne
    exact hcard mon hm
  · intro word
    dsimp only
    rw [heval word, toZ2_par]
    have hsum1 : ∑ mon : Finset V, (if mon ∈ terms then (1 : ZMod 2) else 0) * evalMon mon word
        = ∑ mon ∈ terms, evalMon mon word := by
      simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
      have hfilt : (Finset.univ : Finset (Finset V)).filter (fun mon => mon ∈ terms) = terms := by
        ext mon
        simp
      rw [hfilt]
    rw [hsum1]
    exact (sum_evalMon terms word _).symm

private lemma par_of_degCoeff {V : Type*} [Fintype V] [DecidableEq V]
    {u : Nat} {F : (V → Bool) → ZMod 2} (hF : degCoeff u F) :
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, decide (F word = 1) =
        ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1) := by
  rcases hF with ⟨c, hcdeg, hceval⟩
  let terms : Finset (Finset V) :=
    (Finset.univ : Finset (Finset V)).filter (fun mon => c mon ≠ 0)
  refine ⟨terms, ?_, ?_⟩
  · intro mon hm
    exact hcdeg mon (Finset.mem_filter.mp hm).2
  · intro word
    apply toZ2_injective
    rw [toZ2_decide_eq_one, toZ2_par, hceval word]
    have h1 : ∑ mon : Finset V, c mon * evalMon mon word
        = ∑ mon ∈ terms, c mon * evalMon mon word := by
      symm
      refine Finset.sum_subset (Finset.subset_univ terms) ?_
      intro mon _ hnot
      have hc0 : c mon = 0 := by
        by_contra hne
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ mon, hne⟩)
      simp [hc0]
    have h2 : ∑ mon ∈ terms, c mon * evalMon mon word = ∑ mon ∈ terms, evalMon mon word := by
      refine Finset.sum_congr rfl fun mon hm => ?_
      rw [zmod2_eq_one_of_ne_zero (Finset.mem_filter.mp hm).2, one_mul]
    rw [h1, h2]
    exact sum_evalMon terms word _

private def runFn {W : Type*} (steps : Nat) (ask : Nat → Nat → W → Bool) (x : W) : Nat :=
  (List.range steps).foldl (fun past pos => past + ((ask pos past x).toNat <<< pos)) 0

private lemma runFn_succ {W : Type*} (k : Nat) (ask : Nat → Nat → W → Bool) (x : W) :
    runFn (k + 1) ask x = runFn k ask x + ((ask k (runFn k ask x) x).toNat <<< k) := by
  simp [runFn, List.range_succ]

private lemma runFn_lt {W : Type*} (k : Nat) (ask : Nat → Nat → W → Bool) (x : W) :
    runFn k ask x < 2 ^ k := by
  induction k with
  | zero =>
    simp [runFn]
  | succ k ih =>
    rw [runFn_succ, Nat.shiftLeft_eq]
    cases ask k (runFn k ask x) x
    · simp only [Bool.toNat_false, zero_mul, add_zero]
      exact lt_trans ih (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self k))
    · simp only [Bool.toNat_true, one_mul]
      rw [Nat.pow_succ, Nat.mul_two]
      exact Nat.add_lt_add_right ih (2 ^ k)

private lemma runFn_succ_eq_iff {W : Type*} (k : Nat) (ask : Nat → Nat → W → Bool) (x : W)
    {p : Nat} (hp : p < 2 ^ (k + 1)) :
    runFn (k + 1) ask x = p ↔
      runFn k ask x = p % 2 ^ k ∧ ask k (p % 2 ^ k) x = decide (p / 2 ^ k = 1) := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hlt : runFn k ask x < 2 ^ k := runFn_lt k ask x
  rw [runFn_succ, Nat.shiftLeft_eq]
  constructor
  · intro heq
    have hmod : p % 2 ^ k = runFn k ask x := by
      rw [← heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt]
    have hdiv : p / 2 ^ k = (ask k (runFn k ask x) x).toNat := by
      rw [← heq, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, zero_add]
    refine ⟨hmod.symm, ?_⟩
    rw [hmod, hdiv]
    cases ask k (runFn k ask x) x <;> rfl
  · rintro ⟨h1, h2⟩
    have hdivlt : p / 2 ^ k < 2 := by
      apply Nat.div_lt_of_lt_mul
      simpa [Nat.pow_succ, Nat.mul_comm] using hp
    have htoNat : (decide (p / 2 ^ k = 1)).toNat = p / 2 ^ k := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hdivlt with h0 | h1'
      · have hz : p / 2 ^ k = 0 := Nat.lt_one_iff.mp h0
        simp [hz]
      · simp [h1']
    rw [h1, h2, htoNat, Nat.mul_comm, Nat.mod_add_div]

private lemma degCoeff_leaf_ind {V : Type*} [Fintype V] [DecidableEq V]
    {d : Nat} (budget : Fin d → Nat) (ask : Nat → Nat → (V → Bool) → Bool)
    (hask : ∀ (u : Fin d) (path : Nat), degCoeff (budget u) (fun x => toZ2 (ask u.val path x))) :
    ∀ (k : Nat) (hk : k ≤ d) (p : Nat), p < 2 ^ k →
      degCoeff (∑ j : Fin k, budget ⟨j.val, lt_of_lt_of_le j.isLt hk⟩)
        (fun x => if runFn k ask x = p then (1 : ZMod 2) else 0) := by
  intro k
  induction k with
  | zero =>
    intro hk p hp
    have hp0 : p = 0 := Nat.lt_one_iff.mp hp
    subst hp0
    simpa [runFn] using degCoeff_one (V := V) 0
  | succ k ih =>
    intro hk p hp
    have hk' : k ≤ d := Nat.le_of_succ_le hk
    have hprev := ih hk' (p % 2 ^ k) (Nat.mod_lt p (Nat.two_pow_pos k))
    have hbit_raw : degCoeff (budget ⟨k, hk⟩) (fun x => toZ2 (ask k (p % 2 ^ k) x)) :=
      hask ⟨k, hk⟩ (p % 2 ^ k)
    have hbit : degCoeff (budget ⟨k, hk⟩)
        (fun x => if ask k (p % 2 ^ k) x = decide (p / 2 ^ k = 1) then (1 : ZMod 2) else 0) := by
      have heq : (fun x => if ask k (p % 2 ^ k) x = decide (p / 2 ^ k = 1) then (1 : ZMod 2) else 0)
          = (fun x => if decide (p / 2 ^ k = 1) then toZ2 (ask k (p % 2 ^ k) x)
              else 1 + toZ2 (ask k (p % 2 ^ k) x)) := by
        funext x
        rw [← toZ2_decide_eq_bool]
        simp [toZ2]
      rw [heq]
      cases decide (p / 2 ^ k = 1)
      · simpa using degCoeff_add (degCoeff_one (V := V) (budget ⟨k, hk⟩)) hbit_raw
      · simpa using hbit_raw
    have hmul := degCoeff_mul hprev hbit
    have hsum : (∑ j : Fin k, budget ⟨j.val, lt_of_lt_of_le j.isLt hk'⟩) + budget ⟨k, hk⟩
        = ∑ j : Fin (k + 1), budget ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ := by
      rw [Fin.sum_univ_castSucc]
      rfl
    rw [hsum] at hmul
    have hfun : (fun x =>
        (if runFn k ask x = p % 2 ^ k then (1 : ZMod 2) else 0) *
          (if ask k (p % 2 ^ k) x = decide (p / 2 ^ k = 1) then (1 : ZMod 2) else 0))
        = (fun x => if runFn (k + 1) ask x = p then (1 : ZMod 2) else 0) := by
      funext x
      simp only [runFn_succ_eq_iff k ask x hp]
      by_cases h1 : runFn k ask x = p % 2 ^ k <;>
        by_cases h2 : ask k (p % 2 ^ k) x = decide (p / 2 ^ k = 1) <;>
        simp [h1, h2]
    rwa [hfun] at hmul

private lemma partition_groups {m L t : Nat} (ht : 0 < t)
    (I : Finset (Fin m)) (hI : I.card = L * t) :
    ∃ G : Fin L → Finset (Fin m),
      (∀ a, (G a).card = t) ∧ (∀ i, i ∈ I ↔ ∃ a, i ∈ G a) := by
  let l := I.toList
  have hlen : l.length = L * t := by
    rw [Finset.length_toList, hI]
  have hnd : l.Nodup := Finset.nodup_toList I
  have hidx : ∀ (a : Fin L) (b : Fin t), a.val * t + b.val < l.length := by
    intro a b
    rw [hlen]
    calc
      a.val * t + b.val < a.val * t + t := Nat.add_lt_add_left b.isLt (a.val * t)
      _ = (a.val + 1) * t := by rw [Nat.succ_mul]
      _ ≤ L * t := Nat.mul_le_mul_right t a.isLt
  let f : Fin L → Fin t → Fin m := fun a b => l[a.val * t + b.val]'(hidx a b)
  refine ⟨fun a => Finset.univ.image (f a), ?_, ?_⟩
  · intro a
    have hinj : Function.Injective (f a) := by
      intro b₁ b₂ heq
      have hpos := (List.Nodup.getElem_inj_iff hnd).mp heq
      exact Fin.ext (Nat.add_left_cancel hpos)
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  · intro i
    constructor
    · intro hi
      have hil : i ∈ l := Finset.mem_toList.mpr hi
      rcases List.mem_iff_getElem.mp hil with ⟨k, hk, hget⟩
      have hklt : k < L * t := hlen ▸ hk
      have ha : k / t < L := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hb : k % t < t := Nat.mod_lt k ht
      refine ⟨⟨k / t, ha⟩, Finset.mem_image.mpr ⟨⟨k % t, hb⟩, Finset.mem_univ _, ?_⟩⟩
      have hkeq : k / t * t + k % t = k := by
        rw [Nat.mul_comm]
        exact Nat.div_add_mod k t
      simpa [f, hkeq] using hget
    · rintro ⟨a, ha⟩
      rcases Finset.mem_image.mp ha with ⟨b, _, rfl⟩
      exact Finset.mem_toList.mp (List.getElem_mem (hidx a b))

private lemma term_deg_le {r c L t k j : Nat} (hcr : c < r)
    (hkj : k + j = L) (hj1 : 1 ≤ j) :
    k * (r * t) + j * (c * t) ≤ r * (L * t) - (r - c) * t := by
  apply Nat.le_sub_of_add_le
  have hrc : c + (r - c) = r := Nat.add_sub_of_le (Nat.le_of_lt hcr)
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  calc
    k * (r * t) + j * (c * t) + (r - c) * t
        = k * (r * t) + (j - 1 + 1) * (c * t) + (r - c) * t := by rw [hj]
    _ = k * (r * t) + ((j - 1) * (c * t) + c * t) + (r - c) * t := by
          rw [Nat.add_mul, one_mul]
    _ = k * (r * t) + (j - 1) * (c * t) + (c * t + (r - c) * t) := by
          rw [← Nat.add_assoc (k * (r * t)), Nat.add_assoc]
    _ = k * (r * t) + (j - 1) * (c * t) + r * t := by
          rw [← Nat.add_mul, hrc]
    _ ≤ k * (r * t) + (j - 1) * (r * t) + r * t := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_left
              (Nat.mul_le_mul_left (j - 1) (Nat.mul_le_mul_right t (Nat.le_of_lt hcr))) _) _
    _ = (k + (j - 1) + 1) * (r * t) := by
          rw [Nat.add_mul, Nat.add_mul, one_mul]
    _ = (k + j) * (r * t) := by
          rw [Nat.add_assoc, hj]
    _ = L * (r * t) := by rw [hkj]
    _ = r * (L * t) := by rw [Nat.mul_left_comm]

private lemma final_deg_le {r c L t D : Nat} (hL : 0 < L) (hD : D < (r - c) * t) :
    D + (r * (L * t) - (r - c) * t) ≤ r * (L * t) - 1 := by
  apply Nat.le_sub_of_add_le
  have hsub : (r - c) * t ≤ r * (L * t) :=
    calc
      (r - c) * t ≤ r * t := Nat.mul_le_mul_right t (Nat.sub_le r c)
      _ = r * (1 * t) := by rw [one_mul]
      _ ≤ r * (L * t) := Nat.mul_le_mul_left r (Nat.mul_le_mul_right t hL)
  calc
    D + (r * (L * t) - (r - c) * t) + 1
        = (D + 1) + (r * (L * t) - (r - c) * t) := Nat.add_right_comm _ _ _
    _ ≤ (r - c) * t + (r * (L * t) - (r - c) * t) := Nat.add_le_add_right hD _
    _ = r * (L * t) := Nat.add_sub_of_le hsub

end PEqualNP.Outside.L_lib_583

theorem PEqualNP.Outside.L_lib_583 : ∀ (m r c d L t : Nat), c < r → 0 < L → 0 < t →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let productOn := fun (I : Finset (Fin m)) (x : W) =>
    decide (∀ i ∈ I, ∀ j : Fin r, x (i,j) = true)
  let run := fun (steps : Nat) (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range steps).foldl (fun past pos => past + ((ask pos past x).toNat <<< pos)) 0
  ∀ (budget : Fin d → Nat) (ask : Nat → Nat → W → Bool)
    (leaf : Nat → Fin L → Fin m → W → Bool),
    (∑ j : Fin d, budget j) < (r-c)*t →
    (∀ (u : Fin d) (path : Nat), deg (budget u) (ask u.val path)) →
    (∀ path a i, deg c (leaf path a i)) →
    let hit := (Finset.univ : Finset W).filter (fun sample =>
      ∃ a, ∀ i, leaf (run d ask sample) a i sample = decide (∀ v : Fin r, sample (i,v) = true))
    ∀ I : Finset (Fin m), I.card = L*t →
      ∃ q : W → Bool, deg (r*I.card-1) q ∧ ∀ x ∈ hit, q x = productOn I x := by
  intro m r c d L t hcr hL ht
  dsimp only
  intro budget ask leaf hbudget hask hleaf I hI
  rcases PEqualNP.Outside.L_lib_583.partition_groups ht I hI with ⟨G, hGcard, hGmem⟩
  let V := Fin m × Fin r
  let W := V → Bool
  let M : Fin L → Finset V := fun a => G a ×ˢ (Finset.univ : Finset (Fin r))
  let T : Fin L → W → ZMod 2 := fun a => PEqualNP.Outside.L_lib_583.evalMon (M a)
  let P : Nat → Fin L → W → ZMod 2 := fun path a x =>
    ∏ i ∈ G a, PEqualNP.Outside.L_lib_583.toZ2 (leaf path a i x)
  let R : Nat → W → ZMod 2 := fun path x =>
    ∑ S ∈ (Finset.univ : Finset (Fin L)).powerset.erase Finset.univ,
      (∏ a ∈ S, T a x) * (∏ a ∈ Finset.univ \ S, P path a x)
  let Q : W → ZMod 2 := fun x =>
    ∑ p ∈ Finset.range (2 ^ d),
      (if PEqualNP.Outside.L_lib_583.runFn d ask x = p then (1 : ZMod 2) else 0) * R p x
  have hTdeg : ∀ a : Fin L, PEqualNP.Outside.L_lib_583.degCoeff (r * t) (T a) := by
    intro a
    have hcard : (M a).card = r * t := by
      change (G a ×ˢ (Finset.univ : Finset (Fin r))).card = r * t
      rw [Finset.card_product, hGcard a, Finset.card_fin, Nat.mul_comm]
    rw [← hcard]
    exact PEqualNP.Outside.L_lib_583.degCoeff_mon (M a)
  have hPdeg : ∀ (path : Nat) (a : Fin L),
      PEqualNP.Outside.L_lib_583.degCoeff (c * t) (P path a) := by
    intro path a
    have h := PEqualNP.Outside.L_lib_583.degCoeff_prod (G a) (fun _ => c)
      (fun i x => PEqualNP.Outside.L_lib_583.toZ2 (leaf path a i x))
      (fun i _ => PEqualNP.Outside.L_lib_583.degCoeff_of_par (hleaf path a i))
    simpa [P, Finset.sum_const, hGcard a, smul_eq_mul, Nat.mul_comm] using h
  have hRdeg : ∀ path : Nat,
      PEqualNP.Outside.L_lib_583.degCoeff (r * (L * t) - (r - c) * t) (R path) := by
    intro path
    refine PEqualNP.Outside.L_lib_583.degCoeff_sum _ _ _ ?_
    intro S hS
    have hSne : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
    have hSlt : S.card < L := by
      simpa using Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hSne)
    have hkj : S.card + (Finset.univ \ S).card = L := by
      have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
      simpa [Nat.add_comm] using h
    have hj1 : 1 ≤ (Finset.univ \ S).card := by
      by_contra h0
      have hz : (Finset.univ \ S).card = 0 := Nat.eq_zero_of_not_pos h0
      rw [hz, add_zero] at hkj
      exact Nat.ne_of_lt hSlt hkj
    have hprodT : PEqualNP.Outside.L_lib_583.degCoeff (S.card * (r * t))
        (fun x => ∏ a ∈ S, T a x) := by
      simpa [Finset.sum_const, smul_eq_mul] using
        PEqualNP.Outside.L_lib_583.degCoeff_prod S (fun _ => r * t) T (fun a _ => hTdeg a)
    have hprodP : PEqualNP.Outside.L_lib_583.degCoeff ((Finset.univ \ S).card * (c * t))
        (fun x => ∏ a ∈ Finset.univ \ S, P path a x) := by
      simpa [Finset.sum_const, smul_eq_mul] using
        PEqualNP.Outside.L_lib_583.degCoeff_prod (Finset.univ \ S) (fun _ => c * t) (P path)
          (fun a _ => hPdeg path a)
    exact PEqualNP.Outside.L_lib_583.degCoeff_mono
      (PEqualNP.Outside.L_lib_583.term_deg_le hcr hkj hj1)
      (PEqualNP.Outside.L_lib_583.degCoeff_mul hprodT hprodP)
  have hindDeg : ∀ p ∈ Finset.range (2 ^ d),
      PEqualNP.Outside.L_lib_583.degCoeff (∑ j : Fin d, budget j)
        (fun x => if PEqualNP.Outside.L_lib_583.runFn d ask x = p then (1 : ZMod 2) else 0) := by
    intro p hp
    exact PEqualNP.Outside.L_lib_583.degCoeff_leaf_ind budget ask
      (fun u path => PEqualNP.Outside.L_lib_583.degCoeff_of_par (hask u path))
      d le_rfl p (Finset.mem_range.mp hp)
  have hQdeg : PEqualNP.Outside.L_lib_583.degCoeff (r * I.card - 1) Q := by
    rw [hI]
    refine PEqualNP.Outside.L_lib_583.degCoeff_sum _ _ _ ?_
    intro p hp
    exact PEqualNP.Outside.L_lib_583.degCoeff_mono
      (PEqualNP.Outside.L_lib_583.final_deg_le hL hbudget)
      (PEqualNP.Outside.L_lib_583.degCoeff_mul (hindDeg p hp) (hRdeg p))
  refine ⟨fun x => decide (Q x = 1), PEqualNP.Outside.L_lib_583.par_of_degCoeff hQdeg, ?_⟩
  intro x hx
  rcases (Finset.mem_filter.mp hx).2 with ⟨a₀, ha₀⟩
  apply PEqualNP.Outside.L_lib_583.toZ2_injective
  rw [PEqualNP.Outside.L_lib_583.toZ2_decide_eq_one]
  let p₀ := PEqualNP.Outside.L_lib_583.runFn d ask x
  have hp₀ : p₀ ∈ Finset.range (2 ^ d) :=
    Finset.mem_range.mpr (PEqualNP.Outside.L_lib_583.runFn_lt d ask x)
  have hQeq : Q x = R p₀ x := by
    dsimp only [Q]
    rw [Finset.sum_eq_single p₀]
    · simp [p₀]
    · intro p _ hne
      have hneq : p₀ ≠ p := Ne.symm hne
      simp [p₀, hneq]
    · intro hnot
      exact absurd hp₀ hnot
  have hTprod : (∏ a : Fin L, T a x)
      = PEqualNP.Outside.L_lib_583.toZ2 (decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) := by
    by_cases hc : ∀ i ∈ I, ∀ j : Fin r, x (i, j) = true
    · have hrhs : PEqualNP.Outside.L_lib_583.toZ2
          (decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) = 1 := by
        rw [decide_eq_true hc]
        rfl
      rw [hrhs]
      refine Finset.prod_eq_one fun a _ => ?_
      have hMa : ∀ v ∈ M a, x v = true := fun v hv => by
        rcases Finset.mem_product.mp hv with ⟨hv1, _⟩
        exact hc v.1 ((hGmem v.1).mpr ⟨a, hv1⟩) v.2
      exact PEqualNP.Outside.L_lib_583.evalMon_eq_one hMa
    · have hrhs : PEqualNP.Outside.L_lib_583.toZ2
          (decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) = 0 := by
        rw [decide_eq_false hc]
        rfl
      rw [hrhs]
      have hex : ∃ i ∈ I, ∃ j : Fin r, x (i, j) ≠ true := by
        by_contra hall
        exact hc fun i hi j => by
          by_contra hne
          exact hall ⟨i, hi, j, hne⟩
      rcases hex with ⟨i, hi, j, hne⟩
      rcases (hGmem i).mp hi with ⟨a, ha⟩
      refine Finset.prod_eq_zero (Finset.mem_univ a) ?_
      have hnot : ¬ ∀ v ∈ M a, x v = true :=
        fun h => hne (h (i, j) (Finset.mem_product.mpr ⟨ha, Finset.mem_univ j⟩))
      exact PEqualNP.Outside.L_lib_583.evalMon_eq_zero hnot
  have hPa₀ : P p₀ a₀ x = T a₀ x := by
    dsimp only [T]
    by_cases hc : ∀ v ∈ M a₀, x v = true
    · rw [PEqualNP.Outside.L_lib_583.evalMon_eq_one hc]
      refine Finset.prod_eq_one fun i hi => ?_
      have hall : ∀ v : Fin r, x (i, v) = true :=
        fun v => hc (i, v) (Finset.mem_product.mpr ⟨hi, Finset.mem_univ v⟩)
      have hleaf1 : leaf p₀ a₀ i x = true := by
        have h := ha₀ i
        rw [decide_eq_true hall] at h
        exact h
      rw [hleaf1]
      rfl
    · rw [PEqualNP.Outside.L_lib_583.evalMon_eq_zero hc]
      have hex : ∃ v ∈ M a₀, x v ≠ true := by
        by_contra hall
        exact hc fun v hv => by
          by_contra hne
          exact hall ⟨v, hv, hne⟩
      rcases hex with ⟨v, hv, hne⟩
      rcases Finset.mem_product.mp hv with ⟨hv1, _⟩
      refine Finset.prod_eq_zero hv1 ?_
      have hnot : ¬ ∀ j : Fin r, x (v.1, j) = true := fun h => hne (h v.2)
      have hleaf0 : leaf p₀ a₀ v.1 x = false := by
        have h := ha₀ v.1
        rw [decide_eq_false hnot] at h
        exact h
      rw [hleaf0]
      rfl
  have hprod0 : (∏ a : Fin L, (T a x + P p₀ a x)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ a₀) ?_
    rw [hPa₀]
    exact PEqualNP.Outside.L_lib_583.zmod2_add_self (T a₀ x)
  have hexpand : (∏ a : Fin L, (T a x + P p₀ a x))
      = (∏ a : Fin L, T a x) + R p₀ x := by
    rw [Finset.prod_add]
    have hmem : (Finset.univ : Finset (Fin L)) ∈
        (Finset.univ : Finset (Fin L)).powerset :=
      Finset.mem_powerset.mpr (Finset.Subset.refl _)
    rw [← Finset.add_sum_erase _ _ hmem]
    simp [R]
  rw [hQeq, ← hTprod]
  exact PEqualNP.Outside.L_lib_583.zmod2_eq_of_add_eq_zero (hexpand.symm.trans hprod0)
