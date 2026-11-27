import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_607_aux

open scoped BigOperators

def bit (b : Bool) : ZMod 2 := (b.toNat : ZMod 2)

theorem bit_injective : Function.Injective bit := by
  intro x y eq
  cases x <;> cases y <;> simp_all [bit]

theorem bit_decide (p : Prop) [Decidable p] : bit (decide p) = if p then 1 else 0 := by
  by_cases h : p <;> simp [bit, h]

theorem bit_parity (n : Nat) : bit ((n % 2) == 1) = (n : ZMod 2) := by
  rw [← ZMod.natCast_mod n 2]
  have small := Nat.mod_lt n (by decide : 0 < 2)
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;> simp [h, bit]

def monomial {V : Type*} (input : V → Bool) (vars : Finset V) : ZMod 2 :=
  if ∀ i ∈ vars, input i = true then 1 else 0

def parity {V : Type*} (terms : Finset (Finset V)) (input : V → Bool) : Bool :=
  ((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1

theorem parity_of_filter {V : Type*} (terms : Finset (Finset V)) (input : V → Bool)
    (predicate : DecidablePred (fun mon : Finset V => ∀ j ∈ mon, input j = true)) :
    (((@Finset.filter _ _ predicate terms).card % 2) == 1) = parity terms input := by
  unfold parity
  apply congrArg (fun s : Finset (Finset V) => (s.card % 2) == 1)
  ext mon
  simp only [Finset.mem_filter]

def blockProduct {r : Nat} (input : Fin r → Bool) : Bool :=
  decide (∀ i, input i = true)

theorem parity_eval {V : Type*} (terms : Finset (Finset V)) (input : V → Bool) :
    bit (parity terms input) =
      ∑ mon ∈ terms, monomial input mon := by
  unfold parity
  rw [bit_parity, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
  simp [monomial]

def flip {I : Type*} [DecidableEq I] (i : I) (word : I → Bool) : I → Bool :=
  Function.update word i (!(word i))

theorem flip_involutive {I : Type*} [DecidableEq I] (i : I) : Function.Involutive (flip i) := by
  intro word
  funext j
  by_cases same : j = i
  · subst j
    simp [flip]
  · simp [flip, Function.update_of_ne same]

theorem even_filter_of_flip {I : Type*} [Fintype I] [DecidableEq I]
    (good : (I → Bool) → Prop) [DecidablePred good] (i : I)
    (stable : ∀ word, good (flip i word) ↔ good word) :
    (((Finset.univ.filter good).card : Nat) : ZMod 2) = 0 := by
  classical
  let eligible := Finset.univ.filter good
  let yes := eligible.filter fun w => w i = true
  let no := eligible.filter fun w => ¬ w i = true
  have pair : yes.card = no.card := by
    apply Finset.card_bijective (flip i) (flip_involutive i).bijective
    intro word
    simp only [yes, no, eligible, Finset.mem_filter, Finset.mem_univ, true_and, stable]
    simp [flip]
  have partition : yes.card + no.card = eligible.card :=
    Finset.card_filter_add_card_filter_not (s := eligible) (fun w => w i = true)
  change (eligible.card : ZMod 2) = 0
  rw [← partition, Nat.cast_add, pair]
  exact CharTwo.add_self_eq_zero _

theorem sum_restricted_terms_zero {I V : Type*} [Fintype I] [DecidableEq I]
    (terms : Finset (Finset V)) (restricted : (I → Bool) → V → Bool)
    (unused : ∀ mon ∈ terms, ∃ i : I, ∀ word j, j ∈ mon →
      restricted (flip i word) j = restricted word j) :
    (∑ word : I → Bool, ∑ mon ∈ terms, monomial (restricted word) mon) = 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro mon belongs
  obtain ⟨i, same⟩ := unused mon belongs
  let good := fun word => ∀ j ∈ mon, restricted word j = true
  have stable (word : I → Bool) : good (flip i word) ↔ good word := by
    unfold good
    exact ⟨fun h j hj => (same word j hj).symm.trans (h j hj),
      fun h j hj => (same word j hj).trans (h j hj)⟩
  have count := even_filter_of_flip good i stable
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter] at count
  simpa [monomial, good] using count

theorem and_terms_full_degree {r : Nat} (terms : Finset (Finset (Fin r)))
    (small : ∀ mon ∈ terms, mon.card < r) :
    ∃ z : Fin r → Bool, parity terms z ≠ blockProduct z := by
  classical
  by_contra! same
  have zero : (∑ z : Fin r → Bool, ∑ mon ∈ terms, monomial z mon) = 0 :=
    sum_restricted_terms_zero terms id (by
      intro mon member
      have missing : ∃ j : Fin r, j ∉ mon := by
        by_contra! all
        have eq : mon = Finset.univ := Finset.eq_univ_of_forall all
        simpa [eq] using small mon member
      obtain ⟨i, outside⟩ := missing
      refine ⟨i, ?_⟩
      intro z j belongs
      have different : j ≠ i := fun eq => outside (eq ▸ belongs)
      simp [flip, Function.update_of_ne different])
  have one : (∑ z : Fin r → Bool, bit (blockProduct z)) = 1 := by
    have truth (z : Fin r → Bool) : (∀ j, z j = true) ↔ z = fun _ => true :=
      ⟨fun h => funext h, fun h => h ▸ fun _ => rfl⟩
    simp [blockProduct, bit_decide, truth]
  have eq : (∑ z : Fin r → Bool, ∑ mon ∈ terms, monomial z mon) =
      ∑ z : Fin r → Bool, bit (blockProduct z) := by
    apply Finset.sum_congr rfl
    intro z _
    exact (parity_eval terms z).symm.trans (congrArg bit (same z))
  rw [zero, one] at eq
  exact zero_ne_one eq

theorem choose_power_parity (n k : Nat) :
    n.choose (2^k) % 2 = (n / 2^k) % 2 := by
  let primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have lucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (n := n) (k := 2^(k+1)) (p := 2)
    have modZero : 2^(k+1) % 2 = 0 := by rw [pow_succ']; exact Nat.mul_mod_right 2 _
    have half : 2^(k+1) / 2 = 2^k := by rw [pow_succ']; simp
    have step : n.choose (2^(k+1)) % 2 = (n / 2).choose (2^k) % 2 := by
      simpa [Nat.ModEq, modZero, half] using lucas
    rw [step, ih, Nat.div_div_eq_div_mul, pow_succ']

def Bounded {V : Type*} (b : Nat) (f : (V → Bool) → ZMod 2) : Prop :=
  ∃ terms : List (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
    ∀ input, f input = (terms.map (monomial input)).sum

theorem bounded_mono {V : Type*} {f : (V → Bool) → ZMod 2} {a b : Nat}
    (h : Bounded a f) (more : a ≤ b) : Bounded b f := by
  obtain ⟨terms, small, eval⟩ := h
  exact ⟨terms, fun vars member => (small vars member).trans more, eval⟩

theorem bounded_zero {V : Type*} (b : Nat) : Bounded (V := V) b (fun _ => 0) := by
  exact ⟨[], by simp, by simp⟩

theorem bounded_one {V : Type*} (b : Nat) : Bounded (V := V) b (fun _ => 1) := by
  exact ⟨[∅], by simp, by simp [monomial]⟩

theorem bounded_variable {V : Type*} (v : V) : Bounded 1 (fun input => bit (input v)) := by
  refine ⟨[{v}], by simp, ?_⟩
  intro input
  cases e : input v <;> simp [monomial, e, bit]

theorem bounded_add {V : Type*} {a b : Nat} {f g : (V → Bool) → ZMod 2}
    (hf : Bounded a f) (hg : Bounded b g) :
    Bounded (max a b) (fun input => f input + g input) := by
  obtain ⟨left, leftSmall, leftEval⟩ := hf
  obtain ⟨right, rightSmall, rightEval⟩ := hg
  refine ⟨left ++ right, ?_, ?_⟩
  · intro vars member
    rcases List.mem_append.mp member with h | h
    · exact (leftSmall _ h).trans (le_max_left _ _)
    · exact (rightSmall _ h).trans (le_max_right _ _)
  · intro input
    simp [leftEval, rightEval, List.sum_append]

theorem monomial_union {V : Type*} [DecidableEq V] (input : V → Bool) (left right : Finset V) :
    monomial input (left ∪ right) = monomial input left * monomial input right := by
  have both : (∀ i ∈ left ∪ right, input i = true) ↔
      (∀ i ∈ left, input i = true) ∧ (∀ i ∈ right, input i = true) := by
    simp only [Finset.mem_union]
    constructor
    · exact fun h => ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · exact fun h i hi => hi.elim (h.1 i) (h.2 i)
  unfold monomial
  by_cases h : ∀ i ∈ left, input i = true
  · by_cases k : ∀ i ∈ right, input i = true
    · rw [ite_eq_left (both.mpr ⟨h, k⟩), ite_eq_left h, ite_eq_left k, one_mul]
    · rw [ite_eq_right (fun all => k (both.mp all).2), ite_eq_left h, ite_eq_right k, mul_zero]
  · rw [ite_eq_right (fun all => h (both.mp all).1), ite_eq_right h, zero_mul]

theorem bounded_mul {V : Type*} {a b : Nat} {f g : (V → Bool) → ZMod 2}
    (hf : Bounded a f) (hg : Bounded b g) : Bounded (a+b) (fun input => f input * g input) := by
  classical
  obtain ⟨left, leftSmall, leftEval⟩ := hf
  obtain ⟨right, rightSmall, rightEval⟩ := hg
  refine ⟨left.flatMap (fun s => right.map (s ∪ ·)), ?_, ?_⟩
  · intro vars member
    obtain ⟨s, hs, via⟩ := List.mem_flatMap.mp member
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp via
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add (leftSmall _ hs) (rightSmall _ ht))
  · intro input
    change f input * g input = _
    rw [leftEval, rightEval]
    have factor (term : ZMod 2) (items : List (Finset V)) :
        (items.map (fun s => term * monomial input s)).sum = term * (items.map (monomial input)).sum := by
      induction items with
      | nil => simp
      | cons s tail ih => simp [ih, mul_add]
    have expand (items : List (Finset V)) :
        (items.flatMap (fun s => right.map (s ∪ ·)) |>.map (monomial input)).sum =
          (items.map (monomial input)).sum * (right.map (monomial input)).sum := by
      induction items with
      | nil => simp
      | cons s tail ih =>
        simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
          Function.comp_def, monomial_union, List.map_cons, List.sum_cons, factor, ih, add_mul]
    exact (expand left).symm

def runThrough {W : Type*} (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (input : W) (t : Nat) : Nat :=
  (List.range t).foldl (fun h pos =>
    h + ((ask pos (h % 2^(seen pos)) input).toNat <<< pos)) 0

theorem run_step {W : Type*} (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (input : W) (t : Nat) :
    runThrough seen ask input (t+1) = runThrough seen ask input t +
      2^t * (ask t (runThrough seen ask input t % 2^(seen t)) input).toNat := by
  simp [runThrough, List.range_succ, List.foldl_append, Nat.shiftLeft_eq, Nat.mul_comm]

theorem run_lt {W : Type*} (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (input : W) (t : Nat) :
    runThrough seen ask input t < 2^t := by
  induction t with
  | zero => simp [runThrough]
  | succ t ih =>
    rw [run_step, pow_succ]
    cases ask t (runThrough seen ask input t % 2^(seen t)) input <;> simp <;> omega

theorem run_prefix {W : Type*} (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (input : W)
    (s t : Nat) (before : s ≤ t) :
    runThrough seen ask input t % 2^s = runThrough seen ask input s := by
  induction t with
  | zero =>
    have eq : s = 0 := by omega
    subst s
    simp [runThrough]
  | succ t ih =>
    by_cases same : s = t+1
    · subst s
      exact Nat.mod_eq_of_lt (run_lt seen ask input _)
    have earlier : s ≤ t := by omega
    rw [run_step, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 earlier),
      zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod, ih earlier]

theorem run_query {W : Type*} (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (input : W)
    (u a : Nat) (inside : u < a) (sees : seen u ≤ u) :
    (ask u (runThrough seen ask input a % 2^(seen u)) input).toNat =
      runThrough seen ask input a / 2^u % 2 := by
  rw [run_prefix seen ask input (seen u) a (by omega),
    ← run_prefix seen ask input (seen u) u sees,
    ← Nat.mod_mul_right_div_self, ← pow_succ,
    run_prefix seen ask input (u+1) a (by omega), run_step,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos u), Nat.div_eq_of_lt (run_lt seen ask input u), Nat.zero_add]

abbrev Switches (a u s : Nat) := Fin (2^(u-s)) × Fin (2^(a-1-u))

theorem switch_count (a u s : Nat) (sees : s ≤ u) (inside : u < a) :
    Fintype.card (Switches a u s) = 2^(a-1-s) := by
  simp only [Switches, Fintype.card_prod, Fintype.card_fin, ← pow_add]
  congr 1
  omega

theorem switch_labels {a u s : Nat} (sees : s ≤ u) (inside : u < a) (past : Fin (2^s)) :
    ∃ (zero : Fin (2^a)) (label : Switches a u s → Fin (2^a)),
      Function.Injective label ∧ (zero.val % 2^s = past.val) ∧ (zero.val / 2^u % 2 = 0) ∧
      (∀ t, (label t).val % 2^s = past.val ∧ (label t).val / 2^u % 2 = 1) := by
  let low (t : Switches a u s) := past.val + 2^s * t.1.val
  have lowLt (t : Switches a u s) : low t < 2^u := by
    calc
      low t < 2^s + 2^s * t.1.val := Nat.add_lt_add_right past.isLt _
      _ = 2^s * (t.1.val + 1) := by ring
      _ ≤ 2^s * 2^(u-s) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt t.1.isLt)
      _ = 2^u := by rw [← pow_add, Nat.add_sub_of_le sees]
  have middleLt (t : Switches a u s) : low t + 2^u < 2^(u+1) := by
    rw [pow_succ]
    have quiet := lowLt t
    omega
  have wholeLt (t : Switches a u s) : low t + 2^u + 2^(u+1) * t.2.val < 2^a := by
    calc
      _ < 2^(u+1) + 2^(u+1) * t.2.val := Nat.add_lt_add_right (middleLt t) _
      _ = 2^(u+1) * (t.2.val+1) := by ring
      _ ≤ 2^(u+1) * 2^(a-1-u) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt t.2.isLt)
      _ = 2^a := by rw [← pow_add]; congr 1; omega
  have pastBelow : past.val < 2^u :=
    past.isLt.trans_le (Nat.pow_le_pow_right (by decide) sees)
  let zero : Fin (2^a) := ⟨past.val, pastBelow.trans_le (Nat.pow_le_pow_right (by decide) inside.le)⟩
  let label (t : Switches a u s) : Fin (2^a) :=
    ⟨low t + 2^u + 2^(u+1) * t.2.val, wholeLt t⟩
  have top (t : Switches a u s) : (label t).val / 2^(u+1) = t.2.val := by
    change (low t + 2^u + 2^(u+1) * t.2.val) / 2^(u+1) = _
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (middleLt t), Nat.zero_add]
  have residue (t : Switches a u s) : (label t).val % 2^(u+1) = low t + 2^u := by
    change (low t + 2^u + 2^(u+1) * t.2.val) % 2^(u+1) = _
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (middleLt t)]
  refine ⟨zero, label, ?_, Nat.mod_eq_of_lt past.isLt, ?_, ?_⟩
  · intro left right eq
    have highEq := (top left).symm.trans ((congrArg (fun h : Fin (2^a) => h.val / 2^(u+1)) eq).trans (top right))
    have middleEq := (residue left).symm.trans ((congrArg (fun h : Fin (2^a) => h.val % 2^(u+1)) eq).trans
      (residue right))
    have same : 2^s * left.1.val = 2^s * right.1.val := by
      dsimp only [low] at middleEq
      omega
    exact Prod.ext (Fin.ext (Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos s) same)) (Fin.ext highEq)
  · change past.val / 2^u % 2 = 0
    rw [Nat.div_eq_of_lt pastBelow, Nat.zero_mod]
  · intro t
    constructor
    · rw [← Nat.mod_mod_of_dvd (label t).val (Nat.pow_dvd_pow 2 (by omega : s ≤ u+1)), residue t,
        Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 sees), Nat.add_zero, Nat.mod_mod]
      change (past.val + 2^s * t.1.val) % 2^s = past.val
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt past.isLt]
    · rw [← Nat.mod_mul_right_div_self, ← pow_succ, residue t]
      have addOne : low t + 2^u = low t + 2^u * 1 := by simp
      rw [addOne, Nat.add_mul_div_left _ _ (Nat.two_pow_pos u), Nat.div_eq_of_lt (lowLt t), Nat.zero_add]

def someTrue {I : Type*} [Fintype I] (word : I → Bool) : Bool :=
  decide (∃ i, word i = true)

theorem or_sum_one {I : Type*} [Fintype I] [DecidableEq I] (positive : 0 < Fintype.card I) :
    (∑ word : I → Bool, bit (someTrue word)) = 1 := by
  classical
  let active : (I → Bool) → Prop := fun word => ∃ i, word i = true
  have silent : (Finset.univ.filter fun word => ¬ active word) = {fun _ => false} := by
    ext word
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro quiet
      funext i
      cases h : word i
      · rfl
      · exact (quiet ⟨i, h⟩).elim
    · rintro rfl ⟨i, hi⟩
      cases hi
  have split := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (I → Bool))) active
  rw [silent, Finset.card_singleton] at split
  have whole : (((Finset.univ : Finset (I → Bool)).card : Nat) : ZMod 2) = 0 := by
    rw [Finset.card_univ, Fintype.card_fun]
    have two : Fintype.card Bool = 2 := by decide
    rw [two, show Fintype.card I = Fintype.card I - 1 + 1 by omega, pow_succ, Nat.cast_mul]
    have even : ((2 : Nat) : ZMod 2) = 0 := by decide
    simp only [even, mul_zero]
  let count : ZMod 2 := (Finset.univ.filter active).card
  have zero : count + 1 = 0 := by
    change (((Finset.univ.filter active).card : Nat) : ZMod 2) + 1 = 0
    simpa only [Nat.cast_add, Nat.cast_one] using (congrArg (fun n : Nat => (n : ZMod 2)) split).trans whole
  have parity : count = 1 := by
    calc
      count = (count + 1) + 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = 1 := by rw [zero, zero_add]
  have summed : count = ∑ word : I → Bool, (if active word then 1 else 0 : ZMod 2) := by
    dsimp only [count]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    simp [active]
  simp only [someTrue, bit_decide]
  exact summed.symm.trans parity

abbrev Blocks (a : Nat) := Fin (2^a - 1)

abbrev Word (a r : Nat) := Blocks a × Fin r → Bool

def QueryDegree {V : Type*} (b : Nat) (query : (V → Bool) → Bool) : Prop :=
  ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
    ∀ input, query input = parity terms input

def Recovers (a r : Nat) (seen : Nat → Nat) (ask : Nat → Nat → Word a r → Bool)
    (leaf : Nat → Blocks a → (Fin r → Bool) → Bool) : Prop :=
  (∀ hist i, ∃ terms : Finset (Finset (Fin r)),
    (∀ mon ∈ terms, mon.card < r) ∧ ∀ z, leaf hist i z = parity terms z) ∧
  ∀ word i, leaf (runThrough seen ask word a) i (fun v => word (i,v)) =
    blockProduct (fun v => word (i,v))

def menuEquiv {n : Nat} (missing : Fin n) : Fin (n - 1) ≃ {i : Fin n // i ≠ missing} := by
  cases n with
  | zero => exact Fin.elim0 missing
  | succ n => exact finSuccAboveEquiv missing

theorem degree_lower (a r : Nat) (seen : Nat → Nat) (ask : Nat → Nat → Word a r → Bool)
    (leaf : Nat → Blocks a → (Fin r → Bool) → Bool)
    (sees : ∀ u : Fin a, seen u.val ≤ u.val) (correct : Recovers a r seen ask leaf)
    (u : Fin a) (past : Fin (2^(seen u.val))) (b : Nat)
    (degree : QueryDegree b (ask u.val past.val)) : 2^(a-1-seen u.val) ≤ b := by
  classical
  by_contra! small
  let I := Switches a u.val (seen u.val)
  have countEq : Fintype.card I = 2^(a-1-seen u.val) := switch_count a u.val (seen u.val) (sees u) u.isLt
  have cardTooBig : b < Fintype.card I := by rwa [countEq]
  obtain ⟨zero, label, injective, zeroPrefix, zeroBit, labels⟩ := switch_labels (sees u) u.isLt past
  have labelDifferent (t : I) : label t ≠ zero := by
    intro eq
    have one := (labels t).2
    rw [eq, zeroBit] at one
    omega
  have misses (h : Fin (2^a)) (i : Blocks a) :
      ∃ z, leaf h.val i z ≠ blockProduct z := by
    obtain ⟨terms, bound, eval⟩ := correct.1 h.val i
    obtain ⟨z, bad⟩ := and_terms_full_degree terms bound
    exact ⟨z, by rwa [eval]⟩
  choose bad badSpec using misses
  let menu := menuEquiv zero
  let switched (z : I → Bool) (h : Fin (2^a)) : Prop := ∃ t, label t = h ∧ z t = true
  let tag (z : I → Bool) (i : Blocks a) :=
    if switched z (menu i).val then zero else (menu i).val
  let word (z : I → Bool) : Word a r := fun v => bad (tag z v.1) v.1 v.2
  let chosen (z : I → Bool) : Fin (2^a) :=
    ⟨runThrough seen ask (word z) a, run_lt seen ask (word z) a⟩
  have avoids (z : I → Bool) (i : Blocks a) : chosen z ≠ tag z i := by
    intro same
    have good := correct.2 (word z) i
    change leaf (chosen z).val i (bad (tag z i) i) = blockProduct (bad (tag z i) i) at good
    rw [same] at good
    exact badSpec (tag z i) i good
  have selectedLabel (z : I → Bool) (nonzero : chosen z ≠ zero) :
      ∃ t : I, label t = chosen z ∧ z t = true := by
    let i := menu.symm ⟨chosen z, nonzero⟩
    have listed : (menu i).val = chosen z :=
      congrArg Subtype.val (menu.apply_symm_apply ⟨chosen z, nonzero⟩)
    have active : switched z (menu i).val := by
      by_contra no
      apply avoids z i
      change chosen z = if switched z (menu i).val then zero else (menu i).val
      rw [ite_eq_right no, listed]
    obtain ⟨t, ht, on⟩ := active
    exact ⟨t, ht.trans listed, on⟩
  have notZero (z : I → Bool) (active : ∃ t : I, z t = true) : chosen z ≠ zero := by
    obtain ⟨t, on⟩ := active
    let i := menu.symm ⟨label t, labelDifferent t⟩
    have listed : (menu i).val = label t :=
      congrArg Subtype.val (menu.apply_symm_apply ⟨label t, labelDifferent t⟩)
    have yes : switched z (menu i).val := ⟨t, listed.symm, on⟩
    intro eq
    exact avoids z i (eq.trans (ite_eq_left yes).symm)
  have evaluates (z : I → Bool) : ask u.val past.val (word z) = someTrue z := by
    have query := run_query seen ask (word z) u.val a u.isLt (sees u)
    change (ask u.val ((chosen z).val % 2^(seen u.val)) (word z)).toNat =
      (chosen z).val / 2^u.val % 2 at query
    by_cases active : ∃ t : I, z t = true
    · obtain ⟨t, labelled, _⟩ := selectedLabel z (notZero z active)
      rw [← labelled, (labels t).1, (labels t).2] at query
      cases value : ask u.val past.val (word z) <;> simp_all [someTrue]
    · have isZero : chosen z = zero := by
        by_contra nonzero
        obtain ⟨t, _, on⟩ := selectedLabel z nonzero
        exact active ⟨t,on⟩
      rw [isZero, zeroPrefix, zeroBit] at query
      cases value : ask u.val past.val (word z) <;> simp_all [someTrue]
  obtain ⟨terms, sizes, eval⟩ := degree
  have unused (mon : Finset (Blocks a × Fin r)) (member : mon ∈ terms) :
      ∃ t : I, ∀ v ∈ mon, label t ≠ (menu v.1).val := by
    by_contra! none
    have contained : (Finset.univ.image label) ⊆ mon.image (fun v => (menu v.1).val) := by
      intro h mem
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp mem
      obtain ⟨v, hv, eq⟩ := none t
      exact Finset.mem_image.mpr ⟨v, hv, eq.symm⟩
    have size := (Finset.card_le_card contained).trans Finset.card_image_le
    rw [Finset.card_image_of_injective _ injective, Finset.card_univ] at size
    exact (Nat.not_le_of_lt cardTooBig) (size.trans (sizes mon member))
  have zeroSum : (∑ z : I → Bool, ∑ mon ∈ terms, monomial (word z) mon) = 0 :=
    sum_restricted_terms_zero terms word (by
      intro mon member
      obtain ⟨t, outside⟩ := unused mon member
      refine ⟨t, ?_⟩
      intro z v hv
      have guard : switched (flip t z) (menu v.1).val ↔ switched z (menu v.1).val := by
        unfold switched
        apply exists_congr
        intro s
        apply and_congr_right
        intro labelEq
        have different : s ≠ t := fun eq => outside v hv (eq ▸ labelEq)
        simp [flip, Function.update_of_ne different]
      have same : tag (flip t z) v.1 = tag z v.1 := by
        unfold tag
        exact if_congr guard rfl rfl
      change bad (tag (flip t z) v.1) v.1 v.2 = bad (tag z v.1) v.1 v.2
      rw [same])
  have oneSum := or_sum_one (I := I) (by omega : 0 < Fintype.card I)
  have eqSum : (∑ z : I → Bool, ∑ mon ∈ terms, monomial (word z) mon) =
      ∑ z : I → Bool, bit (someTrue z) := by
    apply Finset.sum_congr rfl
    intro z _
    exact (parity_eval terms (word z)).symm.trans
      (congrArg bit ((eval (word z)).symm.trans (evaluates z)))
  rw [zeroSum, oneSum] at eqSum
  exact zero_ne_one eqSum

theorem bounded_sum {I V : Type*} (s : Finset I) (d : Nat) (f : I → (V → Bool) → ZMod 2)
    (bound : ∀ i ∈ s, Bounded d (f i)) : Bounded d (fun w => ∑ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bounded_zero (V := V) d)
  | @insert i rest absent ih =>
    have head := bound i (Finset.mem_insert_self i rest)
    have tail := ih (fun j member => bound j (Finset.mem_insert_of_mem member))
    simpa only [Finset.sum_insert absent, max_self] using bounded_add head tail

theorem bounded_prod {I V : Type*} (s : Finset I) (d : Nat) (f : I → (V → Bool) → ZMod 2)
    (bound : ∀ i ∈ s, Bounded d (f i)) : Bounded (d*s.card) (fun w => ∏ i ∈ s, f i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (bounded_one (V := V) 0)
  | @insert i rest absent ih =>
    have head := bound i (Finset.mem_insert_self i rest)
    have tail := ih (fun j member => bound j (Finset.mem_insert_of_mem member))
    simpa [Finset.prod_insert absent, Finset.card_insert_of_notMem absent, Nat.mul_succ, Nat.add_comm] using
      bounded_mul head tail

theorem cancel_repeated_terms {V : Type*} (terms : List (Finset V)) (b : Nat)
    (bound : ∀ mon ∈ terms, mon.card ≤ b) :
    ∃ reduced : Finset (Finset V), (∀ mon ∈ reduced, mon.card ≤ b) ∧
      ∀ w, (terms.map (monomial w)).sum = ∑ mon ∈ reduced, monomial w mon := by
  classical
  induction terms with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons head tail ih =>
    obtain ⟨terms, hbound, eval⟩ := ih (fun mon member => bound mon (List.mem_cons_of_mem _ member))
    by_cases occurs : head ∈ terms
    · refine ⟨terms.erase head, fun mon member => hbound _ (Finset.mem_of_mem_erase member), ?_⟩
      intro w
      have split := Finset.sum_erase_add (s := terms) (monomial w) occurs
      rw [List.map_cons, List.sum_cons, eval, ← split]
      rw [← add_assoc, add_comm (monomial w head) (∑ m ∈ terms.erase head, monomial w m), add_assoc,
        CharTwo.add_self_eq_zero, add_zero]
    · refine ⟨insert head terms, ?_, ?_⟩
      · intro mon member
        rcases Finset.mem_insert.mp member with equal | remaining
        · subst mon
          exact bound head List.mem_cons_self
        · exact hbound mon remaining
      · intro w
        rw [List.map_cons, List.sum_cons, eval, Finset.sum_insert occurs]

theorem degree_of_bounded {V : Type*} {d : Nat} {f : (V → Bool) → Bool}
    (proof : Bounded d (fun w => bit (f w))) : QueryDegree d f := by
  obtain ⟨terms, bound, eval⟩ := proof
  obtain ⟨reduced, sizes, same⟩ := cancel_repeated_terms terms d bound
  refine ⟨reduced, sizes, ?_⟩
  intro w
  apply bit_injective
  exact (eval w).trans ((same w).trans (parity_eval reduced w).symm)

def digit (n i : Nat) : Nat := n / 2^i % 2

theorem digit_lt_two (n i : Nat) : digit n i < 2 := Nat.mod_lt _ (by decide)

def localBit {r : Nat} (z : Fin r → Bool) (i : Nat) : Bool :=
  if h : i < r then z ⟨i,h⟩ else false

abbrev prefixMatch {r : Nat} (z : Fin r → Bool) (k tag : Nat) : Prop :=
  ∀ i : Fin k, (localBit z i.val).toNat = digit tag i.val

theorem digit_earlier (h u j : Nat) (before : j < u) :
    digit (h+2^u) j = digit h j := by
  unfold digit
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self, ← pow_succ, Nat.add_mod,
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (Nat.succ_le_of_lt before)),
    Nat.add_zero, Nat.mod_mod]

theorem digit_append (h u : Nat) (bound : h < 2^u) (b : Bool) :
    digit (h + 2^u*b.toNat) u = b.toNat := by
  unfold digit
  rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos u), Nat.div_eq_of_lt bound, Nat.zero_add]
  cases b <;> decide

theorem prefix_match_step {r : Nat} (z : Fin r → Bool) (u h : Nat) (bound : h < 2^u) (b : Bool) :
    prefixMatch z (u+1) (h + 2^u*b.toNat) ↔ prefixMatch z u h ∧ localBit z u = b := by
  have earlier (j : Nat) (lt : j < u) : digit (h + 2^u*b.toNat) j = digit h j := by
    cases b
    · simp
    · simpa using digit_earlier h u j lt
  constructor
  · intro allBits
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [earlier i.val i.isLt] using allBits ⟨i.val, i.isLt.trans (Nat.lt_succ_self _)⟩
    · have eq := allBits ⟨u, Nat.lt_succ_self _⟩
      change (localBit z u).toNat = digit (h+2^u*b.toNat) u at eq
      rw [digit_append h u bound b] at eq
      cases read : localBit z u <;> cases b <;> simp_all
  · rintro ⟨prev, bitEq⟩ i
    by_cases before : i.val < u
    · simpa only [earlier i.val before] using prev ⟨i.val, before⟩
    · have eq : i.val = u := by have := i.isLt; omega
      rw [eq, bitEq, digit_append h u bound b]

def blocksAt {a r : Nat} (word : Word a r) (u h : Nat) : Finset (Blocks a) :=
  Finset.univ.filter fun i => prefixMatch (fun j => word (i,j)) u h

theorem split_blocks {a r : Nat} (word : Word a r) (u h : Nat) (bound : h < 2^u) :
    (blocksAt word (u+1) h).card + (blocksAt word (u+1) (h+2^u)).card = (blocksAt word u h).card := by
  let reads := fun i : Blocks a => localBit (fun j => word (i,j)) u = true
  have no : blocksAt word (u+1) h = (blocksAt word u h).filter (fun i => ¬ reads i) := by
    ext i
    have step : prefixMatch (fun j => word (i,j)) (u+1) h ↔
        prefixMatch (fun j => word (i,j)) u h ∧ localBit (fun j => word (i,j)) u = false := by
      simpa using prefix_match_step (fun j => word (i,j)) u h bound false
    simp [blocksAt, reads, step]
  have yes : blocksAt word (u+1) (h+2^u) = (blocksAt word u h).filter reads := by
    ext i
    have step : prefixMatch (fun j => word (i,j)) (u+1) (h+2^u) ↔
        prefixMatch (fun j => word (i,j)) u h ∧ localBit (fun j => word (i,j)) u = true := by
      simpa using prefix_match_step (fun j => word (i,j)) u h bound true
    simp [blocksAt, reads, step]
  rw [no, yes, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not (s := blocksAt word u h) reads

def chooseHalf (a r : Nat) (u h : Nat) (word : Word a r) : Bool :=
  (((blocksAt word (u+1) h).card.choose (2^(a-1-u))) % 2) == 1

theorem choose_threshold (n k : Nat) (bound : n < 2^(k+1)) :
    (n.choose (2^k) % 2 == 1) = decide (2^k ≤ n) := by
  rw [choose_power_parity]
  have quotientLt : n / 2^k < 2 :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr (by simpa [pow_succ, Nat.mul_comm] using bound)
  by_cases enough : 2^k ≤ n
  · have one : 1 ≤ n / 2^k :=
      (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by simpa using enough)
    have value : n / 2^k = 1 := by omega
    simp [value, enough]
  · have value : n / 2^k = 0 := Nat.div_eq_of_lt (Nat.lt_of_not_ge enough)
    simp [value, enough]

theorem fewer_blocks_than_labels {a r : Nat} (word : Word a r) (u : Nat) (before : u ≤ a) :
    (blocksAt word u (runThrough id (chooseHalf a r) word u)).card < 2^(a-u) := by
  induction u with
  | zero =>
    have card := Finset.card_filter_le (s := (Finset.univ : Finset (Blocks a)))
      (fun i => prefixMatch (fun j => word (i,j)) 0 (runThrough id (chooseHalf a r) word 0))
    simp only [Finset.card_univ, Fintype.card_fin] at card
    have positive := Nat.two_pow_pos a
    change (blocksAt word 0 (runThrough id (chooseHalf a r) word 0)).card ≤ 2^a-1 at card
    simpa only [Nat.sub_zero] using (show (blocksAt word 0 (runThrough id (chooseHalf a r) word 0)).card < 2^a by omega)
  | succ u ih =>
    let h := runThrough id (chooseHalf a r) word u
    let k := a-1-u
    have hBelow : h < 2^u := run_lt _ _ _ _
    have split := split_blocks word u h hBelow
    have leftRight : (blocksAt word (u+1) h).card + (blocksAt word (u+1) (h+2^u)).card < 2^(k+1) := by
      rw [split, show k+1 = a-u by dsimp [k]; omega]
      exact ih (by omega)
    have leftLt : (blocksAt word (u+1) h).card < 2^(k+1) := by omega
    have next := choose_threshold (blocksAt word (u+1) h).card k leftLt
    change chooseHalf a r u h word = decide (2^k ≤ (blocksAt word (u+1) h).card) at next
    rw [run_step]
    change (blocksAt word (u+1)
      (h + 2^u * (chooseHalf a r u (h % 2^u) word).toNat)).card < 2^(a-(u+1))
    rw [Nat.mod_eq_of_lt hBelow, next, show a-(u+1) = k by dsimp [k]; omega]
    rw [pow_succ] at leftRight
    by_cases filled : 2^k ≤ (blocksAt word (u+1) h).card
    · simp only [filled, decide_true, Bool.toNat_true, Nat.mul_one]
      omega
    · simp only [filled, decide_false, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
      omega

def truePositions {r : Nat} (z : Fin r → Bool) : Finset (Fin r) :=
  Finset.univ.filter fun i => z i = true

theorem truePositions_injective {r : Nat} : Function.Injective (truePositions (r := r)) := by
  intro left right eq
  funext i
  apply Bool.eq_iff_iff.mpr
  rw [← show i ∈ truePositions left ↔ left i = true by simp [truePositions],
    ← show i ∈ truePositions right ↔ right i = true by simp [truePositions], eq]

def pointTerms {r : Nat} (target : Fin r → Bool) : Finset (Finset (Fin r)) :=
  Finset.Icc (truePositions target) Finset.univ

theorem pointTerms_off {r : Nat} (target z : Fin r → Bool) (diff : z ≠ target) :
    parity (pointTerms target) z = false := by
  have enabled : (pointTerms target).filter (fun mon => ∀ j ∈ mon, z j = true) =
      Finset.Icc (truePositions target) (truePositions z) := by
    ext mon
    have inside : (∀ j ∈ mon, z j = true) ↔ mon ⊆ truePositions z := by
      simp [Finset.subset_iff, truePositions]
    simp [pointTerms, inside]
  have even : ((Finset.Icc (truePositions target) (truePositions z)).card % 2 == 1) = false := by
    by_cases subset : truePositions target ⊆ truePositions z
    · have unequal : truePositions target ≠ truePositions z := fun eq => diff (truePositions_injective eq.symm)
      have increasing := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset, unequal⟩)
      rw [Finset.card_Icc_finset subset]
      have positive : 0 < (truePositions z).card - (truePositions target).card := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
      rw [hk, pow_succ']
      simp
    · have empty : Finset.Icc (truePositions target) (truePositions z) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro mon included
        obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp included
        exact subset (lo.trans hi)
      simp [empty]
  rwa [← enabled, parity_of_filter] at even

def labelPattern {r : Nat} (h : Nat) (i : Fin r) : Bool :=
  (digit h i.val) == 1

theorem label_has_prefix {a r : Nat} (fits : a ≤ r) (h : Nat) :
    prefixMatch (labelPattern (r := r) h) a h := by
  intro i
  have inside : i.val < r := i.isLt.trans_le fits
  simp only [localBit, dite_eq_left inside, labelPattern]
  have small := digit_lt_two h i.val
  rcases (show digit h i.val = 0 ∨ digit h i.val = 1 by omega) with h0 | h1
  · simp [h0]
  · simp [h1]

def predict {r : Nat} (h : Nat) (z : Fin r → Bool) : Bool :=
  parity ((pointTerms (labelPattern (r := r) h)).erase Finset.univ) z

theorem predict_low {r : Nat} (h : Nat) :
    ∃ terms : Finset (Finset (Fin r)),
      (∀ mon ∈ terms, mon.card < r) ∧ ∀ z, predict h z = parity terms z := by
  refine ⟨(pointTerms (labelPattern (r := r) h)).erase Finset.univ, ?_, fun _ => rfl⟩
  intro mon included
  have smaller := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.subset_univ mon, (Finset.mem_erase.mp included).1⟩)
  simpa using smaller

theorem predict_agrees_of_missing {a r : Nat} (fits : a ≤ r) (h : Nat) (z : Fin r → Bool)
    (missing : ¬ prefixMatch z a h) : predict h z = blockProduct z := by
  let target := labelPattern (r := r) h
  let full := pointTerms target
  have notEqual : z ≠ target := by
    intro eq
    exact missing (eq ▸ label_has_prefix fits h)
  have top : Finset.univ ∈ full := by simp [full, pointTerms]
  have product : monomial z Finset.univ = bit (blockProduct z) := by
    simp [monomial, blockProduct, bit_decide]
  have split : bit (predict h z) + bit (blockProduct z) = 0 := by
    change bit (parity (full.erase Finset.univ) z) + bit (blockProduct z) = 0
    rw [parity_eval, ← product, Finset.sum_erase_add (s := full) _ top, ← parity_eval,
      pointTerms_off target z notEqual]
    rfl
  apply bit_injective
  calc
    bit (predict h z) = (bit (predict h z) + bit (blockProduct z)) + bit (blockProduct z) := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    _ = bit (blockProduct z) := by rw [split, zero_add]

theorem recovers_upper {a r : Nat} (fits : a ≤ r) :
    Recovers a r id (chooseHalf a r) (fun h _ z => predict h z) := by
  refine ⟨fun h _ => predict_low h, ?_⟩
  intro word i
  apply predict_agrees_of_missing fits
  intro found
  have member : i ∈ blocksAt word a (runThrough id (chooseHalf a r) word a) := by
    simpa [blocksAt] using found
  have small := fewer_blocks_than_labels word a le_rfl
  have positive := Finset.card_pos.mpr ⟨i, member⟩
  rw [Nat.sub_self, pow_zero] at small
  exact (Nat.not_lt_of_ge positive) small

theorem bounded_bit_test {V : Type*} (v : V) (d : Nat) (small : d < 2) :
    Bounded 1 (fun input => if (input v).toNat = d then 1 else 0) := by
  rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
  · have same : (fun input : V → Bool => if (input v).toNat = 0 then (1 : ZMod 2) else 0) =
        (fun input => 1 + bit (input v)) := by
      funext input
      cases input v <;> simp [bit, CharTwo.add_self_eq_zero]
    rw [same]
    simpa only [max_self] using bounded_add (bounded_one (V := V) 1) (bounded_variable v)
  · have same : (fun input : V → Bool => if (input v).toNat = 1 then (1 : ZMod 2) else 0) =
        (fun input => bit (input v)) := by
      funext input
      cases input v <;> simp [bit]
    rw [same]
    exact bounded_variable v

theorem bounded_prefix_test {a r k : Nat} (fits : k ≤ r) (h : Nat) (i : Blocks a) :
    Bounded k (fun word : Word a r => if prefixMatch (fun j => word (i,j)) k h then 1 else 0) := by
  let test (j : Fin k) (word : Word a r) : ZMod 2 :=
    if (localBit (fun v => word (i,v)) j.val).toNat = digit h j.val then 1 else 0
  have each (j : Fin k) : Bounded 1 (test j) := by
    have inside : j.val < r := j.isLt.trans_le fits
    simpa only [test, localBit, dite_eq_left inside] using
      bounded_bit_test (i, (⟨j.val, inside⟩ : Fin r)) (digit h j.val) (digit_lt_two h j.val)
  have combined := bounded_prod Finset.univ 1 test (fun j _ => each j)
  have product (word : Word a r) : (∏ j : Fin k, test j word) =
      if prefixMatch (fun v => word (i,v)) k h then 1 else 0 := by
    change (∏ j : Fin k, if (localBit (fun v => word (i,v)) j.val).toNat = digit h j.val
      then (1 : ZMod 2) else 0) = _
    simp only [Finset.prod_boole, Finset.mem_univ, true_implies, prefixMatch]
  have exactness : (fun word : Word a r => ∏ j : Fin k, test j word) =
      (fun word => if prefixMatch (fun v => word (i,v)) k h then 1 else 0) := funext product
  rw [exactness] at combined
  simpa only [Finset.card_univ, Fintype.card_fin, one_mul] using combined

theorem choose_degree {a r : Nat} (fits : a ≤ r) (u : Fin a) (h : Nat) :
    QueryDegree ((u.val+1)*2^(a-1-u.val)) (chooseHalf a r u.val h) := by
  classical
  let k := u.val + 1
  let capacity := 2^(a-1-u.val)
  let tests (i : Blocks a) (word : Word a r) : ZMod 2 :=
    if prefixMatch (fun v => word (i,v)) k h then 1 else 0
  let sets := (Finset.univ : Finset (Blocks a)).powersetCard capacity
  have each (s : Finset (Blocks a)) (included : s ∈ sets) :
      Bounded (k*capacity) (fun word => ∏ i ∈ s, tests i word) := by
    have size : s.card = capacity := (Finset.mem_powersetCard.mp included).2
    have combined := bounded_prod s k tests
      (fun i _ => bounded_prefix_test ((Nat.succ_le_of_lt u.isLt).trans fits) h i)
    simpa only [size] using combined
  have combined := bounded_sum sets (k*capacity) (fun s word => ∏ i ∈ s, tests i word) each
  apply degree_of_bounded
  have exactness : (fun word : Word a r => ∑ s ∈ sets, ∏ i ∈ s, tests i word) =
      (fun word => bit (chooseHalf a r u.val h word)) := by
    funext word
    let active := blocksAt word k h
    have product (s : Finset (Blocks a)) : (∏ i ∈ s, tests i word) =
        if s ⊆ active then 1 else 0 := by
      have membership (i : Blocks a) : i ∈ active ↔ prefixMatch (fun j => word (i,j)) k h := by
        simp [active, blocksAt]
      by_cases all : s ⊆ active
      · rw [ite_eq_left all]
        apply Finset.prod_eq_one
        intro i hi
        simp [tests, (membership i).mp (all hi)]
      · rw [ite_eq_right all]
        have missing : ∃ i ∈ s, i ∉ active := by
          simpa only [Finset.subset_iff, not_forall, not_imp, exists_prop] using all
        obtain ⟨i, hi, absent⟩ := missing
        apply Finset.prod_eq_zero hi
        exact ite_eq_right (fun matchFound => absent ((membership i).mpr matchFound))
    have candidates : (sets.filter fun s => s ⊆ active) = active.powersetCard capacity := by
      ext s
      simp [sets, Finset.mem_powersetCard, and_comm]
    calc
      (∑ s ∈ sets, ∏ i ∈ s, tests i word) = ∑ s ∈ sets, if s ⊆ active then (1 : ZMod 2) else 0 :=
        Finset.sum_congr rfl (fun s _ => product s)
      _ = ((sets.filter fun s => s ⊆ active).card : ZMod 2) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
        simp
      _ = (active.card.choose capacity : ZMod 2) := by rw [candidates, Finset.card_powersetCard]
      _ = bit (chooseHalf a r u.val h word) := (bit_parity _).symm
  rw [exactness] at combined
  exact combined

end PEqualNP.Outside.L_lib_607_aux

open PEqualNP.Outside.L_lib_607_aux in

theorem PEqualNP.Outside.L_lib_607 : (∀ (a r : Nat), 0 < a → a ≤ r →
  let m := 2^a-1
  let V := Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let B := Fin r → Bool
  let low := fun (q : B → Bool) => ∃ terms : Finset (Finset (Fin r)),
    (∀ mon ∈ terms, mon.card < r) ∧ ∀ z, q z =
      (((terms.filter (fun mon => ∀ j ∈ mon, z j = true)).card % 2) == 1)
  let run := fun (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (x : W) =>
    (List.range a).foldl (fun h pos =>
      h + ((ask pos (h % 2^(seen pos)) x).toNat <<< pos)) 0
  let exact := fun (seen : Nat → Nat) (ask : Nat → Nat → W → Bool)
    (leaf : Nat → Fin m → B → Bool) =>
    (∀ hist i, low (leaf hist i)) ∧ ∀ word i,
      leaf (run seen ask word) i (fun v => word (i,v)) = decide (∀ j : Fin r, word (i,j) = true)
  (∀ (seen : Nat → Nat) (ask : Nat → Nat → W → Bool) (leaf : Nat → Fin m → B → Bool),
    (∀ u : Fin a, seen u.val ≤ u.val) → exact seen ask leaf →
    ∀ (u : Fin a) (past : Fin (2^(seen u.val))) (b : Nat),
      deg b (ask u.val past.val) → 2^(a-1-seen u.val) ≤ b) ∧
  ∃ (choose : Nat → Nat → W → Bool) (predict : Nat → Fin m → B → Bool),
    exact id choose predict ∧ ∀ (u : Fin a) (path : Nat),
      deg ((u.val+1)*2^(a-1-u.val)) (choose u.val path)) := by
  intro a r _ fits
  dsimp only
  simp only [parity_of_filter]
  exact ⟨degree_lower a r,
    ⟨chooseHalf a r, fun h _ z => predict h z, recovers_upper fits, choose_degree fits⟩⟩
