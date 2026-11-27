import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_594

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover (ReadsBack gateAt)

-- Credit: adapted the rank recurrence and circuit gadgets from L_lib_603.

def b2n (b : Bool) : ℕ := if b then 1 else 0

def natOf {m : ℕ} (f : Fin m → Bool) : ℕ :=
  ∑ i : Fin m, if f i then 2 ^ i.val else 0

lemma natOf_snoc {m : ℕ} (f : Fin m → Bool) (b : Bool) :
    natOf (Fin.snoc f b) = natOf f + if b then 2 ^ m else 0 := by
  simp only [natOf, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.val_castSucc, Fin.val_last]

lemma natOf_lt {m : ℕ} (f : Fin m → Bool) : natOf f < 2 ^ m := by
  induction m with
  | zero => simp [natOf]
  | succ m ih =>
    have h := ih (fun i : Fin m => f i.castSucc)
    simp only [natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last] at h ⊢
    cases f (Fin.last m) <;> simp [pow_succ] <;> omega

lemma natOf_not_plus {m : ℕ} (f : Fin m → Bool) :
    natOf (fun i => !f i) + natOf f = 2 ^ m - 1 := by
  induction m with
  | zero => simp [natOf]
  | succ m ih =>
    have h := ih (fun i : Fin m => f i.castSucc)
    have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h1 : natOf (fun i : Fin (m + 1) => !f i) =
        natOf (fun i : Fin m => !f i.castSucc) + if !f (Fin.last m) then 2 ^ m else 0 := by
      simp only [natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have h2 : natOf f =
        natOf (fun i : Fin m => f i.castSucc) + if f (Fin.last m) then 2 ^ m else 0 := by
      simp only [natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    rw [h1, h2]
    cases f (Fin.last m) <;> simp [pow_succ] <;> omega

lemma testBit_eq_div_mod (n k : ℕ) : n.testBit k = decide ((n / 2 ^ k) % 2 = 1) := by
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow]
  have h : (n / 2 ^ k) % 2 = 0 ∨ (n / 2 ^ k) % 2 = 1 := by omega
  rcases h with h0 | h1
  · simp [h0]
  · simp [h1]

lemma testBit_natOf {m : ℕ} (f : Fin m → Bool) (j : Fin m) :
    (natOf f).testBit j.val = f j := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    have hsplit : natOf f = natOf (fun i : Fin m => f i.castSucc) +
        if f (Fin.last m) then 2 ^ m else 0 := by
      simp only [natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    set a := natOf (fun i : Fin m => f i.castSucc)
    have ha : a < 2 ^ m := natOf_lt _
    rw [hsplit]
    by_cases hlt : j.val < m
    · have hj : j = (⟨j.val, hlt⟩ : Fin m).castSucc := by ext; rfl
      rw [hj, Fin.val_castSucc, ← ih (fun i : Fin m => f i.castSucc) ⟨j.val, hlt⟩,
        testBit_eq_div_mod, testBit_eq_div_mod]
      cases hb : f (Fin.last m)
      · simp [a]
      · simp only [↓reduceIte]
        have h2m : 2 ^ m = 2 ^ j.val * (2 * 2 ^ (m - j.val - 1)) := by
          have : m = j.val + 1 + (m - j.val - 1) := by omega
          conv_lhs => rw [this]
          rw [pow_add, pow_add, pow_one]
          ring
        have hpos : 0 < 2 ^ j.val := Nat.two_pow_pos _
        rw [h2m, Nat.add_mul_div_left _ _ hpos]
        simp [Nat.add_mul_mod_self_left, a]
    · have hjeq : j = Fin.last m := by ext; simp; omega
      rw [hjeq, Fin.val_last, testBit_eq_div_mod]
      have hpos : 0 < 2 ^ m := Nat.two_pow_pos _
      cases hb : f (Fin.last m)
      · simp [Nat.div_eq_of_lt ha]
      · simp only [↓reduceIte]
        rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt ha]
        simp

lemma natOf_testBit (m x : ℕ) (hx : x < 2 ^ m) :
    natOf (fun i : Fin m => x.testBit i.val) = x := by
  induction m generalizing x with
  | zero => simp [natOf]; omega
  | succ m ih =>
    simp only [natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
    have hpos : 0 < 2 ^ m := Nat.two_pow_pos _
    set rem := x % 2 ^ m
    set quo := x / 2 ^ m
    have hmod_lt : rem < 2 ^ m := Nat.mod_lt x hpos
    have hdiv_lt : quo < 2 := by
      change x / 2 ^ m < 2
      rw [Nat.div_lt_iff_lt_mul hpos]
      simpa [pow_succ, mul_comm] using hx
    have hdecomp : x = rem + 2 ^ m * quo := (Nat.mod_add_div x (2 ^ m)).symm
    have hlow : (∑ i : Fin m, if x.testBit i.val then 2 ^ i.val else 0) = rem := by
      have hcongr : (∑ i : Fin m, if x.testBit i.val then 2 ^ i.val else 0) =
          natOf (fun i : Fin m => rem.testBit i.val) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hbit : x.testBit i.val = rem.testBit i.val := by
          rw [testBit_eq_div_mod, testBit_eq_div_mod]
          have h2m : 2 ^ m = 2 ^ i.val * (2 * 2 ^ (m - i.val - 1)) := by
            have : m = i.val + 1 + (m - i.val - 1) := by omega
            conv_lhs => rw [this]
            rw [pow_add, pow_add, pow_one]
            ring
          have hpi : 0 < 2 ^ i.val := Nat.two_pow_pos _
          have hdiv_eq : x / 2 ^ i.val = rem / 2 ^ i.val + 2 * (2 ^ (m - i.val - 1) * quo) := by
            have hmul : 2 ^ m * quo = 2 ^ i.val * (2 * (2 ^ (m - i.val - 1) * quo)) := by
              rw [h2m]; ring
            calc x / 2 ^ i.val = (rem + 2 ^ m * quo) / 2 ^ i.val := by rw [← hdecomp]
              _ = (rem + 2 ^ i.val * (2 * (2 ^ (m - i.val - 1) * quo))) / 2 ^ i.val := by rw [hmul]
              _ = rem / 2 ^ i.val + 2 * (2 ^ (m - i.val - 1) * quo) := Nat.add_mul_div_left _ _ hpi
          rw [hdiv_eq, Nat.add_mul_mod_self_left]
        rw [hbit]
      rw [hcongr, ih rem hmod_lt]
    rw [hlow, testBit_eq_div_mod]
    change rem + (if decide (quo % 2 = 1) = true then 2 ^ m else 0) = x
    have hcases : quo = 0 ∨ quo = 1 :=
      (Nat.lt_succ_iff.mp hdiv_lt).lt_or_eq.elim (fun h => Or.inl (Nat.lt_one_iff.mp h)) Or.inr
    rcases hcases with h0 | h1
    · rw [h0] at hdecomp ⊢
      simp at hdecomp ⊢
      omega
    · rw [h1] at hdecomp ⊢
      simp at hdecomp ⊢
      omega

def runPrefix {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (p u : Fin l → Bool) : (k : ℕ) → k ≤ l → Fin q
  | 0, _ => start
  | k + 1, hk =>
    step ⟨k, hk⟩ (runPrefix step start p u k (Nat.le_of_succ_le hk)) (p ⟨k, hk⟩) (u ⟨k, hk⟩)

lemma runPrefix_congr {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (p u v : Fin l → Bool) (k : ℕ) (hk : k ≤ l)
    (huv : ∀ i : Fin l, i.val < k → u i = v i) :
    runPrefix step start p u k hk = runPrefix step start p v k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [runPrefix]
    rw [ih (Nat.le_of_succ_le hk) (fun i hi => huv i (by omega))]
    rw [huv ⟨k, hk⟩ (by simp)]

lemma foldl_finRange_take_eq_runPrefix {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q)
    (start : Fin q) (p u : Fin l → Bool) (k : ℕ) (hk : k ≤ l) :
    ((List.finRange l).take k).foldl (fun st j => step j st (p j) (u j)) start =
      runPrefix step start p u k hk := by
  induction k with
  | zero => simp [runPrefix]
  | succ k ih =>
    have hlt : k < (List.finRange l).length := by simp; omega
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, List.getElem_finRange, Fin.cast_mk]
    rw [ih (Nat.le_of_succ_le hk)]
    rfl

lemma foldl_finRange_eq_runPrefix {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q)
    (start : Fin q) (p u : Fin l → Bool) :
    (List.finRange l).foldl (fun st j => step j st (p j) (u j)) start =
      runPrefix step start p u l (le_refl l) := by
  have h := foldl_finRange_take_eq_runPrefix step start p u l (le_refl l)
  rwa [show (List.finRange l).take l = List.finRange l by simp] at h

def dpVal {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (p : Fin l → Bool) : (m : ℕ) → m ≤ l → Fin q → ℕ
  | 0, _, s => if final s then 1 else 0
  | m + 1, hm, s =>
    let k : Fin l := ⟨l - (m + 1), by omega⟩
    dpVal step final p m (by omega) (step k s (p k) false) +
    dpVal step final p m (by omega) (step k s (p k) true)

lemma dpVal_le {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (p : Fin l → Bool) (m : ℕ) (hm : m ≤ l) (s : Fin q) :
    dpVal step final p m hm s ≤ 2 ^ m := by
  induction m generalizing s with
  | zero => simp only [dpVal]; split_ifs <;> omega
  | succ m ih =>
    simp only [dpVal]
    have h0 := ih (by omega) (step ⟨l - (m + 1), by omega⟩ s (p ⟨l - (m + 1), by omega⟩) false)
    have h1 := ih (by omega) (step ⟨l - (m + 1), by omega⟩ s (p ⟨l - (m + 1), by omega⟩) true)
    rw [pow_succ]
    omega

def zeroCount {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (p : Fin l → Bool) (k : Fin l) (s : Fin q) : ℕ :=
  dpVal step final p (l - 1 - k.val) (by omega) (step k s (p k) false)

def oneCount {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (p : Fin l → Bool) (k : Fin l) (s : Fin q) : ℕ :=
  dpVal step final p (l - 1 - k.val) (by omega) (step k s (p k) true)

lemma dpVal_split {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (p : Fin l → Bool) (k : Fin l) (s : Fin q) :
    dpVal step final p (l - k.val) (by omega) s =
      zeroCount step final p k s + oneCount step final p k s := by
  have heq : l - k.val = (l - 1 - k.val) + 1 := by omega
  have hk : (⟨l - ((l - 1 - k.val) + 1), by omega⟩ : Fin l) = k := by ext; dsimp; omega
  generalize_proofs hp
  conv_lhs => rw [show dpVal step final p (l - k.val) hp s =
      dpVal step final p ((l - 1 - k.val) + 1) (by omega) s by congr 1]
  simp only [dpVal, hk, zeroCount, oneCount]

def goodSet {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) : Finset (Fin l → Bool) :=
  Finset.univ.filter (fun u =>
    final ((List.finRange l).foldl (fun st j => step j st (p j) (u j)) start) = true)

def goodPrefix {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (k : ℕ) (u : Fin l → Bool) :
    Finset (Fin l → Bool) :=
  (goodSet step start final p).filter (fun v => ∀ i : Fin l, i.val < k → v i = u i)

lemma card_goodPrefix {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (m : ℕ) (hm : m ≤ l) (u : Fin l → Bool) :
    (goodPrefix step start final p (l - m) u).card =
      dpVal step final p m hm (runPrefix step start p u (l - m) (by omega)) := by
  induction m generalizing u with
  | zero =>
    simp only [Nat.sub_zero, dpVal]
    by_cases hf : final (runPrefix step start p u l (le_refl l)) = true
    · have hset : goodPrefix step start final p l u = {u} := by
        ext v
        simp only [goodPrefix, goodSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, foldl_finRange_eq_runPrefix]
        constructor
        · rintro ⟨_, hvu⟩
          funext i
          exact hvu i i.isLt
        · rintro rfl
          exact ⟨hf, fun _ _ => rfl⟩
      rw [hset, Finset.card_singleton]
      simp [hf]
    · have hset : goodPrefix step start final p l u = ∅ := by
        ext v
        simp only [goodPrefix, goodSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false, not_and, foldl_finRange_eq_runPrefix]
        intro hfv hvu
        have hveq : v = u := funext fun i => hvu i i.isLt
        subst hveq
        exact hf hfv
      rw [hset, Finset.card_empty]
      simp [hf]
  | succ m ih =>
    let k : Fin l := ⟨l - (m + 1), by omega⟩
    let u0 := Function.update u k false
    let u1 := Function.update u k true
    have hdisj : Disjoint (goodPrefix step start final p (l - m) u0)
        (goodPrefix step start final p (l - m) u1) := by
      rw [Finset.disjoint_left]
      intro v hv0 hv1
      simp only [goodPrefix, Finset.mem_filter] at hv0 hv1
      have h0 := hv0.2 k (by dsimp [k]; omega)
      have h1 := hv1.2 k (by dsimp [k]; omega)
      simp [u0, u1] at h0 h1
      rw [h0] at h1
      exact Bool.false_ne_true h1
    have hunion : goodPrefix step start final p (l - (m + 1)) u =
        goodPrefix step start final p (l - m) u0 ∪ goodPrefix step start final p (l - m) u1 := by
      ext v
      simp only [goodPrefix, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ⟨hv, hpre⟩
        cases hvk : v k
        · left
          refine ⟨hv, fun i hi => ?_⟩
          by_cases hik : i = k
          · subst hik; simp [u0, hvk]
          · have hilt : i.val < l - (m + 1) := by
              have : i.val ≠ k.val := fun he => hik (Fin.ext he)
              dsimp [k] at this
              omega
            simp [u0, Function.update_of_ne hik, hpre i hilt]
        · right
          refine ⟨hv, fun i hi => ?_⟩
          by_cases hik : i = k
          · subst hik; simp [u1, hvk]
          · have hilt : i.val < l - (m + 1) := by
              have : i.val ≠ k.val := fun he => hik (Fin.ext he)
              dsimp [k] at this
              omega
            simp [u1, Function.update_of_ne hik, hpre i hilt]
      · rintro (⟨hv, hpre⟩ | ⟨hv, hpre⟩)
        · refine ⟨hv, fun i hi => ?_⟩
          have hne : i ≠ k := fun he => by subst he; dsimp [k] at hi; omega
          have h1 := hpre i (by omega)
          simpa [u0, Function.update_of_ne hne] using h1
        · refine ⟨hv, fun i hi => ?_⟩
          have hne : i ≠ k := fun he => by subst he; dsimp [k] at hi; omega
          have h1 := hpre i (by omega)
          simpa [u1, Function.update_of_ne hne] using h1
    rw [hunion, Finset.card_union_of_disjoint hdisj, ih (by omega) u0, ih (by omega) u1]
    have hstep_b : ∀ b : Bool,
        runPrefix step start p (Function.update u k b) (l - m) (by omega) =
          step k (runPrefix step start p u (l - (m + 1)) (by omega)) (p k) b := by
      intro b
      have hsucc : l - m = (l - (m + 1)) + 1 := by omega
      have hrew : runPrefix step start p (Function.update u k b) (l - m) (by omega) =
          runPrefix step start p (Function.update u k b) ((l - (m + 1)) + 1) (by omega) := by
        congr 1
      rw [hrew]
      simp only [runPrefix]
      have hcongr : runPrefix step start p (Function.update u k b) (l - (m + 1)) (by omega) =
          runPrefix step start p u (l - (m + 1)) (by omega) := by
        refine runPrefix_congr step start p _ _ _ _ fun i hi => ?_
        have hne : i ≠ k := fun he => by subst he; dsimp [k] at hi; omega
        exact Function.update_of_ne hne b u
      have hval : Function.update u k b ⟨l - (m + 1), by omega⟩ = b := by
        change Function.update u k b k = b
        simp
      rw [hcongr, hval]
    rw [hstep_b false, hstep_b true]
    rfl

def keyOf {l : ℕ} (w : Fin l → Bool) : ℕ :=
  ∑ i : Fin l, if w i then 2 ^ (l - 1 - i.val) else 0

lemma sum_tail_lt {l : ℕ} (j : Fin l) (w : Fin l → Bool) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin l => j.val < i.val),
      (if w i then 2 ^ (l - 1 - i.val) else 0) < 2 ^ (l - 1 - j.val) := by
  let rev : Fin (l - 1 - j.val) → Fin l := fun t => ⟨l - 1 - t.val, by omega⟩
  have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin l => j.val < i.val),
        (if w i then 2 ^ (l - 1 - i.val) else 0) ≤
      natOf (fun t : Fin (l - 1 - j.val) => w (rev t)) := by
    have hinj : Function.Injective rev := by
      intro a b hab
      have hval := congrArg Fin.val hab
      dsimp [rev] at hval
      ext; omega
    have himg : Finset.univ.filter (fun i : Fin l => j.val < i.val) = Finset.univ.image rev := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hi
        refine ⟨⟨l - 1 - i.val, by omega⟩, ?_⟩
        ext; dsimp [rev]; omega
      · rintro ⟨t, rfl⟩
        dsimp [rev]; omega
    rw [himg, Finset.sum_image (fun a _ b _ h => hinj h)]
    unfold natOf
    refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
    have heq : l - 1 - (rev t).val = t.val := by dsimp [rev]; omega
    rw [heq]
  exact lt_of_le_of_lt hle (natOf_lt _)

lemma keyOf_lt_of_lex {l : ℕ} {v u : Fin l → Bool} (j : Fin l)
    (hpre : ∀ i : Fin l, i.val < j.val → v i = u i) (hvj : v j = false) (huj : u j = true) :
    keyOf v < keyOf u := by
  unfold keyOf
  set Slt := Finset.univ.filter (fun i : Fin l => i.val < j.val)
  set Sgt := Finset.univ.filter (fun i : Fin l => j.val < i.val)
  have hsplit : ∀ w : Fin l → Bool,
      (∑ i : Fin l, if w i then 2 ^ (l - 1 - i.val) else 0) =
      (∑ i ∈ Slt, if w i then 2 ^ (l - 1 - i.val) else 0) +
      (if w j then 2 ^ (l - 1 - j.val) else 0) +
      (∑ i ∈ Sgt, if w i then 2 ^ (l - 1 - i.val) else 0) := by
    intro w
    have hdisj1 : Disjoint Slt {j} := by
      rw [Finset.disjoint_singleton_right]
      simp [Slt]
    have hdisj2 : Disjoint (Slt ∪ {j}) Sgt := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      simp only [Finset.mem_union, Finset.mem_singleton, Slt, Sgt, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi1 hi2
      rcases hi1 with h1 | rfl <;> omega
    have hall : (Finset.univ : Finset (Fin l)) = (Slt ∪ {j}) ∪ Sgt := by
      ext i
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, Slt, Sgt,
        Finset.mem_filter, true_and, true_iff]
      rcases lt_trichotomy i.val j.val with h1 | h2 | h3
      · left; left; exact h1
      · left; right; exact Fin.ext h2
      · right; exact h3
    conv_lhs => rw [hall]
    rw [Finset.sum_union hdisj2, Finset.sum_union hdisj1, Finset.sum_singleton]
  rw [hsplit v, hsplit u]
  have hSlt : (∑ i ∈ Slt, if v i then 2 ^ (l - 1 - i.val) else 0) =
      (∑ i ∈ Slt, if u i then 2 ^ (l - 1 - i.val) else 0) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Slt, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [hpre i hi]
  rw [hSlt, hvj, huj]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have htail : (∑ i ∈ Sgt, if v i then 2 ^ (l - 1 - i.val) else 0) < 2 ^ (l - 1 - j.val) :=
    sum_tail_lt j v
  have hge : 0 ≤ ∑ i ∈ Sgt, if u i then 2 ^ (l - 1 - i.val) else 0 := Nat.zero_le _
  omega

lemma keyOf_lt_iff {l : ℕ} (v u : Fin l → Bool) :
    keyOf v < keyOf u ↔
      ∃ j : Fin l, (∀ i : Fin l, i.val < j.val → v i = u i) ∧ v j = false ∧ u j = true := by
  constructor
  · intro hlt
    have hne : v ≠ u := fun h => by subst h; exact lt_irrefl _ hlt
    have hdiff : (Finset.univ.filter (fun i : Fin l => v i ≠ u i)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne
      funext i
      by_contra hvi
      have hmem : i ∈ Finset.univ.filter (fun i : Fin l => v i ≠ u i) := by simp [hvi]
      rw [hempty] at hmem
      exact Finset.notMem_empty i hmem
    let j := (Finset.univ.filter (fun i : Fin l => v i ≠ u i)).min' hdiff
    have hj_mem : j ∈ Finset.univ.filter (fun i : Fin l => v i ≠ u i) := Finset.min'_mem _ _
    have hj_ne : v j ≠ u j := (Finset.mem_filter.mp hj_mem).2
    have hpre : ∀ i : Fin l, i.val < j.val → v i = u i := by
      intro i hi
      by_contra hvi
      have him : i ∈ Finset.univ.filter (fun i : Fin l => v i ≠ u i) := by simp [hvi]
      have hle : j ≤ i := Finset.min'_le _ i him
      exact absurd hle (not_le.mpr hi)
    cases hvj : v j <;> cases huj : u j
    · exact absurd (hvj.trans huj.symm) hj_ne
    · exact ⟨j, hpre, hvj, huj⟩
    · have hgt := keyOf_lt_of_lex j (fun i hi => (hpre i hi).symm) huj hvj
      omega
    · exact absurd (hvj.trans huj.symm) hj_ne
  · rintro ⟨j, hpre, hvj, huj⟩
    exact keyOf_lt_of_lex j hpre hvj huj

lemma card_lt_keyOf {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p u : Fin l → Bool) :
    ((goodSet step start final p).filter (fun other => keyOf other < keyOf u)).card =
      ∑ j : Fin l, if u j then zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0 := by
  let piece : Fin l → Finset (Fin l → Bool) := fun j =>
    if u j then goodPrefix step start final p (j.val + 1) (Function.update u j false) else ∅
  have hbi : (goodSet step start final p).filter (fun other => keyOf other < keyOf u) =
      Finset.univ.biUnion piece := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, keyOf_lt_iff]
    constructor
    · rintro ⟨hv, j, hpre, hvj, huj⟩
      refine ⟨j, ?_⟩
      simp only [piece, huj, ↓reduceIte, goodPrefix, Finset.mem_filter]
      refine ⟨hv, fun i hi => ?_⟩
      by_cases hij : i = j
      · subst hij; simp [hvj]
      · have hilt : i.val < j.val := by
          have : i.val ≠ j.val := fun he => hij (Fin.ext he)
          omega
        simp [Function.update_of_ne hij, hpre i hilt]
    · rintro ⟨j, hv⟩
      cases huj : u j
      · simp [piece, huj] at hv
      · simp only [piece, huj, ↓reduceIte, goodPrefix, Finset.mem_filter] at hv
        refine ⟨hv.1, j, fun i hi => ?_, ?_, huj⟩
        · have hne : i ≠ j := fun he => by subst he; omega
          have h1 := hv.2 i (by omega)
          simpa [Function.update_of_ne hne] using h1
        · have h1 := hv.2 j (by omega)
          simpa using h1
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin l)) piece := by
    intro j1 _ j2 _ hne
    change Disjoint (piece j1) (piece j2)
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    cases hu1 : u j1
    · simp [piece, hu1] at hv1
    cases hu2 : u j2
    · simp [piece, hu2] at hv2
    simp only [piece, hu1, hu2, ↓reduceIte, goodPrefix, Finset.mem_filter] at hv1 hv2
    rcases lt_or_gt_of_ne (fun h : j1.val = j2.val => hne (Fin.ext h)) with hlt | hgt
    · have h1 := hv1.2 j1 (by omega)
      have h2 := hv2.2 j1 (by omega)
      have hne12 : j1 ≠ j2 := hne
      simp [Function.update_of_ne hne12, hu1] at h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2
    · have h1 := hv1.2 j2 (by omega)
      have h2 := hv2.2 j2 (by omega)
      have hne21 : j2 ≠ j1 := hne.symm
      simp [Function.update_of_ne hne21, hu2] at h1 h2
      rw [h2] at h1
      exact Bool.false_ne_true h1
  rw [hbi, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases huj : u j
  · simp [piece, huj]
  · simp only [piece, huj, ↓reduceIte]
    have heq : j.val + 1 = l - (l - 1 - j.val) := by omega
    rw [heq, card_goodPrefix step start final p (l - 1 - j.val) (by omega)]
    have hr : runPrefix step start p (Function.update u j false) (l - (l - 1 - j.val)) (by omega) =
        step j (runPrefix step start p u j.val (by omega)) (p j) false := by
      have h1 : runPrefix step start p (Function.update u j false) (l - (l - 1 - j.val)) (by omega) =
          runPrefix step start p (Function.update u j false) (j.val + 1) (by omega) := by
        congr 1; omega
      rw [h1]
      simp only [runPrefix]
      have hcongr : runPrefix step start p (Function.update u j false) j.val (by omega) =
          runPrefix step start p u j.val (by omega) := by
        refine runPrefix_congr step start p _ _ _ _ fun i hi => ?_
        have hne : i ≠ j := fun he => by subst he; omega
        exact Function.update_of_ne hne false u
      have hvj : Function.update u j false ⟨j.val, by omega⟩ = false := by
        change Function.update u j false j = false
        simp
      rw [hcongr, hvj]
    rw [hr]
    rfl

def encRun {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (r : ℕ) :
    (k : ℕ) → k ≤ l → Fin q × ℕ × (Fin l → Bool)
  | 0, _ => (start, r, fun _ => false)
  | k + 1, hk =>
    let prev := encRun step start final p r k (Nat.le_of_succ_le hk)
    let kj : Fin l := ⟨k, hk⟩
    let z := zeroCount step final p kj prev.1
    let b := decide (z ≤ prev.2.1)
    (step kj prev.1 (p kj) b, if b then prev.2.1 - z else prev.2.1, Function.update prev.2.2 kj b)

lemma encRun_word_stable {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (r : ℕ) (k : ℕ) (hk : k ≤ l)
    (j : Fin l) (hj : j.val < k) :
    (encRun step start final p r l (le_refl l)).2.2 j =
      (encRun step start final p r k hk).2.2 j := by
  have haux : ∀ m (hm : m ≤ l), k ≤ m →
      (encRun step start final p r m hm).2.2 j = (encRun step start final p r k hk).2.2 j := by
    intro m hm hkm
    induction m with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0; rfl
    | succ m ih =>
      by_cases hkeq : k = m + 1
      · subst hkeq; rfl
      · have hle : k ≤ m := by omega
        have hne : j ≠ ⟨m, hm⟩ := fun h => by
          have := congrArg Fin.val h; dsimp at this; omega
        simp only [encRun]
        rw [Function.update_of_ne hne, ih (Nat.le_of_succ_le hm) hle]
  exact haux l (le_refl l) hk

lemma encRun_inv {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (r : ℕ)
    (hr : r < (goodSet step start final p).card) (k : ℕ) (hk : k ≤ l) :
    let res := encRun step start final p r k hk
    let word := (encRun step start final p r l (le_refl l)).2.2
    res.1 = runPrefix step start p word k hk ∧
    res.2.1 < dpVal step final p (l - k) (by omega) res.1 ∧
    r = res.2.1 + ∑ j : Fin l, if j.val < k ∧ word j = true then
      zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0 := by
  set word := (encRun step start final p r l (le_refl l)).2.2
  induction k with
  | zero =>
    have hcard : (goodSet step start final p).card = dpVal step final p l (le_refl l) start := by
      have h := card_goodPrefix step start final p l (le_refl l) (fun _ => false)
      have hgp : goodPrefix step start final p (l - l) (fun _ => false) = goodSet step start final p := by
        ext v; simp [goodPrefix]
      rw [hgp] at h
      simpa [runPrefix] using h
    refine ⟨rfl, ?_, by simp [encRun]⟩
    simpa [encRun, hcard] using hr
  | succ k ih =>
    obtain ⟨hst, hrem, hsum⟩ := ih (Nat.le_of_succ_le hk)
    set prev := encRun step start final p r k (Nat.le_of_succ_le hk)
    set kj : Fin l := ⟨k, hk⟩
    set z := zeroCount step final p kj prev.1
    set b := decide (z ≤ prev.2.1)
    have hstep_eq : encRun step start final p r (k + 1) hk =
        (step kj prev.1 (p kj) b, if b then prev.2.1 - z else prev.2.1,
          Function.update prev.2.2 kj b) := rfl
    have hwk : word kj = b := by
      have hst1 := encRun_word_stable step start final p r (k + 1) hk kj (by simp [kj])
      change (encRun step start final p r l (le_refl l)).2.2 kj = b
      rw [hst1, hstep_eq]
      simp
    have hst' : (encRun step start final p r (k + 1) hk).1 =
        runPrefix step start p word (k + 1) hk := by
      rw [hstep_eq]
      change step kj prev.1 (p kj) b =
        step kj (runPrefix step start p word k (Nat.le_of_succ_le hk)) (p kj) (word kj)
      rw [hst, hwk]
    have hsplit : dpVal step final p (l - k) (by omega) prev.1 =
        z + oneCount step final p kj prev.1 := dpVal_split step final p kj prev.1
    have hrem' : (encRun step start final p r (k + 1) hk).2.1 <
        dpVal step final p (l - (k + 1)) (by omega) (encRun step start final p r (k + 1) hk).1 := by
      rw [hstep_eq]
      dsimp only
      have hsub : l - (k + 1) = l - 1 - kj.val := by simp [kj]; omega
      by_cases hge : z ≤ prev.2.1
      · have hb : b = true := decide_eq_true hge
        rw [hb]
        simp only [↓reduceIte]
        have h1 : dpVal step final p (l - (k + 1)) (by omega) (step kj prev.1 (p kj) true) =
            oneCount step final p kj prev.1 := by
          unfold oneCount; congr 1
        rw [h1]
        omega
      · have hb : b = false := decide_eq_false hge
        rw [hb]
        simp only [Bool.false_eq_true, ↓reduceIte]
        have h1 : dpVal step final p (l - (k + 1)) (by omega) (step kj prev.1 (p kj) false) =
            z := by
          unfold z zeroCount; congr 1
        rw [h1]
        omega
    have hsum' : r = (encRun step start final p r (k + 1) hk).2.1 +
        ∑ j : Fin l, if j.val < k + 1 ∧ word j = true then
          zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0 := by
      have hdiff :
          (∑ j : Fin l, if j.val < k + 1 ∧ word j = true then
            zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) =
          (∑ j : Fin l, if j.val < k ∧ word j = true then
            zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) +
          (if word kj = true then z else 0) := by
        rw [← Finset.sum_add_sum_compl {kj}]
        have h1 : (∑ j ∈ ({kj} : Finset (Fin l)),
            if j.val < k + 1 ∧ word j = true then
              zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) =
            if word kj = true then z else 0 := by
          simp [kj, z, hst]
        have h2 : (∑ j ∈ ({kj} : Finset (Fin l))ᶜ,
            if j.val < k + 1 ∧ word j = true then
              zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) =
            (∑ j : Fin l, if j.val < k ∧ word j = true then
              zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) := by
          rw [← Finset.sum_add_sum_compl {kj}]
          have hkj0 : (∑ j ∈ ({kj} : Finset (Fin l)),
              if j.val < k ∧ word j = true then
                zeroCount step final p j (runPrefix step start p word j.val (by omega)) else 0) = 0 := by
            simp [kj]
          rw [hkj0, zero_add]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          have hne : j.val ≠ k := fun he => hj (Fin.ext he)
          have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
          simp [hiff]
        rw [h1, h2, add_comm]
      rw [hdiff, hstep_eq, hwk]
      dsimp only
      by_cases hge : z ≤ prev.2.1
      · have hb : b = true := decide_eq_true hge
        rw [hb]
        simp only [↓reduceIte]
        omega
      · have hb : b = false := decide_eq_false hge
        rw [hb]
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
        exact hsum
    exact ⟨hst', hrem', hsum'⟩

def selectFn {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (r : Fin (goodSet step start final p).card) :
    ↥(goodSet step start final p) :=
  ⟨(encRun step start final p r.val l (le_refl l)).2.2, by
    have ⟨hst, hrem, _⟩ := encRun_inv step start final p r.val r.isLt l (le_refl l)
    simp only [Nat.sub_self, dpVal] at hrem
    have hfin : final (encRun step start final p r.val l (le_refl l)).1 = true := by
      by_contra h
      simp [h] at hrem
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and, foldl_finRange_eq_runPrefix]
    rwa [← hst]⟩

lemma selectFn_rank {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) (r : Fin (goodSet step start final p).card) :
    ((goodSet step start final p).filter (fun other => keyOf other < keyOf (selectFn step start final p r).val)).card = r.val := by
  have ⟨_, hrem, hsum⟩ := encRun_inv step start final p r.val r.isLt l (le_refl l)
  simp only [Nat.sub_self, dpVal] at hrem
  have hrem0 : (encRun step start final p r.val l (le_refl l)).2.1 = 0 := by
    split_ifs at hrem <;> omega
  rw [card_lt_keyOf]
  have hcongr : (∑ j : Fin l, if (selectFn step start final p r).val j then
        zeroCount step final p j (runPrefix step start p (selectFn step start final p r).val j.val (by omega)) else 0) =
      (∑ j : Fin l, if j.val < l ∧ (encRun step start final p r.val l (le_refl l)).2.2 j = true then
        zeroCount step final p j (runPrefix step start p (encRun step start final p r.val l (le_refl l)).2.2 j.val (by omega)) else 0) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [selectFn, j.isLt, true_and]
    rfl
  rw [hcongr]
  omega

noncomputable def selectEquiv {l q : ℕ} (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (final : Fin q → Bool) (p : Fin l → Bool) :
    Fin (goodSet step start final p).card ≃ ↥(goodSet step start final p) :=
  Equiv.ofBijective (selectFn step start final p) <| by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp⟩
    intro r1 r2 heq
    have h1 := selectFn_rank step start final p r1
    have h2 := selectFn_rank step start final p r2
    rw [heq] at h1
    exact Fin.ext (h1.symm.trans h2)

def BasisOK (g : Gate) : Prop :=
  ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨ (g.op = .not ∧ g.inputs.length = 1)

def ValidGates (n : ℕ) (gs : List Gate) : Prop :=
  ReadsBack n ⟨gs, 0⟩ ∧ ∀ g ∈ gs, BasisOK g

def wiresOf (x : List Bool) (gs : List Gate) : List Bool :=
  (Circuit.mk gs 0).wires x

def wireVal (x : List Bool) (gs : List Gate) (w : ℕ) : Bool :=
  (wiresOf x gs).getD w false

lemma getD_append_lt {α : Type*} (l1 l2 : List α) (k : ℕ) (d : α) (hk : k < l1.length) :
    (l1 ++ l2).getD k d = l1.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (k : ℕ) (d : α) (hk : l1.length ≤ k) :
    (l1 ++ l2).getD k d = l2.getD (k - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hk]

lemma wiresOf_nil (x : List Bool) : wiresOf x [] = x := rfl

lemma wiresOf_concat (x : List Bool) (gs : List Gate) (g : Gate) :
    wiresOf x (gs ++ [g]) =
      wiresOf x gs ++ [g.op.eval (g.inputs.map fun i => wireVal x gs i)] := by
  unfold wiresOf wireVal Circuit.wires
  rw [List.foldl_append]
  rfl

lemma wiresOf_length (x : List Bool) (gs : List Gate) :
    (wiresOf x gs).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wiresOf_nil]
  | append_singleton gs g ih =>
    rw [wiresOf_concat, List.length_append, List.length_singleton, ih, List.length_append,
      List.length_singleton]
    omega

lemma wireVal_prefix (x : List Bool) {gs1 gs2 : List Gate} (h : gs1 <+: gs2)
    {k : ℕ} (hk : k < x.length + gs1.length) :
    wireVal x gs2 k = wireVal x gs1 k := by
  rcases h with ⟨ext, rfl⟩
  induction ext using List.reverseRecOn with
  | nil => simp
  | append_singleton ext g ih =>
    unfold wireVal at ih ⊢
    rw [← List.append_assoc, wiresOf_concat, getD_append_lt]
    · exact ih
    · rw [wiresOf_length, List.length_append]; omega

lemma wireVal_concat_last (x : List Bool) (gs : List Gate) (g : Gate) :
    wireVal x (gs ++ [g]) (x.length + gs.length) =
      g.op.eval (g.inputs.map fun i => wireVal x gs i) := by
  change (wiresOf x (gs ++ [g])).getD (x.length + gs.length) false = _
  rw [wiresOf_concat, getD_append_right]
  · rw [wiresOf_length, Nat.sub_self]; rfl
  · rw [wiresOf_length]

lemma validGates_nil (n : ℕ) : ValidGates n [] := by
  refine ⟨fun j hj => by simp at hj, fun g hg => by simp at hg⟩

lemma validGates_append_singleton {n : ℕ} {gs : List Gate} {g : Gate}
    (hv : ValidGates n gs) (hin : ∀ i ∈ g.inputs, i < n + gs.length) (hb : BasisOK g) :
    ValidGates n (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hgat : gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := by
        simp only [gateAt]
        exact getD_append_lt gs [g] j ⟨.or, []⟩ hlt
      rw [hgat] at hi
      exact hv.1 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hgat : gateAt ⟨gs ++ [g], 0⟩ gs.length = g := by
        simp only [gateAt]
        rw [getD_append_right gs [g] gs.length ⟨.or, []⟩ (le_refl _)]
        simp
      rw [hgat] at hi
      exact hin i hi
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hv.2 g' h1
    · simp only [List.mem_singleton] at h2
      subst h2
      exact hb

lemma input_wireVal {l : ℕ} (u : Fin l → Bool) (gs : List Gate) (k : Fin l) :
    wireVal (List.ofFn u) gs k.val = u k := by
  rw [wireVal_prefix _ List.nil_prefix (by simp)]
  simp [wireVal, wiresOf_nil, List.getD_eq_getElem?_getD]

def pushNot (n : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.not, [a]⟩], n + gs.length)

def pushAnd (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.and, [a, b]⟩], n + gs.length)

def pushOr (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨.or, [a, b]⟩], n + gs.length)

lemma pushNot_spec (n : ℕ) (gs : List Gate) (a : ℕ)
    (hv : ValidGates n gs) (ha : a < n + gs.length) :
    let res := pushNot n gs a
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2 = !(wireVal x gs a) := by
  refine ⟨validGates_append_singleton hv (by simp [ha]) (Or.inr ⟨rfl, rfl⟩),
    List.prefix_append _ _, by simp [pushNot], by simp [pushNot], fun x hx => ?_⟩
  simp only [pushNot]
  rw [← hx, wireVal_concat_last]
  simp [GateOp.eval]

lemma pushAnd_spec (n : ℕ) (gs : List Gate) (a b : ℕ)
    (hv : ValidGates n gs) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let res := pushAnd n gs a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2 = (wireVal x gs a && wireVal x gs b) := by
  refine ⟨validGates_append_singleton hv (by simp [ha, hb]) (Or.inl ⟨Or.inl rfl, rfl⟩),
    List.prefix_append _ _, by simp [pushAnd], by simp [pushAnd], fun x hx => ?_⟩
  simp only [pushAnd]
  rw [← hx, wireVal_concat_last]
  simp [GateOp.eval]

lemma pushOr_spec (n : ℕ) (gs : List Gate) (a b : ℕ)
    (hv : ValidGates n gs) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let res := pushOr n gs a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2 = (wireVal x gs a || wireVal x gs b) := by
  refine ⟨validGates_append_singleton hv (by simp [ha, hb]) (Or.inl ⟨Or.inr rfl, rfl⟩),
    List.prefix_append _ _, by simp [pushOr], by simp [pushOr], fun x hx => ?_⟩
  simp only [pushOr]
  rw [← hx, wireVal_concat_last]
  simp [GateOp.eval]

def pushConsts (n : ℕ) (gs : List Gate) : List Gate × ℕ × ℕ :=
  let r1 := pushNot n gs 0
  let r2 := pushAnd n r1.1 0 r1.2
  let r3 := pushOr n r2.1 0 r1.2
  (r3.1, r2.2, r3.2)

lemma pushConsts_spec (n : ℕ) (hn : 0 < n) (gs : List Gate) (hv : ValidGates n gs) :
    let res := pushConsts n gs
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 3 ∧
    res.2.1 < n + res.1.length ∧ res.2.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2.1 = false ∧ wireVal x res.1 res.2.2 = true := by
  dsimp only [pushConsts]
  rcases hr1 : pushNot n gs 0 with ⟨gs1, n0⟩
  have hs1 := pushNot_spec n gs 0 hv (by omega); rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hw1, he1⟩ := hs1
  rcases hr2 : pushAnd n gs1 0 n0 with ⟨gs2, cF⟩
  have hs2 := pushAnd_spec n gs1 0 n0 hv1 (by omega) hw1; rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
  rcases hr3 : pushOr n gs2 0 n0 with ⟨gs3, cT⟩
  have hs3 := pushOr_spec n gs2 0 n0 hv2 (by omega) (by omega); rw [hr3] at hs3; dsimp only at hs3
  obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
  dsimp only
  refine ⟨hv3, hp1.trans (hp2.trans hp3), by omega, by omega, hw3, fun x hx => ?_⟩
  have h0_1 : wireVal x gs1 0 = wireVal x gs 0 := wireVal_prefix x hp1 (by omega)
  have h0_2 : wireVal x gs2 0 = wireVal x gs 0 := wireVal_prefix x (hp1.trans hp2) (by omega)
  have hn0_2 : wireVal x gs2 n0 = !(wireVal x gs 0) := by
    rw [wireVal_prefix x hp2 (by omega), he1 x hx]
  constructor
  · rw [wireVal_prefix x hp3 (by omega), he2 x hx, h0_1, he1 x hx]
    cases wireVal x gs 0 <;> rfl
  · rw [he3 x hx, h0_2, hn0_2]
    cases wireVal x gs 0 <;> rfl

def pushXor (n : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := pushOr n gs a b
  let r2 := pushAnd n r1.1 a b
  let r3 := pushNot n r2.1 r2.2
  pushAnd n r3.1 r1.2 r3.2

lemma pushXor_spec (n : ℕ) (gs : List Gate) (a b : ℕ)
    (hv : ValidGates n gs) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let res := pushXor n gs a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2 = xor (wireVal x gs a) (wireVal x gs b) := by
  dsimp only [pushXor]
  rcases hr1 : pushOr n gs a b with ⟨gs1, w1⟩
  have hs1 := pushOr_spec n gs a b hv ha hb; rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hw1, he1⟩ := hs1
  rcases hr2 : pushAnd n gs1 a b with ⟨gs2, w2⟩
  have hs2 := pushAnd_spec n gs1 a b hv1 (by omega) (by omega); rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
  rcases hr3 : pushNot n gs2 w2 with ⟨gs3, w3⟩
  have hs3 := pushNot_spec n gs2 w2 hv2 hw2; rw [hr3] at hs3; dsimp only at hs3
  obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
  rcases hr4 : pushAnd n gs3 w1 w3 with ⟨gs4, w4⟩
  have hs4 := pushAnd_spec n gs3 w1 w3 hv3 (by omega) hw3; rw [hr4] at hs4; dsimp only at hs4
  obtain ⟨hv4, hp4, hl4, hw4, he4⟩ := hs4
  dsimp only
  refine ⟨hv4, hp1.trans (hp2.trans (hp3.trans hp4)), by omega, hw4, fun x hx => ?_⟩
  rw [he4 x hx]
  rw [wireVal_prefix x (hp2.trans hp3) (by omega), he1 x hx]
  rw [he3 x hx, he2 x hx]
  rw [wireVal_prefix x hp1 (by omega), wireVal_prefix x hp1 (by omega)]
  cases wireVal x gs a <;> cases wireVal x gs b <;> rfl

def pushMux (n : ℕ) (gs : List Gate) (sel a b : ℕ) : List Gate × ℕ :=
  let r1 := pushNot n gs sel
  let r2 := pushAnd n r1.1 sel a
  let r3 := pushAnd n r2.1 r1.2 b
  pushOr n r3.1 r2.2 r3.2

lemma pushMux_spec (n : ℕ) (gs : List Gate) (sel a b : ℕ)
    (hv : ValidGates n gs) (hs : sel < n + gs.length) (ha : a < n + gs.length) (hb : b < n + gs.length) :
    let res := pushMux n gs sel a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 ∧
    res.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      wireVal x res.1 res.2 = if wireVal x gs sel then wireVal x gs a else wireVal x gs b := by
  dsimp only [pushMux]
  rcases hr1 : pushNot n gs sel with ⟨gs1, ns⟩
  have hs1 := pushNot_spec n gs sel hv hs; rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hw1, he1⟩ := hs1
  rcases hr2 : pushAnd n gs1 sel a with ⟨gs2, t1⟩
  have hs2 := pushAnd_spec n gs1 sel a hv1 (by omega) (by omega); rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
  rcases hr3 : pushAnd n gs2 ns b with ⟨gs3, t2⟩
  have hs3 := pushAnd_spec n gs2 ns b hv2 (by omega) (by omega); rw [hr3] at hs3; dsimp only at hs3
  obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
  rcases hr4 : pushOr n gs3 t1 t2 with ⟨gs4, out⟩
  have hs4 := pushOr_spec n gs3 t1 t2 hv3 (by omega) hw3; rw [hr4] at hs4; dsimp only at hs4
  obtain ⟨hv4, hp4, hl4, hw4, he4⟩ := hs4
  dsimp only
  refine ⟨hv4, hp1.trans (hp2.trans (hp3.trans hp4)), by omega, hw4, fun x hx => ?_⟩
  rw [he4 x hx]
  rw [wireVal_prefix x hp3 (by omega), he2 x hx]
  rw [wireVal_prefix x hp1 (by omega), wireVal_prefix x hp1 (by omega)]
  rw [he3 x hx, wireVal_prefix x hp2 (by omega), he1 x hx]
  rw [wireVal_prefix x (hp1.trans hp2) (by omega)]
  cases wireVal x gs sel <;> cases wireVal x gs a <;> cases wireVal x gs b <;> rfl

def pushFA (n : ℕ) (gs : List Gate) (a b cin : ℕ) : List Gate × ℕ × ℕ :=
  let r1 := pushXor n gs a b
  let r2 := pushXor n r1.1 r1.2 cin
  let r3 := pushAnd n r2.1 a b
  let r4 := pushAnd n r3.1 r1.2 cin
  let r5 := pushOr n r4.1 r3.2 r4.2
  (r5.1, r2.2, r5.2)

lemma pushFA_spec (n : ℕ) (gs : List Gate) (a b cin : ℕ)
    (hv : ValidGates n gs) (ha : a < n + gs.length) (hb : b < n + gs.length) (hc : cin < n + gs.length) :
    let res := pushFA n gs a b cin
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 11 ∧
    res.2.1 < n + res.1.length ∧ res.2.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      b2n (wireVal x res.1 res.2.1) + 2 * b2n (wireVal x res.1 res.2.2) =
        b2n (wireVal x gs a) + b2n (wireVal x gs b) + b2n (wireVal x gs cin) := by
  dsimp only [pushFA]
  rcases hr1 : pushXor n gs a b with ⟨gs1, xw⟩
  have hs1 := pushXor_spec n gs a b hv ha hb; rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hw1, he1⟩ := hs1
  rcases hr2 : pushXor n gs1 xw cin with ⟨gs2, sw⟩
  have hs2 := pushXor_spec n gs1 xw cin hv1 hw1 (by omega); rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
  rcases hr3 : pushAnd n gs2 a b with ⟨gs3, ab⟩
  have hs3 := pushAnd_spec n gs2 a b hv2 (by omega) (by omega); rw [hr3] at hs3; dsimp only at hs3
  obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
  rcases hr4 : pushAnd n gs3 xw cin with ⟨gs4, xc⟩
  have hs4 := pushAnd_spec n gs3 xw cin hv3 (by omega) (by omega); rw [hr4] at hs4; dsimp only at hs4
  obtain ⟨hv4, hp4, hl4, hw4, he4⟩ := hs4
  rcases hr5 : pushOr n gs4 ab xc with ⟨gs5, co⟩
  have hs5 := pushOr_spec n gs4 ab xc hv4 (by omega) hw4; rw [hr5] at hs5; dsimp only at hs5
  obtain ⟨hv5, hp5, hl5, hw5, he5⟩ := hs5
  dsimp only
  refine ⟨hv5, hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5))), by omega, by omega, hw5, fun x hx => ?_⟩
  have hsw : wireVal x gs5 sw = xor (xor (wireVal x gs a) (wireVal x gs b)) (wireVal x gs cin) := by
    rw [wireVal_prefix x (hp3.trans (hp4.trans hp5)) (by omega), he2 x hx, he1 x hx,
      wireVal_prefix x hp1 (by omega)]
  have hco : wireVal x gs5 co =
      ((wireVal x gs a && wireVal x gs b) ||
        (xor (wireVal x gs a) (wireVal x gs b) && wireVal x gs cin)) := by
    rw [he5 x hx]
    rw [wireVal_prefix x hp4 (by omega), he3 x hx]
    rw [wireVal_prefix x (hp1.trans hp2) (by omega), wireVal_prefix x (hp1.trans hp2) (by omega)]
    rw [he4 x hx, wireVal_prefix x (hp2.trans hp3) (by omega), he1 x hx]
    rw [wireVal_prefix x (hp1.trans (hp2.trans hp3)) (by omega)]
  rw [hsw, hco]
  cases wireVal x gs a <;> cases wireVal x gs b <;> cases wireVal x gs cin <;> decide

def vecVal (x : List Bool) (gs : List Gate) {m : ℕ} (v : Fin m → ℕ) : ℕ :=
  natOf (fun i => wireVal x gs (v i))

lemma vecVal_prefix (x : List Bool) {gs1 gs2 : List Gate} (h : gs1 <+: gs2) {m : ℕ}
    (v : Fin m → ℕ) (hv : ∀ i, v i < x.length + gs1.length) :
    vecVal x gs2 v = vecVal x gs1 v := by
  dsimp only [vecVal, natOf]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [wireVal_prefix x h (hv i)]

def pushNotVec (n : ℕ) : (m : ℕ) → List Gate → (Fin m → ℕ) → List Gate × (Fin m → ℕ)
  | 0, gs, _ => (gs, Fin.elim0)
  | m + 1, gs, v =>
    let r1 := pushNotVec n m gs (fun i => v i.castSucc)
    let r2 := pushNot n r1.1 (v (Fin.last m))
    (r2.1, Fin.snoc r1.2 r2.2)

lemma pushNotVec_spec (n m : ℕ) (gs : List Gate) (v : Fin m → ℕ)
    (hv : ValidGates n gs) (hvb : ∀ i, v i < n + gs.length) :
    let res := pushNotVec n m gs v
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + m ∧
    (∀ i, res.2 i < n + res.1.length) ∧
    ∀ x : List Bool, x.length = n →
      vecVal x res.1 res.2 + vecVal x gs v = 2 ^ m - 1 := by
  induction m generalizing gs with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [pushNotVec], fun i => i.elim0, fun x _ => ?_⟩
    simp [pushNotVec, vecVal, natOf]
  | succ m ih =>
    dsimp only [pushNotVec]
    rcases hr1 : pushNotVec n m gs (fun i => v i.castSucc) with ⟨gs1, out1⟩
    have hs1 := ih gs (fun i => v i.castSucc) hv (fun i => hvb i.castSucc)
    rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hvb1, he1⟩ := hs1
    rcases hr2 : pushNot n gs1 (v (Fin.last m)) with ⟨gs2, w⟩
    have hs2 := pushNot_spec n gs1 (v (Fin.last m)) hv1 (by have := hvb (Fin.last m); omega)
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
    dsimp only
    refine ⟨hv2, hp1.trans hp2, by omega, fun i => ?_, fun x hx => ?_⟩
    · refine Fin.lastCases ?_ ?_ i
      · simpa using hw2
      · intro j; simp only [Fin.snoc_castSucc]; have := hvb1 j; omega
    · have h1 : vecVal x gs2 (Fin.snoc out1 w) =
          vecVal x gs1 out1 + if !(wireVal x gs (v (Fin.last m))) then 2 ^ m else 0 := by
        dsimp only [vecVal, natOf]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hw := wireVal_prefix x hp2 (k := out1 j) (by have := hvb1 j; omega)
          simp [hw]
        · have hw := wireVal_prefix x hp1 (k := v (Fin.last m)) (by have := hvb (Fin.last m); omega)
          simp [he2 x hx, hw]
      have h2 : vecVal x gs v =
          vecVal x gs (fun i : Fin m => v i.castSucc) +
          if wireVal x gs (v (Fin.last m)) then 2 ^ m else 0 := by
        simp only [vecVal, natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
      rw [h1, h2]
      have hih := he1 x hx
      have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      cases wireVal x gs (v (Fin.last m)) <;> simp [pow_succ] <;> omega

def pushMuxVec (n : ℕ) : (m : ℕ) → List Gate → ℕ → (Fin m → ℕ) → (Fin m → ℕ) →
    List Gate × (Fin m → ℕ)
  | 0, gs, _, _, _ => (gs, Fin.elim0)
  | m + 1, gs, sel, a, b =>
    let r1 := pushMuxVec n m gs sel (fun i => a i.castSucc) (fun i => b i.castSucc)
    let r2 := pushMux n r1.1 sel (a (Fin.last m)) (b (Fin.last m))
    (r2.1, Fin.snoc r1.2 r2.2)

lemma pushMuxVec_spec (n m : ℕ) (gs : List Gate) (sel : ℕ) (a b : Fin m → ℕ)
    (hv : ValidGates n gs) (hs : sel < n + gs.length)
    (ha : ∀ i, a i < n + gs.length) (hb : ∀ i, b i < n + gs.length) :
    let res := pushMuxVec n m gs sel a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 * m ∧
    (∀ i, res.2 i < n + res.1.length) ∧
    (∀ x : List Bool, x.length = n → ∀ i : Fin m,
      wireVal x res.1 (res.2 i) =
        if wireVal x gs sel then wireVal x gs (a i) else wireVal x gs (b i)) ∧
    ∀ x : List Bool, x.length = n →
      vecVal x res.1 res.2 = if wireVal x gs sel then vecVal x gs a else vecVal x gs b := by
  have hcore : let res := pushMuxVec n m gs sel a b
      ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 * m ∧
      (∀ i, res.2 i < n + res.1.length) ∧
      ∀ x : List Bool, x.length = n → ∀ i : Fin m,
        wireVal x res.1 (res.2 i) =
          if wireVal x gs sel then wireVal x gs (a i) else wireVal x gs (b i) := by
    induction m generalizing gs with
    | zero =>
      refine ⟨hv, List.prefix_refl _, by simp [pushMuxVec], fun i => i.elim0, fun _ _ i => i.elim0⟩
    | succ m ih =>
      dsimp only [pushMuxVec]
      rcases hr1 : pushMuxVec n m gs sel (fun i => a i.castSucc) (fun i => b i.castSucc) with ⟨gs1, out1⟩
      have hs1 := ih gs (fun i => a i.castSucc) (fun i => b i.castSucc)
        hv hs (fun i => ha i.castSucc) (fun i => hb i.castSucc)
      rw [hr1] at hs1; dsimp only at hs1
      obtain ⟨hv1, hp1, hl1, hvb1, he1⟩ := hs1
      rcases hr2 : pushMux n gs1 sel (a (Fin.last m)) (b (Fin.last m)) with ⟨gs2, w⟩
      have hs2 := pushMux_spec n gs1 sel (a (Fin.last m)) (b (Fin.last m))
        hv1 (by omega) (by have := ha (Fin.last m); omega) (by have := hb (Fin.last m); omega)
      rw [hr2] at hs2; dsimp only at hs2
      obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
      dsimp only
      refine ⟨hv2, hp1.trans hp2, by omega, fun i => ?_, fun x hx i => ?_⟩
      · refine Fin.lastCases ?_ ?_ i
        · simpa using hw2
        · intro j; simp only [Fin.snoc_castSucc]; have := hvb1 j; omega
      · refine Fin.lastCases ?_ ?_ i
        · simp only [Fin.snoc_last]
          rw [he2 x hx]
          rw [wireVal_prefix x hp1 (by omega),
            wireVal_prefix x hp1 (by have := ha (Fin.last m); omega),
            wireVal_prefix x hp1 (by have := hb (Fin.last m); omega)]
        · intro j
          simp only [Fin.snoc_castSucc]
          rw [wireVal_prefix x hp2 (by have := hvb1 j; omega)]
          exact he1 x hx j
  obtain ⟨hv1, hp1, hl1, hout, he⟩ := hcore
  refine ⟨hv1, hp1, hl1, hout, he, fun x hx => ?_⟩
  cases hsel : wireVal x gs sel <;>
  · dsimp only [vecVal, natOf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [he x hx i, hsel]

def pushAddVec (n : ℕ) : (m : ℕ) → List Gate → (Fin m → ℕ) → (Fin m → ℕ) → ℕ →
    List Gate × (Fin m → ℕ) × ℕ
  | 0, gs, _, _, cin => (gs, Fin.elim0, cin)
  | m + 1, gs, a, b, cin =>
    let r1 := pushAddVec n m gs (fun i => a i.castSucc) (fun i => b i.castSucc) cin
    let r2 := pushFA n r1.1 (a (Fin.last m)) (b (Fin.last m)) r1.2.2
    (r2.1, Fin.snoc r1.2.1 r2.2.1, r2.2.2)

lemma pushAddVec_spec (n m : ℕ) (gs : List Gate) (a b : Fin m → ℕ) (cin : ℕ)
    (hv : ValidGates n gs) (ha : ∀ i, a i < n + gs.length) (hb : ∀ i, b i < n + gs.length)
    (hc : cin < n + gs.length) :
    let res := pushAddVec n m gs a b cin
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 11 * m ∧
    (∀ i, res.2.1 i < n + res.1.length) ∧ res.2.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n →
      vecVal x res.1 res.2.1 + b2n (wireVal x res.1 res.2.2) * 2 ^ m =
        vecVal x gs a + vecVal x gs b + b2n (wireVal x gs cin) := by
  induction m generalizing gs with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [pushAddVec], fun i => i.elim0, hc, fun x _ => ?_⟩
    simp [pushAddVec, vecVal, natOf]
  | succ m ih =>
    dsimp only [pushAddVec]
    rcases hr1 : pushAddVec n m gs (fun i => a i.castSucc) (fun i => b i.castSucc) cin with ⟨gs1, out1, c1⟩
    have hs1 := ih gs (fun i => a i.castSucc) (fun i => b i.castSucc)
      hv (fun i => ha i.castSucc) (fun i => hb i.castSucc) hc
    rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hvb1, hc1, he1⟩ := hs1
    rcases hr2 : pushFA n gs1 (a (Fin.last m)) (b (Fin.last m)) c1 with ⟨gs2, sw, co⟩
    have hs2 := pushFA_spec n gs1 (a (Fin.last m)) (b (Fin.last m)) c1
      hv1 (by have := ha (Fin.last m); omega) (by have := hb (Fin.last m); omega) hc1
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hsw, hco, he2⟩ := hs2
    dsimp only
    refine ⟨hv2, hp1.trans hp2, by omega, fun i => ?_, hco, fun x hx => ?_⟩
    · refine Fin.lastCases ?_ ?_ i
      · simpa using hsw
      · intro j; simp only [Fin.snoc_castSucc]; have := hvb1 j; omega
    · have hsnoc : vecVal x gs2 (Fin.snoc out1 sw) =
          vecVal x gs1 out1 + b2n (wireVal x gs2 sw) * 2 ^ m := by
        dsimp only [vecVal, natOf]
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        congr 1
        · refine Finset.sum_congr rfl fun j _ => ?_
          have hw := wireVal_prefix x hp2 (k := out1 j) (by have := hvb1 j; omega)
          simp [hw]
        · cases wireVal x gs2 sw <;> simp [b2n]
      have ha_sp : vecVal x gs a =
          vecVal x gs (fun i : Fin m => a i.castSucc) +
            b2n (wireVal x gs (a (Fin.last m))) * 2 ^ m := by
        simp only [vecVal, natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        cases wireVal x gs (a (Fin.last m)) <;> simp [b2n]
      have hb_sp : vecVal x gs b =
          vecVal x gs (fun i : Fin m => b i.castSucc) +
            b2n (wireVal x gs (b (Fin.last m))) * 2 ^ m := by
        simp only [vecVal, natOf, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]
        cases wireVal x gs (b (Fin.last m)) <;> simp [b2n]
      have hfa := he2 x hx
      rw [wireVal_prefix x hp1 (by have := ha (Fin.last m); omega),
        wireVal_prefix x hp1 (by have := hb (Fin.last m); omega)] at hfa
      have hih := he1 x hx
      rw [hsnoc, ha_sp, hb_sp, pow_succ]
      have hmul := congrArg (· * 2 ^ m) hfa
      linarith

def pushSubVec (n m : ℕ) (gs : List Gate) (cT : ℕ) (a b : Fin m → ℕ) :
    List Gate × (Fin m → ℕ) × ℕ :=
  let r1 := pushNotVec n m gs b
  pushAddVec n m r1.1 a r1.2 cT

lemma pushSubVec_spec (n m : ℕ) (gs : List Gate) (cT : ℕ) (a b : Fin m → ℕ)
    (hv : ValidGates n gs) (hcT : cT < n + gs.length)
    (ha : ∀ i, a i < n + gs.length) (hb : ∀ i, b i < n + gs.length) :
    let res := pushSubVec n m gs cT a b
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 12 * m ∧
    (∀ i, res.2.1 i < n + res.1.length) ∧ res.2.2 < n + res.1.length ∧
    ∀ x : List Bool, x.length = n → wireVal x gs cT = true →
      wireVal x res.1 res.2.2 = decide (vecVal x gs b ≤ vecVal x gs a) ∧
      (vecVal x gs b ≤ vecVal x gs a → vecVal x res.1 res.2.1 = vecVal x gs a - vecVal x gs b) := by
  dsimp only [pushSubVec]
  rcases hr1 : pushNotVec n m gs b with ⟨gs1, nb⟩
  have hs1 := pushNotVec_spec n m gs b hv hb; rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hnb, hnot⟩ := hs1
  rcases hr2 : pushAddVec n m gs1 a nb cT with ⟨gs2, dv, co⟩
  have hs2 := pushAddVec_spec n m gs1 a nb cT hv1 (fun i => by have := ha i; omega) hnb (by omega)
  rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hdv, hco, hsum⟩ := hs2
  dsimp only
  refine ⟨hv2, hp1.trans hp2, by omega, hdv, hco, fun x hx hct => ?_⟩
  have h1 := hsum x hx
  have h2 := hnot x hx
  have ha1 : vecVal x gs1 a = vecVal x gs a :=
    vecVal_prefix x hp1 a (fun i => by have := ha i; omega)
  have hct1 : wireVal x gs1 cT = true := by
    rw [wireVal_prefix x hp1 (by omega), hct]
  rw [ha1, hct1] at h1
  have hltD : vecVal x gs2 dv < 2 ^ m := natOf_lt _
  have hltA : vecVal x gs a < 2 ^ m := natOf_lt _
  have hltB : vecVal x gs b < 2 ^ m := natOf_lt _
  have hpow : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have hrel : vecVal x gs2 dv + b2n (wireVal x gs2 co) * 2 ^ m + vecVal x gs b =
      vecVal x gs a + 2 ^ m := by
    have hb1 : b2n true = 1 := rfl
    rw [hb1] at h1
    omega
  cases hbit : wireVal x gs2 co
  · rw [hbit] at hrel
    simp only [b2n, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero] at hrel
    have hlt : vecVal x gs a < vecVal x gs b := by omega
    refine ⟨by simp [not_le.mpr hlt], fun hle => by omega⟩
  · rw [hbit] at hrel
    simp only [b2n, ↓reduceIte, one_mul] at hrel
    have hle : vecVal x gs b ≤ vecVal x gs a := by omega
    refine ⟨by simp [hle], fun _ => by omega⟩

def pushSelectVecAux (n q w : ℕ) (cF : ℕ) (oh : Fin q → ℕ) (vecs : Fin q → Fin w → ℕ) :
    (r : ℕ) → r ≤ q → List Gate → List Gate × (Fin w → ℕ)
  | 0, _, gs => (gs, fun _ => cF)
  | r + 1, hr, gs =>
    let r1 := pushSelectVecAux n q w cF oh vecs r (Nat.le_of_succ_le hr) gs
    pushMuxVec n w r1.1 (oh ⟨r, hr⟩) (vecs ⟨r, hr⟩) r1.2

lemma pushSelectVecAux_spec (n q w : ℕ) (cF : ℕ) (oh : Fin q → ℕ) (vecs : Fin q → Fin w → ℕ)
    (r : ℕ) (hr : r ≤ q) (gs : List Gate)
    (hv : ValidGates n gs) (hcF : cF < n + gs.length)
    (hoh : ∀ s, oh s < n + gs.length) (hvecs : ∀ s i, vecs s i < n + gs.length) :
    let res := pushSelectVecAux n q w cF oh vecs r hr gs
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 * r * w ∧
    (∀ i, res.2 i < n + res.1.length) ∧
    ∀ (x : List Bool), x.length = n → wireVal x gs cF = false →
      ∀ (cur : Fin q), (∀ s : Fin q, wireVal x gs (oh s) = decide (s = cur)) →
      vecVal x res.1 res.2 = if cur.val < r then vecVal x gs (vecs cur) else 0 := by
  induction r with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [pushSelectVecAux], fun _ => hcF, fun x _ hcf _ _ => ?_⟩
    simp [pushSelectVecAux, vecVal, natOf, hcf]
  | succ r ih =>
    dsimp only [pushSelectVecAux]
    rcases hr1 : pushSelectVecAux n q w cF oh vecs r (Nat.le_of_succ_le hr) gs with ⟨gs1, acc1⟩
    have hs1 := ih (Nat.le_of_succ_le hr); rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hacc, he1⟩ := hs1
    rcases hr2 : pushMuxVec n w gs1 (oh ⟨r, hr⟩) (vecs ⟨r, hr⟩) acc1 with ⟨gs2, out2⟩
    have hs2 := pushMuxVec_spec n w gs1 (oh ⟨r, hr⟩) (vecs ⟨r, hr⟩) acc1
      hv1 (by have := hoh ⟨r, hr⟩; omega) (fun i => by have := hvecs ⟨r, hr⟩ i; omega) hacc
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hout, _, hvv2⟩ := hs2
    dsimp only
    refine ⟨hv2, hp1.trans hp2, by rw [hl2, hl1]; ring, hout, fun x hx hcf cur hcur => ?_⟩
    rw [hvv2 x hx]
    rw [wireVal_prefix x hp1 (by have := hoh ⟨r, hr⟩; omega), hcur ⟨r, hr⟩]
    rw [vecVal_prefix x hp1 (vecs ⟨r, hr⟩) (fun i => by have := hvecs ⟨r, hr⟩ i; omega)]
    rw [he1 x hx hcf cur hcur]
    by_cases hrc : (⟨r, hr⟩ : Fin q) = cur
    · subst hrc
      simp
    · have hne : cur.val ≠ r := fun he => hrc (Fin.ext he.symm)
      have hiff : (cur.val < r + 1) ↔ (cur.val < r) := by omega
      simp [hrc, hiff]

def pushSelectVec (n q w : ℕ) (gs : List Gate) (cF : ℕ) (oh : Fin q → ℕ)
    (vecs : Fin q → Fin w → ℕ) : List Gate × (Fin w → ℕ) :=
  pushSelectVecAux n q w cF oh vecs q (le_refl q) gs

lemma pushSelectVec_spec (n q w : ℕ) (gs : List Gate) (cF : ℕ) (oh : Fin q → ℕ)
    (vecs : Fin q → Fin w → ℕ)
    (hv : ValidGates n gs) (hcF : cF < n + gs.length)
    (hoh : ∀ s, oh s < n + gs.length) (hvecs : ∀ s i, vecs s i < n + gs.length) :
    let res := pushSelectVec n q w gs cF oh vecs
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 4 * q * w ∧
    (∀ i, res.2 i < n + res.1.length) ∧
    ∀ (x : List Bool), x.length = n → wireVal x gs cF = false →
      ∀ (cur : Fin q), (∀ s : Fin q, wireVal x gs (oh s) = decide (s = cur)) →
      vecVal x res.1 res.2 = vecVal x gs (vecs cur) := by
  obtain ⟨hv1, hp1, hl1, hout, he1⟩ :=
    pushSelectVecAux_spec n q w cF oh vecs q (le_refl q) gs hv hcF hoh hvecs
  refine ⟨hv1, hp1, hl1, hout, fun x hx hcf cur hcur => ?_⟩
  simpa [pushSelectVec, cur.isLt] using he1 x hx hcf cur hcur

def pushNextOhTargetAux {l q : ℕ} (n : ℕ) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (mFF mFT mTF mTT : ℕ) (s' : Fin q) :
    (r : ℕ) → r ≤ q → List Gate → List Gate × ℕ
  | 0, _, gs => (gs, cF)
  | r + 1, hr, gs =>
    let r1 := pushNextOhTargetAux n cF step k oh mFF mFT mTF mTT s' r (Nat.le_of_succ_le hr) gs
    let s : Fin q := ⟨r, hr⟩
    let t0 := if step k s false false = s' then mFF else cF
    let t1 := if step k s false true = s' then mFT else cF
    let t2 := if step k s true false = s' then mTF else cF
    let t3 := if step k s true true = s' then mTT else cF
    let r2 := pushOr n r1.1 t0 t1
    let r3 := pushOr n r2.1 t2 t3
    let r4 := pushOr n r3.1 r2.2 r3.2
    let r5 := pushAnd n r4.1 (oh s) r4.2
    pushOr n r5.1 r1.2 r5.2

lemma pushNextOhTargetAux_spec {l q : ℕ} (n : ℕ) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (mFF mFT mTF mTT : ℕ) (s' : Fin q)
    (r : ℕ) (hr : r ≤ q) (gs : List Gate)
    (hv : ValidGates n gs) (hcF : cF < n + gs.length)
    (hoh : ∀ s, oh s < n + gs.length)
    (hm0 : mFF < n + gs.length) (hm1 : mFT < n + gs.length)
    (hm2 : mTF < n + gs.length) (hm3 : mTT < n + gs.length) :
    let res := pushNextOhTargetAux n cF step k oh mFF mFT mTF mTT s' r hr gs
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 5 * r ∧
    res.2 < n + res.1.length ∧
    ∀ (x : List Bool), x.length = n → wireVal x gs cF = false →
      ∀ (bp bu : Bool),
        wireVal x gs mFF = (!bp && !bu) →
        wireVal x gs mFT = (!bp && bu) →
        wireVal x gs mTF = (bp && !bu) →
        wireVal x gs mTT = (bp && bu) →
      ∀ (cur : Fin q), (∀ s : Fin q, wireVal x gs (oh s) = decide (s = cur)) →
      wireVal x res.1 res.2 = decide (cur.val < r ∧ step k cur bp bu = s') := by
  induction r with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [pushNextOhTargetAux], hcF,
      fun x _ hcf _ _ _ _ _ _ _ _ => by simp [pushNextOhTargetAux, hcf]⟩
  | succ r ih =>
    dsimp only [pushNextOhTargetAux]
    rcases hr1 : pushNextOhTargetAux n cF step k oh mFF mFT mTF mTT s' r (Nat.le_of_succ_le hr) gs with ⟨gs1, acc1⟩
    have hs1 := ih (Nat.le_of_succ_le hr); rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hacc, he1⟩ := hs1
    set s : Fin q := ⟨r, hr⟩
    set t0 := if step k s false false = s' then mFF else cF
    set t1 := if step k s false true = s' then mFT else cF
    set t2 := if step k s true false = s' then mTF else cF
    set t3 := if step k s true true = s' then mTT else cF
    have ht0 : t0 < n + gs1.length := by dsimp only [t0]; split_ifs <;> omega
    have ht1 : t1 < n + gs1.length := by dsimp only [t1]; split_ifs <;> omega
    rcases hr2 : pushOr n gs1 t0 t1 with ⟨gs2, t01⟩
    have hs2 := pushOr_spec n gs1 t0 t1 hv1 ht0 ht1; rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
    have ht2 : t2 < n + gs2.length := by dsimp only [t2]; split_ifs <;> omega
    have ht3 : t3 < n + gs2.length := by dsimp only [t3]; split_ifs <;> omega
    rcases hr3 : pushOr n gs2 t2 t3 with ⟨gs3, t23⟩
    have hs3 := pushOr_spec n gs2 t2 t3 hv2 ht2 ht3; rw [hr3] at hs3; dsimp only at hs3
    obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
    rcases hr4 : pushOr n gs3 t01 t23 with ⟨gs4, tAll⟩
    have hs4 := pushOr_spec n gs3 t01 t23 hv3 (by omega) hw3; rw [hr4] at hs4; dsimp only at hs4
    obtain ⟨hv4, hp4, hl4, hw4, he4⟩ := hs4
    rcases hr5 : pushAnd n gs4 (oh s) tAll with ⟨gs5, hit⟩
    have hs5 := pushAnd_spec n gs4 (oh s) tAll hv4 (by have := hoh s; omega) hw4
    rw [hr5] at hs5; dsimp only at hs5
    obtain ⟨hv5, hp5, hl5, hw5, he5⟩ := hs5
    rcases hr6 : pushOr n gs5 acc1 hit with ⟨gs6, out6⟩
    have hs6 := pushOr_spec n gs5 acc1 hit hv5 (by omega) hw5; rw [hr6] at hs6; dsimp only at hs6
    obtain ⟨hv6, hp6, hl6, hw6, he6⟩ := hs6
    dsimp only
    refine ⟨hv6, hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans hp6)))), by omega, hw6,
      fun x hx hcf bp bu h0 h1 h2 h3 cur hcur => ?_⟩
    rw [he6 x hx, wireVal_prefix x (hp2.trans (hp3.trans (hp4.trans hp5))) (by omega)]
    rw [he1 x hx hcf bp bu h0 h1 h2 h3 cur hcur]
    rw [he5 x hx, wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans hp4))) (by have := hoh s; omega), hcur s]
    rw [he4 x hx, wireVal_prefix x hp3 (by omega), he2 x hx, he3 x hx]
    have ht0v : wireVal x gs1 t0 = (if step k s false false = s' then (!bp && !bu) else false) := by
      dsimp only [t0]; split_ifs
      · rw [wireVal_prefix x hp1 (by omega), h0]
      · rw [wireVal_prefix x hp1 (by omega), hcf]
    have ht1v : wireVal x gs1 t1 = (if step k s false true = s' then (!bp && bu) else false) := by
      dsimp only [t1]; split_ifs
      · rw [wireVal_prefix x hp1 (by omega), h1]
      · rw [wireVal_prefix x hp1 (by omega), hcf]
    have ht2v : wireVal x gs2 t2 = (if step k s true false = s' then (bp && !bu) else false) := by
      dsimp only [t2]; split_ifs
      · rw [wireVal_prefix x (hp1.trans hp2) (by omega), h2]
      · rw [wireVal_prefix x (hp1.trans hp2) (by omega), hcf]
    have ht3v : wireVal x gs2 t3 = (if step k s true true = s' then (bp && bu) else false) := by
      dsimp only [t3]; split_ifs
      · rw [wireVal_prefix x (hp1.trans hp2) (by omega), h3]
      · rw [wireVal_prefix x (hp1.trans hp2) (by omega), hcf]
    rw [ht0v, ht1v, ht2v, ht3v]
    have hstepv : ((if step k s false false = s' then (!bp && !bu) else false) ||
        (if step k s false true = s' then (!bp && bu) else false) ||
        ((if step k s true false = s' then (bp && !bu) else false) ||
         (if step k s true true = s' then (bp && bu) else false))) = decide (step k s bp bu = s') := by
      cases bp <;> cases bu <;> simp
    rw [hstepv]
    by_cases hsc : s = cur
    · subst hsc
      simp [s]
    · have hne : cur.val ≠ r := fun he => hsc (Fin.ext he.symm)
      have hiff : (cur.val < r + 1) ↔ (cur.val < r) := by omega
      simp [hsc, hiff]

def pushNextOhAux {l q : ℕ} (n : ℕ) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (mFF mFT mTF mTT : ℕ) :
    (r : ℕ) → r ≤ q → List Gate → List Gate × (Fin q → ℕ)
  | 0, _, gs => (gs, fun _ => cF)
  | r + 1, hr, gs =>
    let r1 := pushNextOhAux n cF step k oh mFF mFT mTF mTT r (Nat.le_of_succ_le hr) gs
    let s' : Fin q := ⟨r, hr⟩
    let r2 := pushNextOhTargetAux n cF step k oh mFF mFT mTF mTT s' q (le_refl q) r1.1
    (r2.1, Function.update r1.2 s' r2.2)

lemma pushNextOhAux_spec {l q : ℕ} (n : ℕ) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (mFF mFT mTF mTT : ℕ)
    (r : ℕ) (hr : r ≤ q) (gs : List Gate)
    (hv : ValidGates n gs) (hcF : cF < n + gs.length)
    (hoh : ∀ s, oh s < n + gs.length)
    (hm0 : mFF < n + gs.length) (hm1 : mFT < n + gs.length)
    (hm2 : mTF < n + gs.length) (hm3 : mTT < n + gs.length) :
    let res := pushNextOhAux n cF step k oh mFF mFT mTF mTT r hr gs
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 5 * r * q ∧
    (∀ s, res.2 s < n + res.1.length) ∧
    ∀ (x : List Bool), x.length = n → wireVal x gs cF = false →
      ∀ (bp bu : Bool),
        wireVal x gs mFF = (!bp && !bu) →
        wireVal x gs mFT = (!bp && bu) →
        wireVal x gs mTF = (bp && !bu) →
        wireVal x gs mTT = (bp && bu) →
      ∀ (cur : Fin q), (∀ s : Fin q, wireVal x gs (oh s) = decide (s = cur)) →
      ∀ s' : Fin q, s'.val < r →
        wireVal x res.1 (res.2 s') = decide (s' = step k cur bp bu) := by
  induction r with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [pushNextOhAux], fun _ => hcF,
      fun _ _ _ _ _ _ _ _ _ _ _ _ hs => by omega⟩
  | succ r ih =>
    dsimp only [pushNextOhAux]
    rcases hr1 : pushNextOhAux n cF step k oh mFF mFT mTF mTT r (Nat.le_of_succ_le hr) gs with ⟨gs1, out1⟩
    have hs1 := ih (Nat.le_of_succ_le hr); rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hout1, he1⟩ := hs1
    set sr : Fin q := ⟨r, hr⟩
    rcases hr2 : pushNextOhTargetAux n cF step k oh mFF mFT mTF mTT sr q (le_refl q) gs1 with ⟨gs2, w2⟩
    have hs2 := pushNextOhTargetAux_spec n cF step k oh mFF mFT mTF mTT sr q (le_refl q) gs1
      hv1 (by omega) (fun s => by have := hoh s; omega) (by omega) (by omega) (by omega) (by omega)
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
    dsimp only
    refine ⟨hv2, hp1.trans hp2, by rw [hl2, hl1]; ring, fun s => ?_,
      fun x hx hcf bp bu h0 h1 h2 h3 cur hcur s' hs' => ?_⟩
    · by_cases hsr : s = sr
      · subst hsr; simpa using hw2
      · rw [Function.update_of_ne hsr]; have := hout1 s; omega
    · by_cases hsr : s' = sr
      · subst hsr
        simp only [Function.update_self]
        rw [he2 x hx
          (by rw [wireVal_prefix x hp1 (by omega), hcf]) bp bu
          (by rw [wireVal_prefix x hp1 (by omega), h0])
          (by rw [wireVal_prefix x hp1 (by omega), h1])
          (by rw [wireVal_prefix x hp1 (by omega), h2])
          (by rw [wireVal_prefix x hp1 (by omega), h3])
          cur (fun s => by rw [wireVal_prefix x hp1 (by have := hoh s; omega), hcur s])]
        simp [cur.isLt, eq_comm]
      · rw [Function.update_of_ne hsr]
        rw [wireVal_prefix x hp2 (by have := hout1 s'; omega)]
        have hlt : s'.val < r := by
          have : s'.val ≠ r := fun he => hsr (Fin.ext he)
          omega
        exact he1 x hx hcf bp bu h0 h1 h2 h3 cur hcur s' hlt

def pushNextOh {l q : ℕ} (n : ℕ) (gs : List Gate) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (pw uw : ℕ) : List Gate × (Fin q → ℕ) :=
  let r1 := pushNot n gs pw
  let r2 := pushNot n r1.1 uw
  let r3 := pushAnd n r2.1 r1.2 r2.2
  let r4 := pushAnd n r3.1 r1.2 uw
  let r5 := pushAnd n r4.1 pw r2.2
  let r6 := pushAnd n r5.1 pw uw
  pushNextOhAux n cF step k oh r3.2 r4.2 r5.2 r6.2 q (le_refl q) r6.1

lemma pushNextOh_spec {l q : ℕ} (n : ℕ) (gs : List Gate) (cF : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (k : Fin l)
    (oh : Fin q → ℕ) (pw uw : ℕ)
    (hv : ValidGates n gs) (hcF : cF < n + gs.length)
    (hoh : ∀ s, oh s < n + gs.length) (hpw : pw < n + gs.length) (huw : uw < n + gs.length) :
    let res := pushNextOh n gs cF step k oh pw uw
    ValidGates n res.1 ∧ gs <+: res.1 ∧ res.1.length = gs.length + 6 + 5 * q * q ∧
    (∀ s, res.2 s < n + res.1.length) ∧
    ∀ (x : List Bool), x.length = n → wireVal x gs cF = false →
      ∀ (cur : Fin q), (∀ s : Fin q, wireVal x gs (oh s) = decide (s = cur)) →
      ∀ s' : Fin q, wireVal x res.1 (res.2 s') =
        decide (s' = step k cur (wireVal x gs pw) (wireVal x gs uw)) := by
  dsimp only [pushNextOh]
  rcases hr1 : pushNot n gs pw with ⟨gs1, np⟩
  have hs1 := pushNot_spec n gs pw hv hpw; rw [hr1] at hs1; dsimp only at hs1
  obtain ⟨hv1, hp1, hl1, hw1, he1⟩ := hs1
  rcases hr2 : pushNot n gs1 uw with ⟨gs2, nu⟩
  have hs2 := pushNot_spec n gs1 uw hv1 (by omega); rw [hr2] at hs2; dsimp only at hs2
  obtain ⟨hv2, hp2, hl2, hw2, he2⟩ := hs2
  rcases hr3 : pushAnd n gs2 np nu with ⟨gs3, mFF⟩
  have hs3 := pushAnd_spec n gs2 np nu hv2 (by omega) hw2; rw [hr3] at hs3; dsimp only at hs3
  obtain ⟨hv3, hp3, hl3, hw3, he3⟩ := hs3
  rcases hr4 : pushAnd n gs3 np uw with ⟨gs4, mFT⟩
  have hs4 := pushAnd_spec n gs3 np uw hv3 (by omega) (by omega); rw [hr4] at hs4; dsimp only at hs4
  obtain ⟨hv4, hp4, hl4, hw4, he4⟩ := hs4
  rcases hr5 : pushAnd n gs4 pw nu with ⟨gs5, mTF⟩
  have hs5 := pushAnd_spec n gs4 pw nu hv4 (by omega) (by omega); rw [hr5] at hs5; dsimp only at hs5
  obtain ⟨hv5, hp5, hl5, hw5, he5⟩ := hs5
  rcases hr6 : pushAnd n gs5 pw uw with ⟨gs6, mTT⟩
  have hs6 := pushAnd_spec n gs5 pw uw hv5 (by omega) (by omega); rw [hr6] at hs6; dsimp only at hs6
  obtain ⟨hv6, hp6, hl6, hw6, he6⟩ := hs6
  have hp16 : gs <+: gs6 := hp1.trans (hp2.trans (hp3.trans (hp4.trans (hp5.trans hp6))))
  rcases hr7 : pushNextOhAux n cF step k oh mFF mFT mTF mTT q (le_refl q) gs6 with ⟨gs7, out7⟩
  have hs7 := pushNextOhAux_spec n cF step k oh mFF mFT mTF mTT q (le_refl q) gs6
    hv6 (by omega) (fun s => by have := hoh s; omega) (by omega) (by omega) (by omega) hw6
  rw [hr7] at hs7; dsimp only at hs7
  obtain ⟨hv7, hp7, hl7, hout7, he7⟩ := hs7
  dsimp only
  refine ⟨hv7, hp16.trans hp7, by omega, hout7, fun x hx hcf cur hcur s' => ?_⟩
  have hmFF : wireVal x gs6 mFF = (!(wireVal x gs pw) && !(wireVal x gs uw)) := by
    rw [wireVal_prefix x (hp4.trans (hp5.trans hp6)) (by omega), he3 x hx,
      wireVal_prefix x hp2 (by omega), he1 x hx, he2 x hx, wireVal_prefix x hp1 (by omega)]
  have hmFT : wireVal x gs6 mFT = (!(wireVal x gs pw) && wireVal x gs uw) := by
    rw [wireVal_prefix x (hp5.trans hp6) (by omega), he4 x hx,
      wireVal_prefix x (hp2.trans hp3) (by omega), he1 x hx,
      wireVal_prefix x (hp1.trans (hp2.trans hp3)) (by omega)]
  have hmTF : wireVal x gs6 mTF = (wireVal x gs pw && !(wireVal x gs uw)) := by
    rw [wireVal_prefix x hp6 (by omega), he5 x hx,
      wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans hp4))) (by omega),
      wireVal_prefix x (hp3.trans hp4) (by omega), he2 x hx, wireVal_prefix x hp1 (by omega)]
  have hmTT : wireVal x gs6 mTT = (wireVal x gs pw && wireVal x gs uw) := by
    rw [he6 x hx,
      wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5)))) (by omega),
      wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5)))) (by omega)]
  exact he7 x hx (by rw [wireVal_prefix x hp16 (by omega), hcf])
    (wireVal x gs pw) (wireVal x gs uw) hmFF hmFT hmTF hmTT cur
    (fun s => by rw [wireVal_prefix x hp16 (by have := hoh s; omega), hcur s])
    s' s'.isLt

def fixedWord (l : ℕ) : Fin l → Bool := fun _ => false

def countWires {l q : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (j : Fin l) (s : Fin q) (i : Fin (l + 1)) : ℕ :=
  if (zeroCount step final (fixedWord l) j s).testBit i.val then cT else cF

lemma countWires_lt {l q n : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (hF : cF < n) (hT : cT < n) (j : Fin l) (s : Fin q) (i : Fin (l + 1)) :
    countWires cF cT step final j s i < n := by
  unfold countWires
  split_ifs <;> assumption

lemma countWires_value {l q : ℕ} {x : List Bool} {gs : List Gate} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (final : Fin q → Bool)
    (hF : wireVal x gs cF = false) (hT : wireVal x gs cT = true)
    (j : Fin l) (s : Fin q) :
    vecVal x gs (countWires cF cT step final j s) = zeroCount step final (fixedWord l) j s := by
  let count := zeroCount step final (fixedWord l) j s
  have hbound : count < 2 ^ (l + 1) := by
    have hd : l - 1 - j.val ≤ l := by omega
    have hle : count ≤ 2 ^ (l - 1 - j.val) := by
      unfold count zeroCount
      exact dpVal_le step final (fixedWord l) _ _ _
    exact hle.trans_lt (Nat.pow_lt_pow_right (by omega) (by omega))
  change vecVal x gs (countWires cF cT step final j s) = count
  rw [← natOf_testBit (l + 1) count hbound]
  change natOf (fun i : Fin (l + 1) => wireVal x gs (countWires cF cT step final j s i)) =
    natOf (fun i : Fin (l + 1) => count.testBit i.val)
  congr 1
  funext i
  unfold countWires
  cases hi : count.testBit i.val <;>
    simp [show zeroCount step final (fixedWord l) j s = count from rfl, hi, hF, hT]

def initOh {q : ℕ} (cF cT : ℕ) (start : Fin q) : Fin q → ℕ :=
  fun s => if s = start then cT else cF

def initRem (l cF : ℕ) : Fin (l + 1) → ℕ :=
  fun i => if i.val < l then i.val else cF

def buildEncLoop {l q : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (c0 : Fin l → Fin q → Fin (l + 1) → ℕ) :
    (k : ℕ) → k ≤ l → List Gate →
      List Gate × (Fin q → ℕ) × (Fin (l + 1) → ℕ) × (Fin l → ℕ)
  | 0, _, gs => (gs, initOh cF cT start, initRem l cF, fun _ => cF)
  | k + 1, hk, gs =>
    let r1 := buildEncLoop cF cT step start c0 k (Nat.le_of_succ_le hk) gs
    let kj : Fin l := ⟨k, hk⟩
    let r2 := pushSelectVec l q (l + 1) r1.1 cF r1.2.1 (c0 kj)
    let r3 := pushSubVec l (l + 1) r2.1 cT r1.2.2.1 r2.2
    let r4 := pushMuxVec l (l + 1) r3.1 r3.2.2 r3.2.1 r1.2.2.1
    let r5 := pushNextOh l r4.1 cF step kj r1.2.1 cF r3.2.2
    (r5.1, r5.2, r4.2, Function.update r1.2.2.2 kj r3.2.2)

lemma buildEncLoop_spec {l q : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q) (final : Fin q → Bool)
    (c0 : Fin l → Fin q → Fin (l + 1) → ℕ)
    (k : ℕ) (hk : k ≤ l) (gs : List Gate)
    (hv : ValidGates l gs) (hcF : cF < l + gs.length) (hcT : cT < l + gs.length)
    (hc0 : ∀ j s i, c0 j s i < l + gs.length) :
    let res := buildEncLoop cF cT step start c0 k hk gs
    ValidGates l res.1 ∧ gs <+: res.1 ∧
    res.1.length = gs.length + k * (4 * q * (l + 1) + 16 * (l + 1) + 6 + 5 * q * q) ∧
    (∀ s, res.2.1 s < l + res.1.length) ∧
    (∀ i, res.2.2.1 i < l + res.1.length) ∧
    (∀ j, res.2.2.2 j < l + res.1.length) ∧
    let p := fixedWord l
    ∀ (r : Fin (goodSet step start final p).card),
      let idx := fun i : Fin l => r.val.testBit i.val
      let x := List.ofFn idx
      wireVal x gs cF = false →
      wireVal x gs cT = true →
      (∀ j s, vecVal x gs (c0 j s) = zeroCount step final p j s) →
      let er := encRun step start final p r.val k hk
      (∀ s, wireVal x res.1 (res.2.1 s) = decide (s = er.1)) ∧
      vecVal x res.1 res.2.2.1 = er.2.1 ∧
      ∀ j : Fin l, j.val < k → wireVal x res.1 (res.2.2.2 j) = er.2.2 j := by
  induction k with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [buildEncLoop],
      fun s => by dsimp only [buildEncLoop, initOh]; split_ifs <;> omega,
      fun i => by dsimp only [buildEncLoop, initRem]; split_ifs <;> omega,
      fun _ => hcF, fun r hcf hct _ => ?_⟩
    let p := fixedWord l
    set idx := fun i : Fin l => r.val.testBit i.val
    set x := List.ofFn idx
    refine ⟨fun s => ?_, ?_, fun _ hj => by omega⟩
    · dsimp only [buildEncLoop, initOh, encRun]
      by_cases hs : s = start <;> simp [hs, hcf, hct]
    · change vecVal x gs (initRem l cF) = r.val
      dsimp only [vecVal, natOf]
      rw [Fin.sum_univ_castSucc]
      have hlast : (if wireVal x gs (initRem l cF (Fin.last l)) = true then 2 ^ (Fin.last l).val else 0) = 0 := by
        simp [initRem, hcf]
      rw [hlast, add_zero]
      have hrlt : r.val < 2 ^ l := by
        have h1 : (goodSet step start final p).card ≤ (Finset.univ : Finset (Fin l → Bool)).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have h2 : (Finset.univ : Finset (Fin l → Bool)).card = 2 ^ l := by simp
        exact r.isLt.trans_le (h1.trans_eq h2)
      have hcongr : (∑ i : Fin l, if wireVal x gs (initRem l cF i.castSucc) = true then 2 ^ i.castSucc.val else 0) =
          natOf (fun i : Fin l => r.val.testBit i.val) := by
        unfold natOf
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [initRem, Fin.val_castSucc, i.isLt, ↓reduceIte]
        rw [input_wireVal idx gs i]
      rw [hcongr, natOf_testBit l r.val hrlt]
  | succ k ih =>
    dsimp only [buildEncLoop]
    rcases hr1 : buildEncLoop cF cT step start c0 k (Nat.le_of_succ_le hk) gs with ⟨gs1, oh1, rem1, ew1⟩
    have hs1 := ih (Nat.le_of_succ_le hk); rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hoh1, hrem1, hew1, he1⟩ := hs1
    set kj : Fin l := ⟨k, hk⟩
    rcases hr2 : pushSelectVec l q (l + 1) gs1 cF oh1 (c0 kj) with ⟨gs2, zVec⟩
    have hs2 := pushSelectVec_spec l q (l + 1) gs1 cF oh1 (c0 kj)
      hv1 (by omega) hoh1 (fun s i => by have := hc0 kj s i; omega)
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hz2, he2⟩ := hs2
    rcases hr3 : pushSubVec l (l + 1) gs2 cT rem1 zVec with ⟨gs3, diff, ge⟩
    have hs3 := pushSubVec_spec l (l + 1) gs2 cT rem1 zVec
      hv2 (by omega) (fun i => by have := hrem1 i; omega) hz2
    rw [hr3] at hs3; dsimp only at hs3
    obtain ⟨hv3, hp3, hl3, hdiff3, hge3, he3⟩ := hs3
    rcases hr4 : pushMuxVec l (l + 1) gs3 ge diff rem1 with ⟨gs4, rem2⟩
    have hs4 := pushMuxVec_spec l (l + 1) gs3 ge diff rem1
      hv3 hge3 hdiff3 (fun i => by have := hrem1 i; omega)
    rw [hr4] at hs4; dsimp only at hs4
    obtain ⟨hv4, hp4, hl4, hrem4, _, hvv4⟩ := hs4
    rcases hr5 : pushNextOh l gs4 cF step kj oh1 cF ge with ⟨gs5, oh2⟩
    have hs5 := pushNextOh_spec l gs4 cF step kj oh1 cF ge
      hv4 (by omega) (fun s => by have := hoh1 s; omega) (by omega) (by omega)
    rw [hr5] at hs5; dsimp only at hs5
    obtain ⟨hv5, hp5, hl5, hoh5, he5⟩ := hs5
    dsimp only
    have hp15 : gs1 <+: gs5 := hp2.trans (hp3.trans (hp4.trans hp5))
    refine ⟨hv5, hp1.trans hp15, by rw [hl5, hl4, hl3, hl2, hl1]; ring, hoh5,
      fun i => by have := hrem4 i; omega,
      fun j => by
        by_cases hjk : j = kj
        · subst hjk; simp; omega
        · rw [Function.update_of_ne hjk]; have := hew1 j; omega,
      fun r hcf hct hc0v => ?_⟩
    let p := fixedWord l
    set idx := fun i : Fin l => r.val.testBit i.val
    set x := List.ofFn idx
    have hx : x.length = l := by simp [x]
    obtain ⟨hoh_v, hrem_v, hew_v⟩ := he1 r hcf hct hc0v
    set er := encRun step start final p r.val k (Nat.le_of_succ_le hk)
    have hcf1 : wireVal x gs1 cF = false := by
      rw [wireVal_prefix x hp1 (by omega), hcf]
    have hct2 : wireVal x gs2 cT = true := by
      rw [wireVal_prefix x (hp1.trans hp2) (by omega), hct]
    have hz_val : vecVal x gs2 zVec = zeroCount step final p kj er.1 := by
      rw [he2 x hx hcf1 er.1 hoh_v]
      rw [vecVal_prefix x hp1 (c0 kj er.1) (fun i => by have := hc0 kj er.1 i; omega), hc0v kj er.1]
    have hrem_2 : vecVal x gs2 rem1 = er.2.1 := by
      rw [vecVal_prefix x hp2 rem1 (fun i => by have := hrem1 i; omega), hrem_v]
    obtain ⟨hge_val, hdiff_val⟩ := he3 x hx hct2
    rw [hz_val, hrem_2] at hge_val hdiff_val
    have hrem_4 : vecVal x gs4 rem2 = if decide (zeroCount step final p kj er.1 ≤ er.2.1) then
        er.2.1 - zeroCount step final p kj er.1 else er.2.1 := by
      rw [hvv4 x hx, hge_val, vecVal_prefix x (hp2.trans hp3) rem1 (fun i => by have := hrem1 i; omega), hrem_v]
      by_cases hle : zeroCount step final p kj er.1 ≤ er.2.1
      · simp [hle, hdiff_val hle]
      · simp [hle]
    refine ⟨fun s => ?_, ?_, fun j hj => ?_⟩
    · have hcf4 : wireVal x gs4 cF = false := by
        rw [wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans hp4))) (by omega), hcf]
      have hoh4 : ∀ s, wireVal x gs4 (oh1 s) = decide (s = er.1) := fun s => by
        rw [wireVal_prefix x (hp2.trans (hp3.trans hp4)) (by have := hoh1 s; omega), hoh_v s]
      rw [he5 x hx hcf4 er.1 hoh4 s]
      rw [hcf4, wireVal_prefix x hp4 (by omega), hge_val]
      rfl
    · rw [vecVal_prefix x hp5 rem2 (fun i => by have := hrem4 i; omega), hrem_4]
      rfl
    · by_cases hjk : j = kj
      · subst hjk
        change wireVal x gs5 (Function.update ew1 kj ge kj) =
          Function.update er.2.2 kj (decide (zeroCount step final p kj er.1 ≤ er.2.1)) kj
        simp only [Function.update_self]
        rw [wireVal_prefix x (hp4.trans hp5) (by omega), hge_val]
      · change wireVal x gs5 (Function.update ew1 kj ge j) =
          Function.update er.2.2 kj (decide (zeroCount step final p kj er.1 ≤ er.2.1)) j
        simp only [Function.update_of_ne hjk]
        have hlt : j.val < k := by
          have : j.val ≠ k := fun he => hjk (Fin.ext he)
          omega
        rw [wireVal_prefix x hp15 (by have := hew1 j; omega)]
        exact hew_v j hlt

def buildDecLoop {l q : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q)
    (c0 : Fin l → Fin q → Fin (l + 1) → ℕ) :
    (k : ℕ) → k ≤ l → List Gate →
      List Gate × (Fin q → ℕ) × (Fin (l + 1) → ℕ)
  | 0, _, gs => (gs, initOh cF cT start, fun _ => cF)
  | k + 1, hk, gs =>
    let r1 := buildDecLoop cF cT step start c0 k (Nat.le_of_succ_le hk) gs
    let kj : Fin l := ⟨k, hk⟩
    let r2 := pushSelectVec l q (l + 1) r1.1 cF r1.2.1 (c0 kj)
    let r3 := pushAddVec l (l + 1) r2.1 r1.2.2 r2.2 cF
    let r4 := pushMuxVec l (l + 1) r3.1 k r3.2.1 r1.2.2
    let r5 := pushNextOh l r4.1 cF step kj r1.2.1 cF k
    (r5.1, r5.2, r4.2)

lemma buildDecLoop_spec {l q : ℕ} (cF cT : ℕ)
    (step : Fin l → Fin q → Bool → Bool → Fin q) (start : Fin q) (final : Fin q → Bool)
    (c0 : Fin l → Fin q → Fin (l + 1) → ℕ)
    (k : ℕ) (hk : k ≤ l) (gs : List Gate)
    (hv : ValidGates l gs) (hcF : cF < l + gs.length) (hcT : cT < l + gs.length)
    (hc0 : ∀ j s i, c0 j s i < l + gs.length) :
    let res := buildDecLoop cF cT step start c0 k hk gs
    ValidGates l res.1 ∧ gs <+: res.1 ∧
    res.1.length = gs.length + k * (4 * q * (l + 1) + 15 * (l + 1) + 6 + 5 * q * q) ∧
    (∀ s, res.2.1 s < l + res.1.length) ∧
    (∀ i, res.2.2 i < l + res.1.length) ∧
    let p := fixedWord l
    ∀ (u : Fin l → Bool),
      let x := List.ofFn u
      wireVal x gs cF = false →
      wireVal x gs cT = true →
      (∀ j s, vecVal x gs (c0 j s) = zeroCount step final p j s) →
      (∀ s, wireVal x res.1 (res.2.1 s) =
        decide (s = runPrefix step start p u k hk)) ∧
      vecVal x res.1 res.2.2 =
        ∑ j : Fin l, if j.val < k ∧ u j = true then
          zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0 := by
  induction k with
  | zero =>
    refine ⟨hv, List.prefix_refl _, by simp [buildDecLoop],
      fun s => by dsimp only [buildDecLoop, initOh]; split_ifs <;> omega,
      fun _ => hcF, fun u hcf hct _ => ⟨fun s => ?_, ?_⟩⟩
    · dsimp only [buildDecLoop, initOh, runPrefix]
      by_cases hs : s = start <;> simp [hs, hcf, hct]
    · simp [buildDecLoop, vecVal, natOf, hcf]
  | succ k ih =>
    dsimp only [buildDecLoop]
    rcases hr1 : buildDecLoop cF cT step start c0 k (Nat.le_of_succ_le hk) gs with ⟨gs1, oh1, acc1⟩
    have hs1 := ih (Nat.le_of_succ_le hk); rw [hr1] at hs1; dsimp only at hs1
    obtain ⟨hv1, hp1, hl1, hoh1, hacc1, he1⟩ := hs1
    set kj : Fin l := ⟨k, hk⟩
    rcases hr2 : pushSelectVec l q (l + 1) gs1 cF oh1 (c0 kj) with ⟨gs2, zVec⟩
    have hs2 := pushSelectVec_spec l q (l + 1) gs1 cF oh1 (c0 kj)
      hv1 (by omega) hoh1 (fun s i => by have := hc0 kj s i; omega)
    rw [hr2] at hs2; dsimp only at hs2
    obtain ⟨hv2, hp2, hl2, hz2, he2⟩ := hs2
    rcases hr3 : pushAddVec l (l + 1) gs2 acc1 zVec cF with ⟨gs3, sumVec, co3⟩
    have hs3 := pushAddVec_spec l (l + 1) gs2 acc1 zVec cF
      hv2 (fun i => by have := hacc1 i; omega) hz2 (by omega)
    rw [hr3] at hs3; dsimp only at hs3
    obtain ⟨hv3, hp3, hl3, hsum3, hco3, he3⟩ := hs3
    rcases hr4 : pushMuxVec l (l + 1) gs3 k sumVec acc1 with ⟨gs4, acc2⟩
    have hs4 := pushMuxVec_spec l (l + 1) gs3 k sumVec acc1
      hv3 (by omega) hsum3 (fun i => by have := hacc1 i; omega)
    rw [hr4] at hs4; dsimp only at hs4
    obtain ⟨hv4, hp4, hl4, hacc4, _, hvv4⟩ := hs4
    rcases hr5 : pushNextOh l gs4 cF step kj oh1 cF k with ⟨gs5, oh2⟩
    have hs5 := pushNextOh_spec l gs4 cF step kj oh1 cF k
      hv4 (by omega) (fun s => by have := hoh1 s; omega) (by omega) (by omega)
    rw [hr5] at hs5; dsimp only at hs5
    obtain ⟨hv5, hp5, hl5, hoh5, he5⟩ := hs5
    dsimp only
    have hp15 : gs1 <+: gs5 := hp2.trans (hp3.trans (hp4.trans hp5))
    refine ⟨hv5, hp1.trans hp15, by rw [hl5, hl4, hl3, hl2, hl1]; ring, hoh5,
      fun i => by have := hacc4 i; omega, fun u hcf hct hc0v => ?_⟩
    let p := fixedWord l
    set x := List.ofFn u
    have hx : x.length = l := by simp [x]
    obtain ⟨hoh_v, hacc_v⟩ := he1 u hcf hct hc0v
    set cur := runPrefix step start p u k (Nat.le_of_succ_le hk)
    have hcf1 : wireVal x gs1 cF = false := by
      rw [wireVal_prefix x hp1 (by omega), hcf]
    have hz_val : vecVal x gs2 zVec = zeroCount step final p kj cur := by
      rw [he2 x hx hcf1 cur hoh_v]
      rw [vecVal_prefix x hp1 (c0 kj cur) (fun i => by have := hc0 kj cur i; omega), hc0v kj cur]
    have hacc_2 : vecVal x gs2 acc1 =
        ∑ j : Fin l, if j.val < k ∧ u j = true then
          zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0 := by
      rw [vecVal_prefix x hp2 acc1 (fun i => by have := hacc1 i; omega), hacc_v]
    have hacc_le : vecVal x gs2 acc1 ≤ 2 ^ l := by
      rw [hacc_2]
      have h1 : (∑ j : Fin l, if j.val < k ∧ u j = true then
            zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) ≤
          ∑ j : Fin l, if u j then
            zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0 := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : j.val < k <;> cases u j <;> simp [hj]
      rw [← card_lt_keyOf step start final p u] at h1
      have h2 : ((goodSet step start final p).filter (fun other => keyOf other < keyOf u)).card ≤
          (Finset.univ : Finset (Fin l → Bool)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      have h3 : (Finset.univ : Finset (Fin l → Bool)).card = 2 ^ l := by simp
      omega
    have hz_le : zeroCount step final p kj cur ≤ 2 ^ (l - 1) := by
      unfold zeroCount
      exact le_trans (dpVal_le step final p (l - 1 - kj.val) (by omega) _)
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hsum_eq : vecVal x gs3 sumVec = vecVal x gs2 acc1 + zeroCount step final p kj cur := by
      have hadd := he3 x hx
      rw [hz_val, wireVal_prefix x (hp1.trans hp2) (by omega), hcf] at hadd
      simp only [b2n, Bool.false_eq_true, ↓reduceIte, add_zero] at hadd
      have hlt_tot : vecVal x gs2 acc1 + zeroCount step final p kj cur < 2 ^ (l + 1) := by
        have h3 : 2 ^ (l + 1) = 2 ^ l + 2 ^ l := by rw [pow_succ]; omega
        have hstrict : 2 ^ (l - 1) < 2 ^ l := Nat.pow_lt_pow_right (by omega) (by omega)
        omega
      have hco0 : wireVal x gs3 co3 = false := by
        cases hc : wireVal x gs3 co3
        · rfl
        · rw [hc] at hadd
          simp only [↓reduceIte, one_mul] at hadd
          omega
      rw [hco0] at hadd
      simpa using hadd
    refine ⟨fun s => ?_, ?_⟩
    · have hcf4 : wireVal x gs4 cF = false := by
        rw [wireVal_prefix x (hp1.trans (hp2.trans (hp3.trans hp4))) (by omega), hcf]
      have hoh4 : ∀ s, wireVal x gs4 (oh1 s) = decide (s = cur) := fun s => by
        rw [wireVal_prefix x (hp2.trans (hp3.trans hp4)) (by have := hoh1 s; omega), hoh_v s]
      rw [he5 x hx hcf4 cur hoh4 s]
      rw [hcf4, input_wireVal u gs4 kj]
      rfl
    · rw [vecVal_prefix x hp5 acc2 (fun i => by have := hacc4 i; omega)]
      rw [hvv4 x hx, input_wireVal u gs3 kj]
      rw [hsum_eq, vecVal_prefix x (hp2.trans hp3) acc1 (fun i => by have := hacc1 i; omega), hacc_2, hacc_v]
      have hdiff :
          (∑ j : Fin l, if j.val < k + 1 ∧ u j = true then
            zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) =
          (∑ j : Fin l, if j.val < k ∧ u j = true then
            zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) +
          (if u kj = true then zeroCount step final p kj cur else 0) := by
        rw [← Finset.sum_add_sum_compl {kj}]
        have h1 : (∑ j ∈ ({kj} : Finset (Fin l)),
            if j.val < k + 1 ∧ u j = true then
              zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) =
            if u kj = true then zeroCount step final p kj cur else 0 := by
          simp [kj, cur]
        have h2 : (∑ j ∈ ({kj} : Finset (Fin l))ᶜ,
            if j.val < k + 1 ∧ u j = true then
              zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) =
            (∑ j : Fin l, if j.val < k ∧ u j = true then
              zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) := by
          rw [← Finset.sum_add_sum_compl {kj}]
          have hkj0 : (∑ j ∈ ({kj} : Finset (Fin l)),
              if j.val < k ∧ u j = true then
                zeroCount step final p j (runPrefix step start p u j.val (by omega)) else 0) = 0 := by
            simp [kj]
          rw [hkj0, zero_add]
          refine Finset.sum_congr rfl fun j hj => ?_
          simp only [Finset.mem_compl, Finset.mem_singleton] at hj
          have hne : j.val ≠ k := fun he => hj (Fin.ext he)
          have hiff : (j.val < k + 1) ↔ (j.val < k) := by omega
          simp [hiff]
        rw [h1, h2, add_comm]
      rw [hdiff]
      cases hu : u kj <;> simp <;> rfl

end PEqualNP.Outside.L_lib_594

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_lib_594

theorem PEqualNP.Outside.L_lib_594 :
∀ (l q : ℕ), 0 < l → ∀ (start : Fin q) (step : Fin l → Fin q → Bool → Fin q)
  (final : Fin q → Bool),
  let W := Fin l → Bool
  let good := Finset.univ.filter (fun word : W =>
    final ((List.finRange l).foldl (fun s j => step j s (word j)) start) = true)
  let key := fun x : W => ∑ i : Fin l, if x i then 2^(l-1-i.val) else 0
  let rank := fun x : W => (good.filter (fun z => key z < key x)).card
  let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
    PEqualNP.MetaComplexity.NestedCover.ReadsBack l C ∧
    (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) ∧ C.size ≤ 256*(l+1)^2*(q+1)^2
  ∃ (select : Fin good.card ≃ ↥good)
    (enc dec : PEqualNP.CircuitLowerBounds.Circuit)
    (ew : Fin l → Fin (l+enc.size)) (dw : Fin l → Fin (l+dec.size)),
    valid enc ∧ valid dec ∧ ∀ (r : Fin good.card) (j : Fin l),
      rank (select r).val = r.val ∧
      (enc.wires (List.ofFn (fun i : Fin l => r.val.testBit i.val))).getD (ew j).val false =
        (select r).val j ∧
      (dec.wires (List.ofFn (select r).val)).getD (dw j).val false = r.val.testBit j.val := by
  intro l q hl start step final
  dsimp only
  let step' : Fin l → Fin q → Bool → Bool → Fin q := fun j s _ b => step j s b
  let p := fixedWord l
  rcases hrC : pushConsts l [] with ⟨gsC, cF, cT⟩
  have hsC := pushConsts_spec l hl [] (validGates_nil l)
  rw [hrC] at hsC
  dsimp only at hsC
  obtain ⟨hvC, _, hlC, hcF, hcT, heC⟩ := hsC
  let c0 := countWires cF cT step' final
  have hc0 : ∀ j s i, c0 j s i < l + gsC.length :=
    countWires_lt cF cT step' final hcF hcT
  rcases hrE : buildEncLoop cF cT step' start c0 l (le_refl l) gsC with ⟨gsE, ohE, remE, ewRaw⟩
  have hsE := buildEncLoop_spec cF cT step' start final c0 l (le_refl l) gsC hvC hcF hcT hc0
  rw [hrE] at hsE
  dsimp only at hsE
  obtain ⟨hvE, _, hlE, _, _, hew_lt, heE⟩ := hsE
  rcases hrD : buildDecLoop cF cT step' start c0 l (le_refl l) gsC with ⟨gsD, ohD, dwRaw⟩
  have hsD := buildDecLoop_spec cF cT step' start final c0 l (le_refl l) gsC hvC hcF hcT hc0
  rw [hrD] at hsD
  dsimp only at hsD
  obtain ⟨hvD, _, hlD, _, hdw_lt, heD⟩ := hsD
  let enc : Circuit := ⟨gsE, 0⟩
  let dec : Circuit := ⟨gsD, 0⟩
  let ew : Fin l → Fin (l + enc.size) := fun j => ⟨ewRaw j, hew_lt j⟩
  let dw : Fin l → Fin (l + dec.size) := fun j => ⟨dwRaw j.castSucc, hdw_lt j.castSucc⟩
  have henc_size : enc.size ≤ 256 * (l + 1) ^ 2 * (q + 1) ^ 2 := by
    change gsE.length ≤ _
    rw [hlE, hlC, List.length_nil]
    have hdiff : 256 * (l + 1) ^ 2 * (q + 1) ^ 2 =
        (0 + 3 + l * (4 * q * (l + 1) + 16 * (l + 1) + 6 + 5 * q * q)) +
        (253 + 490 * l + 240 * l ^ 2 + 512 * q + 1020 * l * q + 508 * l ^ 2 * q +
          256 * q ^ 2 + 507 * l * q ^ 2 + 256 * l ^ 2 * q ^ 2) := by ring
    omega
  have hdec_size : dec.size ≤ 256 * (l + 1) ^ 2 * (q + 1) ^ 2 := by
    change gsD.length ≤ _
    rw [hlD, hlC, List.length_nil]
    have hdiff : 256 * (l + 1) ^ 2 * (q + 1) ^ 2 =
        (0 + 3 + l * (4 * q * (l + 1) + 15 * (l + 1) + 6 + 5 * q * q)) +
        (253 + 491 * l + 241 * l ^ 2 + 512 * q + 1020 * l * q + 508 * l ^ 2 * q +
          256 * q ^ 2 + 507 * l * q ^ 2 + 256 * l ^ 2 * q ^ 2) := by ring
    omega
  refine ⟨selectEquiv step' start final p, enc, dec, ew, dw,
    ⟨hvE.1, hvE.2, henc_size⟩, ⟨hvD.1, hvD.2, hdec_size⟩, ?_⟩
  intro r j
  let word := (selectEquiv step' start final p r).val
  let idx := fun i : Fin l => r.val.testBit i.val
  have hrank : ((goodSet step' start final p).filter (fun other => keyOf other < keyOf word)).card = r.val :=
    selectFn_rank step' start final p r
  refine ⟨hrank, ?_, ?_⟩
  · let x := List.ofFn idx
    have hx : x.length = l := by simp [x]
    obtain ⟨hcf, hct⟩ := heC x hx
    obtain ⟨_, _, hew_v⟩ := heE r hcf hct (countWires_value cF cT step' final hcf hct)
    exact hew_v j j.isLt
  · let x := List.ofFn word
    have hx : x.length = l := by simp [x]
    obtain ⟨hcf, hct⟩ := heC x hx
    obtain ⟨_, hacc_v⟩ := heD word hcf hct (countWires_value cF cT step' final hcf hct)
    have hacc_eq : vecVal x gsD dwRaw = r.val := by
      rw [hacc_v]
      have hcongr : (∑ j' : Fin l, if j'.val < l ∧ word j' = true then
            zeroCount step' final p j' (runPrefix step' start p word j'.val (by omega)) else 0) =
          ∑ j' : Fin l, if word j' then
            zeroCount step' final p j' (runPrefix step' start p word j'.val (by omega)) else 0 := by
        refine Finset.sum_congr rfl fun j' _ => ?_
        simp [j'.isLt]
      rw [hcongr, ← card_lt_keyOf step' start final p word]
      exact hrank
    have htb := testBit_natOf (fun i : Fin (l + 1) => wireVal x gsD (dwRaw i)) j.castSucc
    change (vecVal x gsD dwRaw).testBit j.val = (dec.wires x).getD (dw j).val false at htb
    rw [hacc_eq] at htb
    exact htb.symm
