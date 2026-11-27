import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25624

abbrev ev5 (t0 t1 t2 t3 t4 k : Bool) : Bool :=
  xor (xor (xor (xor t0 t1) t2) (!(xor (xor t1 t2) t3) && xor (xor t2 t3) t4)) k


def mixF (x : Int → Bool) (z : Int) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evolveF (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (injection z)

theorem ev_eq (x inj : Int → Bool) (z : Int) :
    evolveF x inj z = ev5 (x (z-1)) (x z) (x (z+1)) (x (z+2)) (x (z+3)) (inj z) := by
  have h1 : z + 1 - 1 = z := by ring
  have h2 : z + 1 + 1 = z + 2 := by ring
  have h3 : z + 2 - 1 = z + 1 := by ring
  have h4 : z + 2 + 1 = z + 3 := by ring
  simp only [evolveF, mixF, ev5, h1, h2, h3, h4]

theorem evolve_congr {x x' inj inj' : Int → Bool} {z : Int}
    (h : ∀ s, z - 1 ≤ s → s ≤ z + 3 → x s = x' s) (hi : inj z = inj' z) :
    evolveF x inj z = evolveF x' inj' z := by
  rw [ev_eq, ev_eq, h (z-1) (by omega) (by omega), h z (by omega) (by omega),
    h (z+1) (by omega) (by omega), h (z+2) (by omega) (by omega),
    h (z+3) (by omega) (by omega), hi]


def blockF (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0


theorem block_succ (w : Nat) (t : Int → Bool) (e : Int) :
    blockF (w+1) t e = blockF w t e ||| ((t (e+1+(w:Int))).toNat <<< w) := by
  simp only [blockF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem block_bit (w : Nat) (t : Int → Bool) (e : Int) (i : Nat) :
    (blockF w t e).testBit i = (decide (i < w) && t (e+1+(i:Int))) := by
  induction w with
  | zero => simp [blockF]
  | succ w ih =>
    rw [block_succ, Nat.testBit_or, ih]
    rcases lt_trichotomy i w with h | rfl | h
    · cases t (e+1+(w:Int)) <;> simp [Nat.testBit_shiftLeft, h, show i < w + 1 by omega] <;> omega
    · cases t (e+1+(i:Int)) <;> simp [Nat.testBit_shiftLeft]
    · cases t (e+1+(w:Int)) <;>
        simp [Nat.one_shiftLeft, Nat.testBit_two_pow, show ¬ i < w by omega,
          show ¬ i < w + 1 by omega, show w ≠ i by omega]

theorem block_lt (w : Nat) (t : Int → Bool) (e : Int) : blockF w t e < 2 ^ w := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [block_bit]
  simp [show ¬ i < w by omega]


theorem ev5_free (t0 t1 t2 t3 t4 t4' k : Bool) (h : xor (xor t1 t2) t3 = true) :
    ev5 t0 t1 t2 t3 t4 k = ev5 t0 t1 t2 t3 t4' k := by
  revert h; revert t0 t1 t2 t3 t4 t4' k; decide

theorem agree_step (x y inj : Int → Bool) (c : Int) (h : ∀ z ≤ c, x z = y z) :
    ∀ z ≤ c - 3 + ((mixF y (c-1)).toNat : Int), evolveF x inj z = evolveF y inj z := by
  intro z hz
  by_cases hz3 : z ≤ c - 3
  · exact evolve_congr (fun s _ h2 => h s (by omega)) rfl
  · cases hm : mixF y (c-1)
    · rw [hm] at hz
      simp only [Bool.toNat_false, Nat.cast_zero] at hz
      omega
    · rw [hm] at hz
      simp only [Bool.toNat_true, Nat.cast_one] at hz
      have hc : c = z + 2 := by omega
      subst hc
      rw [show z + 2 - 1 = z + 1 by ring] at hm
      simp only [mixF, show z + 1 - 1 = z by ring, show z + 1 + 1 = z + 2 by ring] at hm
      rw [ev_eq, ev_eq, h (z-1) (by omega), h z (by omega), h (z+1) (by omega),
        h (z+2) (by omega)]
      exact ev5_free _ _ _ _ _ _ _ hm

def actualF (inj : Nat → Int → Bool) (x : Int → Bool) (time : Nat) : Int → Bool :=
  (List.range time).foldl (fun state tick => evolveF state (inj (tick+1))) x

def pairF (inj : Nat → Int → Bool) (x : Int → Bool) (c : Int) (n : Nat) : (Int → Bool) × Int :=
  (List.range n).foldl (fun (prev : (Int → Bool) × Int) j =>
    (evolveF prev.1 (inj (j+1)), prev.2-3+((mixF prev.1 (prev.2-1)).toNat : Int))) (x, c)

theorem pair_spec (inj : Nat → Int → Bool) (x y : Int → Bool) (c : Int) (n : Nat)
    (h : ∀ z ≤ c, x z = y z) :
    (∀ z ≤ (pairF inj y c n).2, actualF inj x n z = (pairF inj y c n).1 z) ∧
      c - 3*(n:Int) ≤ (pairF inj y c n).2 := by
  induction n with
  | zero =>
    simp only [pairF, actualF, List.range_zero, List.foldl_nil]
    exact ⟨h, by omega⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have e1 : pairF inj y c (n+1) = (evolveF (pairF inj y c n).1 (inj (n+1)),
        (pairF inj y c n).2 - 3 + ((mixF (pairF inj y c n).1 ((pairF inj y c n).2-1)).toNat : Int)) := by
      simp only [pairF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have e2 : actualF inj x (n+1) = evolveF (actualF inj x n) (inj (n+1)) := by
      simp only [actualF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [e1, e2]
    dsimp only
    refine ⟨agree_step _ _ _ _ ih1, ?_⟩
    push_cast
    omega

def sampleF (ref : Int → Bool) (f : Int) (pattern : Nat) (site : Int) : Bool :=
  if site ≤ f then ref site else pattern.testBit (site-f-1).toNat

def observeF (inj : Nat → Int → Bool) (ref : Int → Bool) (f : Int) (width pattern : Nat)
    (query : Nat × Int × Bool) : Option Bool :=
  if query.2.1 ≤ (pairF inj (sampleF ref f pattern) (f+(width : Int)) query.1).2 then
    some ((pairF inj (sampleF ref f pattern) (f+(width : Int)) query.1).1 query.2.1 == query.2.2)
  else none

def firstF (base : Int → Bool) (inj : Nat → Int → Bool) (b : Int) (raw : Nat) : Int → Bool :=
  evolveF (fun inputSite => if inputSite ≤ b then base inputSite
    else raw.testBit (inputSite-b-1).toNat) (inj 0)

theorem sample_agree (t ref : Int → Bool) (f : Int) (h p : Nat) (h1 : ∀ z ≤ f, t z = ref z)
    (hb : blockF h t f = p) : ∀ z ≤ f + (h:Int), t z = sampleF ref f p z := by
  intro z hz
  unfold sampleF
  split_ifs with hzf
  · exact h1 z hzf
  · have hbit := block_bit h t f (z-f-1).toNat
    rw [hb] at hbit
    have e : ((z-f-1).toNat : Int) = z-f-1 := Int.toNat_of_nonneg (by omega)
    have hi : (z-f-1).toNat < h := by omega
    rw [show f + 1 + ((z-f-1).toNat : Int) = z by omega, decide_eq_true hi, Bool.true_and] at hbit
    exact hbit.symm

theorem block_split (h : Nat) (t : Int → Bool) (e : Int) :
    blockF (h+1) t e = blockF h t e ∨ blockF (h+1) t e = blockF h t e + 2^h := by
  rw [block_succ]
  cases t (e+1+(h:Int))
  · left
    simp
  · right
    rw [Bool.toNat_true, Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt (block_lt h t e),
      Nat.one_shiftLeft, Nat.add_comm]

def gF {α : Type} (mass : Nat → Nat → Nat) (obs : Nat → Nat → α → Option Bool) (tests : List α)
    (depth : Nat) (acc : Nat × List Nat) (label : Nat) : Nat × List Nat :=
  let weight := mass depth label
  if weight = 0 then acc else
    let answers := tests.map (obs depth label)
    if answers.contains (some false) then acc
    else if answers.all (fun answer => answer == some true) then (acc.1+weight, acc.2)
    else (acc.1, label :: (label + 2^depth) :: acc.2)

def foF {α : Type} (mass : Nat → Nat → Nat) (obs : Nat → Nat → α → Option Bool) (tests : List α)
    (layer : Nat × List Nat) (depth : Nat) : Nat × List Nat :=
  layer.2.foldl (gF mass obs tests depth) (layer.1, [])

def passF {α : Type} (seeds : List Nat) (cls : Nat → Nat → Nat) (tests : List α)
    (test : Nat → α → Bool) (h p : Nat) : Nat :=
  seeds.countP (fun k => (cls h k == p) && tests.all (test k))

def sumF {α : Type} (seeds : List Nat) (cls : Nat → Nat → Nat) (tests : List α)
    (test : Nat → α → Bool) (h : Nat) (L : List Nat) : Nat :=
  (L.map (passF seeds cls tests test h)).sum

theorem countP_split (l : List Nat) (f g1 g2 : Nat → Bool) (H : ∀ x, f x = (g1 x || g2 x))
    (Hd : ∀ x, ¬ (g1 x = true ∧ g2 x = true)) :
    l.countP f = l.countP g1 + l.countP g2 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, ih, H a]
    have := Hd a
    cases h1 : g1 a <;> cases h2 : g2 a <;> simp [h1, h2] at this ⊢ <;> omega

theorem pass_split {α : Type} (seeds : List Nat) (cls : Nat → Nat → Nat) (tests : List α)
    (test : Nat → α → Bool)
    (hsplit : ∀ h k, cls (h+1) k = cls h k ∨ cls (h+1) k = cls h k + 2^h)
    (hlt : ∀ h k, cls h k < 2^h) (h p : Nat) (hp : p < 2^h) :
    passF seeds cls tests test h p =
      passF seeds cls tests test (h+1) p + passF seeds cls tests test (h+1) (p+2^h) := by
  unfold passF
  apply countP_split
  · intro k
    have hl := hlt h k
    cases tests.all (test k)
    · simp
    · simp only [Bool.and_true]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hsplit h k with e | e <;> rw [e] <;> constructor <;> intro hh <;> omega
  · intro k ⟨h1, h2⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h1 h2
    omega

theorem g_step {α : Type} (seeds : List Nat) (cls mass : Nat → Nat → Nat)
    (obs : Nat → Nat → α → Option Bool) (tests : List α) (test : Nat → α → Bool) (D : Nat)
    (hmass : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => cls h k == p)).length)
    (hsound : ∀ h p q k v, k ∈ seeds → cls h k = p → q ∈ tests → obs h p q = some v →
      test k q = v)
    (hsplit : ∀ h k, cls (h+1) k = cls h k ∨ cls (h+1) k = cls h k + 2^h)
    (hlt : ∀ h k, cls h k < 2^h) (h p : Nat) (hD : h ≤ D) (hp : p < 2^h) (acc : Nat × List Nat) :
    (gF mass obs tests h acc p).1 + sumF seeds cls tests test (h+1) (gF mass obs tests h acc p).2 =
      acc.1 + sumF seeds cls tests test (h+1) acc.2 + passF seeds cls tests test h p ∧
    ((∀ x ∈ acc.2, x < 2^(h+1)) → ∀ x ∈ (gF mass obs tests h acc p).2, x < 2^(h+1)) := by
  have hm := hmass h hD p hp
  rw [← List.countP_eq_length_filter] at hm
  have hle : passF seeds cls tests test h p ≤ mass h p := by
    rw [hm]
    apply List.countP_mono_left
    intro k _ hk
    simp only [Bool.and_eq_true] at hk
    exact hk.1
  unfold gF
  dsimp only
  split_ifs with hw hf ht
  · exact ⟨by omega, fun hb => hb⟩
  · rw [List.contains_iff_mem, List.mem_map] at hf
    obtain ⟨q, hq, hqo⟩ := hf
    have h0 : passF seeds cls tests test h p = 0 := by
      unfold passF
      rw [List.countP_eq_zero]
      intro k hk hk2
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hk2
      have e1 := hsound h p q k false hk hk2.1 hq hqo
      have e2 := hk2.2 q hq
      rw [e1] at e2
      exact Bool.false_ne_true e2
    exact ⟨by omega, fun hb => hb⟩
  · have heq : passF seeds cls tests test h p = mass h p := by
      rw [hm]
      unfold passF
      apply List.countP_congr
      intro k hk
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
      constructor
      · exact fun x => x.1
      · intro hc
        refine ⟨hc, fun q hq => ?_⟩
        rw [List.all_eq_true] at ht
        have h1 := ht (obs h p q) (List.mem_map.2 ⟨q, hq, rfl⟩)
        have h2 : obs h p q = some true := by simpa using h1
        exact hsound h p q k true hk hc hq h2
    refine ⟨?_, fun hb => hb⟩
    dsimp only
    omega
  · have hs := pass_split seeds cls tests test hsplit hlt h p hp
    refine ⟨?_, ?_⟩
    · simp only [sumF, List.map_cons, List.sum_cons] at hs ⊢
      omega
    · intro hb x hx
      simp only [List.mem_cons] at hx
      have h2 : 2^(h+1) = 2*2^h := by rw [pow_succ]; ring
      rcases hx with rfl | rfl | hx
      · omega
      · omega
      · exact hb x hx

theorem inner_fold {α : Type} (seeds : List Nat) (cls mass : Nat → Nat → Nat)
    (obs : Nat → Nat → α → Option Bool) (tests : List α) (test : Nat → α → Bool) (D : Nat)
    (hmass : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => cls h k == p)).length)
    (hsound : ∀ h p q k v, k ∈ seeds → cls h k = p → q ∈ tests → obs h p q = some v →
      test k q = v)
    (hsplit : ∀ h k, cls (h+1) k = cls h k ∨ cls (h+1) k = cls h k + 2^h)
    (hlt : ∀ h k, cls h k < 2^h) (h : Nat) (hD : h ≤ D) :
    ∀ (L : List Nat) (acc : Nat × List Nat), (∀ p ∈ L, p < 2^h) → (∀ x ∈ acc.2, x < 2^(h+1)) →
      (L.foldl (gF mass obs tests h) acc).1 +
          sumF seeds cls tests test (h+1) (L.foldl (gF mass obs tests h) acc).2 =
        acc.1 + sumF seeds cls tests test (h+1) acc.2 + sumF seeds cls tests test h L ∧
      ∀ x ∈ (L.foldl (gF mass obs tests h) acc).2, x < 2^(h+1) := by
  intro L
  induction L with
  | nil =>
    intro acc _ hb
    simp only [List.foldl_nil, sumF, List.map_nil, List.sum_nil]
    exact ⟨by omega, hb⟩
  | cons p t ih =>
    intro acc hL hb
    rw [List.foldl_cons]
    obtain ⟨s1, s2⟩ := g_step seeds cls mass obs tests test D hmass hsound hsplit hlt h p hD
      (hL p (by simp)) acc
    obtain ⟨i1, i2⟩ := ih _ (fun x hx => hL x (by simp [hx])) (s2 hb)
    refine ⟨?_, i2⟩
    have e : sumF seeds cls tests test h (p :: t) =
        passF seeds cls tests test h p + sumF seeds cls tests test h t := by
      simp only [sumF, List.map_cons, List.sum_cons]
    rw [e]
    omega

theorem last_fold {α : Type} (mass : Nat → Nat → Nat) (obs : Nat → Nat → α → Option Bool)
    (tests : List α) (D : Nat) (hcomp : ∀ p q, q ∈ tests → obs D p q ≠ none) :
    ∀ (L : List Nat) (acc : Nat × List Nat), (L.foldl (gF mass obs tests D) acc).2 = acc.2 := by
  intro L
  induction L with
  | nil => intro acc; rfl
  | cons p t ih =>
    intro acc
    rw [List.foldl_cons, ih]
    unfold gF
    dsimp only
    split_ifs with hw hf ht
    · rfl
    · rfl
    · rfl
    · exfalso
      apply ht
      rw [List.all_eq_true]
      intro a ha
      rw [List.mem_map] at ha
      obtain ⟨q, hq, rfl⟩ := ha
      have hn := hcomp p q hq
      cases ho : obs D p q with
      | none => exact absurd ho hn
      | some v =>
        cases v
        · exact absurd (List.contains_iff_mem.2 (List.mem_map.2 ⟨q, hq, ho⟩)) hf
        · simp

theorem outer {α : Type} (seeds : List Nat) (cls mass : Nat → Nat → Nat)
    (obs : Nat → Nat → α → Option Bool) (tests : List α) (test : Nat → α → Bool) (D : Nat)
    (h0 : ∀ k, cls 0 k = 0)
    (hmass : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => cls h k == p)).length)
    (hsound : ∀ h p q k v, k ∈ seeds → cls h k = p → q ∈ tests → obs h p q = some v →
      test k q = v)
    (hsplit : ∀ h k, cls (h+1) k = cls h k ∨ cls (h+1) k = cls h k + 2^h)
    (hlt : ∀ h k, cls h k < 2^h) :
    ∀ n, n ≤ D + 1 →
      ((List.range n).foldl (foF mass obs tests) (0, [0])).1 +
          sumF seeds cls tests test n ((List.range n).foldl (foF mass obs tests) (0, [0])).2 =
        seeds.countP (fun k => tests.all (test k)) ∧
      ∀ x ∈ ((List.range n).foldl (foF mass obs tests) (0, [0])).2, x < 2^n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · simp only [sumF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, passF, h0]
      simp
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      simp
  | succ n ih =>
    intro hn
    obtain ⟨i1, i2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (foF mass obs tests) (0, [0]) = X at i1 i2 ⊢
    unfold foF
    obtain ⟨j1, j2⟩ := inner_fold seeds cls mass obs tests test D hmass hsound hsplit hlt n
      (by omega) X.2 (X.1, []) i2 (by simp)
    refine ⟨?_, j2⟩
    have e : sumF seeds cls tests test (n+1) ([] : List Nat) = 0 := rfl
    dsimp only at j1
    rw [e] at j1
    omega

theorem tally_main {α : Type} (seeds : List Nat) (cls mass : Nat → Nat → Nat)
    (obs : Nat → Nat → α → Option Bool) (tests : List α) (test : Nat → α → Bool) (D : Nat)
    (h0 : ∀ k, cls 0 k = 0)
    (hsplit : ∀ h k, cls (h+1) k = cls h k ∨ cls (h+1) k = cls h k + 2^h)
    (hlt : ∀ h k, cls h k < 2^h)
    (hmass : ∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => cls h k == p)).length)
    (hsound : ∀ h p q k v, k ∈ seeds → cls h k = p → q ∈ tests → obs h p q = some v →
      test k q = v)
    (hcomp : ∀ p q, q ∈ tests → obs D p q ≠ none) :
    ((List.range (D+1)).foldl (foF mass obs tests) (0, [0])).2 = [] ∧
      ((List.range (D+1)).foldl (foF mass obs tests) (0, [0])).1 =
        (seeds.filter (fun k => tests.all (test k))).length := by
  obtain ⟨o1, -⟩ := outer seeds cls mass obs tests test D h0 hmass hsound hsplit hlt (D+1) le_rfl
  have hl : ((List.range (D+1)).foldl (foF mass obs tests) (0, [0])).2 = [] := by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range D).foldl (foF mass obs tests) (0, [0]) = X
    unfold foF
    rw [last_fold mass obs tests D hcomp]
  refine ⟨hl, ?_⟩
  rw [hl] at o1
  rw [← List.countP_eq_length_filter]
  have e : sumF seeds cls tests test (D+1) ([] : List Nat) = 0 := rfl
  rw [e] at o1
  omega

theorem sound_inst (base : Int → Bool) (inj : Nat → Int → Bool) (b f : Int)
    (seeds : List Nat) (tests : List (Nat × Int × Bool))
    (H1 : ∀ raw ∈ seeds, ∀ z ≤ f, firstF base inj b raw z = evolveF base (inj 0) z) :
    ∀ h p q k v, k ∈ seeds → blockF h (firstF base inj b k) f = p → q ∈ tests →
      observeF inj (evolveF base (inj 0)) f h p q = some v →
      (actualF inj (firstF base inj b k) q.1 q.2.1 == q.2.2) = v := by
  intro h p q k v hk hb _ ho
  have hag := sample_agree _ _ f h p (H1 k hk) hb
  obtain ⟨s1, -⟩ := pair_spec inj _ _ _ q.1 hag
  unfold observeF at ho
  split_ifs at ho with hq
  rw [s1 _ hq]
  exact Option.some.inj ho

theorem comp_inst (inj : Nat → Int → Bool) (ref : Int → Bool) (f : Int) (D : Nat)
    (tests : List (Nat × Int × Bool))
    (H3 : ∀ test ∈ tests, test.2.1 + 3*(test.1 : Int) ≤ f+(D : Int)) :
    ∀ p q, q ∈ tests → observeF inj ref f D p q ≠ none := by
  intro p q hq
  have h3 := H3 q hq
  obtain ⟨-, s2⟩ := pair_spec inj (sampleF ref f p) (sampleF ref f p) (f+(D:Int)) q.1
    (fun _ _ => rfl)
  unfold observeF
  split_ifs with hq2
  · simp
  · exact absurd (by omega) hq2

end PEqualNP.Outside.L_meta_25624

open PEqualNP.Outside.L_meta_25624 in
theorem PEqualNP.Outside.L_meta_25624 :
    let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let step := fun (x injection : ℤ → Bool) (z : ℤ) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
    let block := fun (w : ℕ) (tape : ℤ → Bool) (edge : ℤ) =>
      (List.range w).foldl (fun (code j : ℕ) => code ||| ((tape (edge+1+(j : ℤ))).toNat <<< j)) 0
    ∀ (w m D : ℕ) (b f : ℤ) (base : ℤ → Bool) (inj : ℕ → ℤ → Bool) (mask : ℕ)
        (tests : List (ℕ × ℤ × Bool)) (mass : ℕ → ℕ → ℕ),
      let seeds := (List.range (2^m)).filter (fun raw => mask.testBit (raw % 2^w))
      let first := fun (raw : ℕ) => step (fun inputSite => if inputSite ≤ b then base inputSite else raw.testBit (inputSite-b-1).toNat) (inj 0)
      let ref := step base (inj 0)
      (∀ raw ∈ seeds, ∀ z ≤ f, first raw z = ref z) →
      (∀ h ≤ D, ∀ p < 2^h, mass h p = (seeds.filter (fun k => block h (first k) f == p)).length) →
      (∀ test ∈ tests, test.2.1 + 3*(test.1 : ℤ) ≤ f+(D : ℤ)) →
      let actual := fun (seed time : ℕ) =>
        (List.range time).foldl (fun state tick => step state (inj (tick+1))) (first seed)
      let observe := fun (width pattern : ℕ) (query : ℕ × ℤ × Bool) =>
        let sample := fun (site : ℤ) => if site ≤ f then ref site else pattern.testBit (site-f-1).toNat
        let pair := (List.range query.1).foldl (fun (prev : (ℤ → Bool) × ℤ) j =>
          (step prev.1 (inj (j+1)), prev.2-3+((mix prev.1 (prev.2-1)).toNat : ℤ)))
          (sample, f+(width : ℤ))
        if query.2.1 ≤ pair.2 then some (pair.1 query.2.1 == query.2.2) else none
      let tally := (List.range (D+1)).foldl (fun (layer : ℕ × List ℕ) depth =>
        layer.2.foldl (fun (acc : ℕ × List ℕ) label =>
          let weight := mass depth label
          if weight = 0 then acc else
            let answers := tests.map (observe depth label)
            if answers.contains (some false) then acc
            else if answers.all (fun answer => answer == some true) then (acc.1+weight, acc.2)
            else (acc.1, label :: (label + 2^depth) :: acc.2))
          (layer.1, [])) (0, [0])
      tally.2 = [] ∧ tally.1 =
        (seeds.filter (fun key => tests.all (fun wanted => actual key wanted.1 wanted.2.1 == wanted.2.2))).length := by
  intro mix step block w m D b f base inj mask tests mass seeds first ref H1 H2 H3 actual observe
    tally
  exact tally_main seeds (fun h k => blockF h (firstF base inj b k) f) mass
    (observeF inj (evolveF base (inj 0)) f) tests
    (fun k q => actualF inj (firstF base inj b k) q.1 q.2.1 == q.2.2) D (fun _ => rfl)
    (fun h _ => block_split h _ f) (fun h _ => block_lt h _ f) H2
    (sound_inst base inj b f seeds tests H1) (comp_inst inj (evolveF base (inj 0)) f D tests H3)
