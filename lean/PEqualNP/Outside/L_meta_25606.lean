import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25606

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


def runF (inj : Nat → Int → Bool) (x : Int → Bool) (rounds : Nat) : Int → Bool :=
  (List.range rounds).foldl (fun state tick => evolveF state (inj tick)) x

theorem run_succ (inj : Nat → Int → Bool) (x : Int → Bool) (t : Nat) :
    runF inj x (t+1) = evolveF (runF inj x t) (inj t) := by
  simp only [runF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

def capF (edge : Nat → Int) (width : Nat → Nat) (time : Nat) : Int := edge time + (width time : Int)

def wordF (base : Int → Bool) (inj : Nat → Int → Bool) (edge : Nat → Int) (width : Nat → Nat)
    (layer pattern extraBits : Nat) (z : Int) : Bool :=
  if z ≤ edge layer then runF inj base layer z
  else if z ≤ capF edge width layer then pattern.testBit (z-edge layer-1).toNat
  else extraBits.testBit (z-capF edge width layer-1).toNat

def admF (width mask : Nat → Nat) (layerIndex label : Nat) : Bool :=
  decide (label < 2^(width layerIndex)) && (mask layerIndex).testBit label

def linkF (base : Int → Bool) (inj : Nat → Int → Bool) (edge : Nat → Int) (width : Nat → Nat)
    (oldTime source dest : Nat) : Bool :=
  (List.range (2^((capF edge width (oldTime+1)+3-capF edge width oldTime).toNat))).any
    (fun completion =>
      (List.range (capF edge width (oldTime+1)-min (edge oldTime-3) (edge (oldTime+1))).toNat).all
        (fun offset =>
          evolveF (wordF base inj edge width oldTime source completion) (inj oldTime)
              (min (edge oldTime-3) (edge (oldTime+1))+1+(offset : Int)) ==
            wordF base inj edge width (oldTime+1) dest 0
              (min (edge oldTime-3) (edge (oldTime+1))+1+(offset : Int))))

def carryA (W : Nat → Nat → Nat → Int → Bool) (Cap : Nat → Int) (fromTime fromPattern : Nat)
    (certified : Int) : Int :=
  if fromTime = 0 then Cap 1 else
    min (Cap (fromTime+1)) (certified-3 + ((mixF (W fromTime fromPattern 0) (certified-1)).toNat : Int))

def limK (carry : Nat → Nat → Int → Int) (c0 : Int) (a : Nat → Nat) (len : Nat) : Int :=
  (List.range len).foldl (fun previous index => carry index (a index) previous) c0

theorem lim_succ (carry : Nat → Nat → Int → Int) (c0 : Int) (a : Nat → Nat) (k : Nat) :
    limK carry c0 a (k+1) = carry k (a k) (limK carry c0 a k) := by
  simp only [limK, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem lim_congr (carry : Nat → Nat → Int → Int) (c0 : Int) (a b : Nat → Nat) :
    ∀ k, (∀ i < k, a i = b i) → limK carry c0 a k = limK carry c0 b k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [lim_succ, lim_succ, ih (fun i hi => h i (by omega)), h k (by omega)]

theorem lim_le_cap (W : Nat → Nat → Nat → Int → Bool) (Cap : Nat → Int) (a : Nat → Nat) :
    ∀ t, limK (carryA W Cap) (Cap 0) a t ≤ Cap t := by
  intro t
  cases t with
  | zero =>
    simp only [limK, List.range_zero, List.foldl_nil]
    exact le_refl _
  | succ t =>
    rw [lim_succ]
    unfold carryA
    split_ifs with h
    · subst h
      exact le_refl _
    · exact min_le_left _ _

theorem part1 (inj : Nat → Int → Bool) (W : Nat → Nat → Nat → Int → Bool) (Cap : Nat → Int)
    (link : Nat → Nat → Nat → Bool) (n : Nat) (a : Nat → Nat)
    (hW : ∀ t p e z, z ≤ Cap t → W t p e z = W t p 0 z)
    (hL : ∀ t p d, link t p d = true → ∃ comp : Nat, ∀ z ≤ Cap (t+1),
      evolveF (W t p comp) (inj t) z = W (t+1) d 0 z)
    (hlink : ∀ t < n, link t (a t) (a (t+1)) = true) :
    ∃ initial : Int → Bool, ∀ t ≤ n, ∀ z ≤ limK (carryA W Cap) (Cap 0) a t,
      runF inj initial t z = W t (a t) 0 z := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · refine ⟨W 0 (a 0) 0, fun t ht z _ => ?_⟩
    have h0 : t = 0 := by omega
    subst h0
    rfl
  · obtain ⟨comp, hcomp⟩ := hL 0 (a 0) (a 1) (hlink 0 hn)
    refine ⟨W 0 (a 0) comp, ?_⟩
    intro t
    induction t with
    | zero =>
      intro _ z hz
      exact hW 0 (a 0) comp z hz
    | succ t ih =>
      intro ht z hz
      rw [run_succ]
      rw [lim_succ] at hz
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · subst h0
        have hz' : z ≤ Cap 1 := by simpa [carryA] using hz
        exact hcomp z hz'
      · have ih' := ih (by omega)
        have hcap := lim_le_cap W Cap a t
        obtain ⟨ct, hct⟩ := hL t (a t) (a (t+1)) (hlink t (by omega))
        unfold carryA at hz
        rw [if_neg (show ¬ t = 0 by omega)] at hz
        have hz1 := le_trans hz (min_le_right _ _)
        have hz2 := le_trans hz (min_le_left _ _)
        rw [agree_step _ _ _ _ ih' z hz1, ← agree_step (W t (a t) ct) (W t (a t) 0) (inj t)
          (limK (carryA W Cap) (Cap 0) a t) (fun s hs => hW t (a t) ct s (le_trans hs hcap)) z hz1]
        exact hct z hz2

def legalK (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool) (k : Nat) (a : Nat → Nat) :
    Prop :=
  (∀ t ≤ k, adm t (a t) = true) ∧ ∀ t < k, link t (a t) (a (t+1)) = true

def scoreF (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool) (carry : Nat → Nat → Int → Int)
    (wd : Nat → Nat) (c0 : Int) (n : Nat) : Nat → Option Int :=
  (List.range n).foldl (fun (prev : Nat → Option Int) stage child =>
    if adm (stage+1) child then
      ((List.range (2^(wd stage))).filterMap (fun parent =>
        if link stage parent child then (prev parent).map (carry stage parent) else none)).max?
    else none) (fun parent => if adm 0 parent then some c0 else none)

theorem score_succ (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool)
    (carry : Nat → Nat → Int → Int) (wd : Nat → Nat) (c0 : Int) (k q : Nat) :
    scoreF adm link carry wd c0 (k+1) q =
      if adm (k+1) q then
        ((List.range (2^(wd k))).filterMap (fun parent =>
          if link k parent q then (scoreF adm link carry wd c0 k parent).map (carry k parent)
          else none)).max?
      else none := by
  simp only [scoreF, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem extend (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool) (k : Nat) (a : Nat → Nat)
    (q : Nat) (ha : legalK adm link k a) (hq : adm (k+1) q = true) (hl : link k (a k) q = true) :
    legalK adm link (k+1) (fun t => if t = k+1 then q else a t) := by
  constructor
  · intro t ht
    dsimp only
    by_cases h : t = k+1
    · rw [if_pos h, h]
      exact hq
    · rw [if_neg h]
      exact ha.1 t (by omega)
  · intro t ht
    dsimp only
    by_cases h : t = k
    · subst h
      rw [if_neg (show ¬ t = t+1 by omega), if_pos rfl]
      exact hl
    · rw [if_neg (show ¬ t = k+1 by omega), if_neg (show ¬ t+1 = k+1 by omega)]
      exact ha.2 t (by omega)

theorem lim_ext (carry : Nat → Nat → Int → Int) (c0 : Int) (a : Nat → Nat) (k q : Nat) :
    limK carry c0 (fun t => if t = k+1 then q else a t) (k+1) = carry k (a k) (limK carry c0 a k) := by
  rw [lim_succ, lim_congr carry c0 _ a k (fun i hi => by
    show (if i = k+1 then q else a i) = a i
    exact if_neg (by omega))]
  rw [if_neg (show ¬ k = k+1 by omega)]

def InvK (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool) (carry : Nat → Nat → Int → Int)
    (wd : Nat → Nat) (c0 : Int) (k : Nat) : Prop :=
  ∀ q, (scoreF adm link carry wd c0 k q = none ↔ ¬ ∃ a, legalK adm link k a ∧ a k = q) ∧
    ∀ v, scoreF adm link carry wd c0 k q = some v →
      (∃ a, legalK adm link k a ∧ a k = q ∧ limK carry c0 a k = v) ∧
      ∀ b, legalK adm link k b → b k = q → limK carry c0 b k ≤ v

theorem inv0 (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool)
    (carry : Nat → Nat → Int → Int) (wd : Nat → Nat) (c0 : Int) :
    InvK adm link carry wd c0 0 := by
  intro q
  have e : scoreF adm link carry wd c0 0 q = if adm 0 q then some c0 else none := rfl
  rw [e]
  have legal0 : ∀ a, legalK adm link 0 a ↔ adm 0 (a 0) = true := by
    intro a
    constructor
    · intro h
      exact h.1 0 le_rfl
    · intro h
      exact ⟨fun t ht => by rw [show t = 0 by omega]; exact h, fun t ht => absurd ht (by omega)⟩
  by_cases hq : adm 0 q = true
  · rw [if_pos hq]
    refine ⟨⟨fun h => absurd h (by simp), fun h => absurd ⟨fun _ => q, (legal0 _).2 hq, rfl⟩ h⟩, ?_⟩
    intro v hv
    have hv' : c0 = v := Option.some.inj hv
    subst hv'
    exact ⟨⟨fun _ => q, (legal0 _).2 hq, rfl, rfl⟩, fun b _ _ => le_refl _⟩
  · rw [if_neg hq]
    refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => absurd hv (by simp)⟩
    rintro ⟨a, ha, rfl⟩
    exact hq ((legal0 a).1 ha)

theorem inv_succ (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool)
    (carry : Nat → Nat → Int → Int) (wd : Nat → Nat) (c0 : Int)
    (hadm : ∀ t p, adm t p = true → p < 2^(wd t))
    (hmono : ∀ t p c c', c ≤ c' → carry t p c ≤ carry t p c') (k : Nat)
    (ih : InvK adm link carry wd c0 k) : InvK adm link carry wd c0 (k+1) := by
  intro q
  have hex : (∃ a, legalK adm link (k+1) a ∧ a (k+1) = q) ↔
      adm (k+1) q = true ∧ ∃ p, link k p q = true ∧ ∃ a, legalK adm link k a ∧ a k = p := by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha.1 (k+1) le_rfl, a k, ha.2 k (by omega), a,
        ⟨fun t ht => ha.1 t (by omega), fun t ht => ha.2 t (by omega)⟩, rfl⟩
    · rintro ⟨hq, p, hl, a, ha, rfl⟩
      exact ⟨_, extend adm link k a q ha hq hl, by simp⟩
  rw [score_succ]
  by_cases hq : adm (k+1) q = true
  · rw [if_pos hq]
    refine ⟨?_, ?_⟩
    · simp only [List.max?_eq_none_iff, List.filterMap_eq_nil_iff]
      rw [hex]
      constructor
      · rintro h ⟨_, p, hl, a, ha, rfl⟩
        have hp := hadm k (a k) (ha.1 k le_rfl)
        have h1 := h (a k) (List.mem_range.2 hp)
        rw [if_pos hl] at h1
        have h2 := Option.map_eq_none_iff.1 h1
        exact ((ih (a k)).1.1 h2) ⟨a, ha, rfl⟩
      · intro h p _
        split_ifs with hl
        · rw [Option.map_eq_none_iff]
          exact (ih p).1.2 (fun ⟨a, ha, hap⟩ => h ⟨hq, p, hl, a, ha, hap⟩)
        · rfl
    · intro v hv
      rw [List.max?_eq_some_iff] at hv
      obtain ⟨hmem, hmax⟩ := hv
      simp only [List.mem_filterMap] at hmem
      obtain ⟨p, _, hp⟩ := hmem
      split_ifs at hp with hl
      cases hs : scoreF adm link carry wd c0 k p with
      | none =>
        rw [hs] at hp
        simp at hp
      | some u =>
        rw [hs, Option.map_some] at hp
        have hv : carry k p u = v := Option.some.inj hp
        obtain ⟨⟨a, ha, hap, hlim⟩, _⟩ := (ih p).2 u hs
        refine ⟨⟨_, extend adm link k a q ha hq (by rw [hap]; exact hl), by simp, ?_⟩, ?_⟩
        · rw [lim_ext, hap, hlim, hv]
        · intro b hb hbq
          have hbk : legalK adm link k b :=
            ⟨fun t ht => hb.1 t (by omega), fun t ht => hb.2 t (by omega)⟩
          have hlb := hb.2 k (by omega)
          rw [hbq] at hlb
          cases hs2 : scoreF adm link carry wd c0 k (b k) with
          | none => exact absurd ⟨b, hbk, rfl⟩ ((ih (b k)).1.1 hs2)
          | some u2 =>
            have hle := ((ih (b k)).2 u2 hs2).2 b hbk rfl
            rw [lim_succ]
            exact le_trans (hmono k (b k) _ _ hle) (hmax _ (List.mem_filterMap.2
              ⟨b k, List.mem_range.2 (hadm k (b k) (hb.1 k (by omega))), by simp [hlb, hs2]⟩))
  · rw [if_neg hq]
    refine ⟨⟨fun _ => ?_, fun _ => rfl⟩, fun v hv => absurd hv (by simp)⟩
    rw [hex]
    exact fun ⟨h, _⟩ => hq h

theorem part2 (adm : Nat → Nat → Bool) (link : Nat → Nat → Nat → Bool)
    (carry : Nat → Nat → Int → Int) (wd : Nat → Nat) (c0 : Int) (n : Nat)
    (hadm : ∀ t p, adm t p = true → p < 2^(wd t))
    (hmono : ∀ t p c c', c ≤ c' → carry t p c ≤ carry t p c') (q : Nat) (best : Int) :
    scoreF adm link carry wd c0 n q = some best ↔
      (∃ a, legalK adm link n a ∧ a n = q ∧ limK carry c0 a n = best) ∧
      ∀ b, legalK adm link n b → b n = q → limK carry c0 b n ≤ best := by
  have inv : InvK adm link carry wd c0 n := by
    induction n with
    | zero => exact inv0 adm link carry wd c0
    | succ k ih => exact inv_succ adm link carry wd c0 hadm hmono k ih
  constructor
  · intro h
    exact (inv q).2 best h
  · rintro ⟨⟨a, ha, haq, hlim⟩, hub⟩
    cases hs : scoreF adm link carry wd c0 n q with
    | none => exact absurd ⟨a, ha, haq⟩ ((inv q).1.1 hs)
    | some v =>
      obtain ⟨⟨a', ha', ha'q, hlim'⟩, hub'⟩ := (inv q).2 v hs
      have h1 := hub a' ha' ha'q
      have h2 := hub' a ha haq
      rw [hlim'] at h1
      rw [hlim] at h2
      rw [le_antisymm h1 h2]

theorem carry_mono (W : Nat → Nat → Nat → Int → Bool) (Cap : Nat → Int) :
    ∀ t p c c', c ≤ c' → carryA W Cap t p c ≤ carryA W Cap t p c' := by
  intro t p c c' h
  unfold carryA
  split_ifs
  · exact le_refl _
  · apply min_le_min_left
    have b1 := Bool.toNat_le (mixF (W t p 0) (c-1))
    have b2 := Bool.toNat_le (mixF (W t p 0) (c'-1))
    rcases eq_or_lt_of_le h with h | h
    · subst h
      exact le_refl _
    · omega

theorem word_ext (base : Int → Bool) (inj : Nat → Int → Bool) (edge : Nat → Int)
    (width : Nat → Nat) (t p e : Nat) (z : Int) (hz : z ≤ capF edge width t) :
    wordF base inj edge width t p e z = wordF base inj edge width t p 0 z := by
  unfold wordF
  split_ifs with h1 h2
  · rfl
  · rfl

theorem link_spec (base : Int → Bool) (inj : Nat → Int → Bool) (edge : Nat → Int)
    (width : Nat → Nat) (t p d : Nat) (h : linkF base inj edge width t p d = true) :
    ∃ comp : Nat, ∀ z ≤ capF edge width (t+1),
      evolveF (wordF base inj edge width t p comp) (inj t) z = wordF base inj edge width (t+1) d 0 z := by
  unfold linkF at h
  rw [List.any_eq_true] at h
  obtain ⟨comp, _, hc⟩ := h
  rw [List.all_eq_true] at hc
  refine ⟨comp, fun z hz => ?_⟩
  by_cases hzl : z ≤ min (edge t - 3) (edge (t+1))
  · have hz1 : z ≤ edge t - 3 := le_trans hzl (min_le_left _ _)
    have hz2 : z ≤ edge (t+1) := le_trans hzl (min_le_right _ _)
    have e2 : wordF base inj edge width (t+1) d 0 z = runF inj base (t+1) z := by
      unfold wordF
      rw [if_pos hz2]
    rw [e2, run_succ]
    apply evolve_congr _ rfl
    intro s _ hs2
    unfold wordF
    rw [if_pos (by omega)]
  · have e : ((z - min (edge t - 3) (edge (t+1)) - 1).toNat : Int) =
        z - min (edge t - 3) (edge (t+1)) - 1 := Int.toNat_of_nonneg (by omega)
    have hlt : (z - min (edge t - 3) (edge (t+1)) - 1).toNat <
        (capF edge width (t+1) - min (edge t - 3) (edge (t+1))).toNat := by omega
    have h2 := hc _ (List.mem_range.2 hlt)
    simp only [beq_iff_eq] at h2
    rwa [show min (edge t - 3) (edge (t+1)) + 1 +
      (((z - min (edge t - 3) (edge (t+1)) - 1).toNat : Nat) : Int) = z by omega] at h2

theorem adm_lt (width mask : Nat → Nat) (t p : Nat) (h : admF width mask t p = true) :
    p < 2^(width t) := by
  simp only [admF, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

end PEqualNP.Outside.L_meta_25606

open PEqualNP.Outside.L_meta_25606 in
theorem PEqualNP.Outside.L_meta_25606 :
    let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let step := fun (x inj : ℤ → Bool) (z : ℤ) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
    ∀ (n : ℕ) (base : ℤ → Bool) (inj : ℕ → ℤ → Bool) (edge : ℕ → ℤ)
        (width mask : ℕ → ℕ),
      let run := fun (x : ℤ → Bool) (rounds : ℕ) =>
        (List.range rounds).foldl (fun state tick => step state (inj tick)) x
      let cap := fun time => edge time + (width time : ℤ)
      let word := fun (layer pattern extraBits : ℕ) (z : ℤ) =>
        if z ≤ edge layer then run base layer z
        else if z ≤ cap layer then pattern.testBit (z-edge layer-1).toNat
        else extraBits.testBit (z-cap layer-1).toNat
      let admitted := fun (layerIndex label : ℕ) => decide (label < 2^(width layerIndex)) && (mask layerIndex).testBit label
      let link := fun (oldTime source dest : ℕ) =>
        let low := min (edge oldTime-3) (edge (oldTime+1))
        let extra := (cap (oldTime+1)+3-cap oldTime).toNat
        (List.range (2^extra)).any (fun completion =>
          (List.range (cap (oldTime+1)-low).toNat).all (fun offset =>
            let site := low+1+(offset : ℤ)
            step (word oldTime source completion) (inj oldTime) site == word (oldTime+1) dest 0 site))
      let carry := fun (fromTime fromPattern : ℕ) (certified : ℤ) =>
        if fromTime = 0 then cap 1 else
          min (cap (fromTime+1)) (certified-3 + ((mix (word fromTime fromPattern 0) (certified-1)).toNat : ℤ))
      let scores := (List.range n).foldl (fun (prev : ℕ → Option ℤ) stage child =>
        if admitted (stage+1) child then
          ((List.range (2^(width stage))).filterMap (fun parent =>
            if link stage parent child then (prev parent).map (carry stage parent) else none)).max?
        else none) (fun parent => if admitted 0 parent then some (cap 0) else none)
      let legal := fun (a : ℕ → ℕ) => (∀ t ≤ n, admitted t (a t) = true) ∧
        ∀ t < n, link t (a t) (a (t+1)) = true
      let limitAt := fun (a : ℕ → ℕ) (length : ℕ) =>
        (List.range length).foldl (fun previous index => carry index (a index) previous) (cap 0)
      (∀ a : ℕ → ℕ, legal a → ∃ initial : ℤ → Bool, ∀ t ≤ n, ∀ z ≤ limitAt a t,
        run initial t z = word t (a t) 0 z) ∧
      ∀ (q : ℕ) (best : ℤ), scores q = some best ↔
        (∃ a : ℕ → ℕ, legal a ∧ a n = q ∧ limitAt a n = best) ∧
        ∀ b : ℕ → ℕ, legal b → b n = q → limitAt b n ≤ best := by
  intro mix step n base inj edge width mask run cap word admitted link carry scores legal limitAt
  exact ⟨fun a ha => part1 inj (wordF base inj edge width) (capF edge width)
      (linkF base inj edge width) n a (word_ext base inj edge width)
      (link_spec base inj edge width) ha.2,
    fun q best => part2 (admF width mask) (linkF base inj edge width)
      (carryA (wordF base inj edge width) (capF edge width)) width (capF edge width 0) n
      (adm_lt width mask) (carry_mono _ _) q best⟩
