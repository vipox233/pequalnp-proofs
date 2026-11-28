import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25605_aux

-- The core definitions and bit lemmas adapt L_meta_25608.lean at
-- 4e38289c430e13b54d69b958b2cc4a9eb31dbfea.

private def mix (x : Int → Bool) (z : Int) : Bool :=
  xor (xor (x (z - 1)) (x z)) (x (z + 1))

private def evolve (x injection : Int → Bool) (z : Int) : Bool :=
  xor (xor (mix x z) (!(mix x (z + 1)) && mix x (z + 2))) (injection z)

private def block (width : Nat) (tape : Int → Bool) (edge : Int) : Nat :=
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge + 1 + (bitIndex : Int))).toNat <<< bitIndex)) 0

private def advance (w : Nat) (b : Int) (x inj : Int → Bool) (allowed : Nat) : Int × Nat :=
  let tails := (List.range (2 ^ (2 * w + 5))).filter (fun pattern => allowed.testBit (pattern % 2 ^ w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site - b - 1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b - 2 + (offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b - 3 + (((List.range (w + 5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)

private theorem block_spec (tape : Int → Bool) (edge : Int) : ∀ w : Nat,
    block w tape edge < 2 ^ w ∧
    ∀ k : Nat, (block w tape edge).testBit k = if k < w then tape (edge + 1 + (k : Int)) else false := by
  intro w
  induction w with
  | zero =>
    refine ⟨by simp [block], fun k => by simp [block]⟩
  | succ w ih =>
    rcases ih with ⟨hlt, hbit⟩
    have hstep : block (w + 1) tape edge =
        block w tape edge ||| ((tape (edge + 1 + (w : Int))).toNat <<< w) := by
      dsimp only [block]
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    set bv : Bool := tape (edge + 1 + (w : Int))
    have hsh : (bv.toNat <<< w) < 2 ^ (w + 1) := by
      rw [Nat.shiftLeft_eq, Nat.pow_succ']
      cases bv <;> simp [Bool.toNat]
    have hlt1 : block w tape edge < 2 ^ (w + 1) :=
      lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by omega) (by omega))
    refine ⟨Nat.or_lt_two_pow hlt1 hsh, fun k => ?_⟩
    rw [Nat.testBit_or, hbit k, Nat.testBit_shiftLeft]
    by_cases hk : k < w
    · have hk1 : k < w + 1 := by omega
      simp only [hk, hk1, ↓reduceIte, decide_eq_false (show ¬ w ≤ k by omega), Bool.false_and, Bool.or_false]
    · by_cases hkeq : k = w
      · subst hkeq
        simp only [lt_irrefl, ↓reduceIte, Nat.lt_succ_self, ge_iff_le, le_refl, decide_true,
          Bool.true_and, Nat.sub_self, Bool.false_or]
        change bv.toNat.testBit 0 = bv
        cases bv <;> rfl
      · have hnot1 : ¬ k < w + 1 := by omega
        have hbm : bv.toNat.testBit (k - w) = false := by
          apply Nat.testBit_lt_two_pow
          have h1 : bv.toNat < 2 ^ 1 := by cases bv <;> decide
          exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) (by omega))
        simp only [hk, hnot1, ↓reduceIte, hbm, Bool.and_false, Bool.or_false]

private theorem foldl_mask_testBit (l : List Nat) (f : Nat → Nat) (acc m : Nat) :
    (l.foldl (fun a c => a ||| ((1 : Nat) <<< f c)) acc).testBit m =
      (acc.testBit m || l.any (fun c => decide (f c = m))) := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, List.any_cons]
    have hbit1 : (decide (f c ≤ m) && (1 : Nat).testBit (m - f c)) = decide (f c = m) := by
      by_cases heq : f c = m
      · subst heq; simp
      · by_cases hle : f c ≤ m
        · have hpos : 1 ≤ m - f c := by omega
          have hz : (1 : Nat).testBit (m - f c) = false :=
            Nat.testBit_lt_two_pow (lt_of_lt_of_le (by omega : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by omega) hpos))
          simp [heq, hle, hz]
        · simp [heq, hle]
    rw [hbit1, Bool.or_assoc]
private theorem evolve_congr {x1 x2 inj : Int → Bool} {z : Int}
    (hm1 : x1 (z - 1) = x2 (z - 1))
    (h0 : x1 z = x2 z)
    (hp1 : x1 (z + 1) = x2 (z + 1))
    (hp2 : x1 (z + 2) = x2 (z + 2))
    (hp3 : x1 (z + 3) = x2 (z + 3)) :
    evolve x1 inj z = evolve x2 inj z := by
  have hz1 : z + 1 - 1 = z := by omega
  have hz2 : z + 1 + 1 = z + 2 := by omega
  have hz3 : z + 2 - 1 = z + 1 := by omega
  have hz4 : z + 2 + 1 = z + 3 := by omega
  simp only [evolve, mix, hz1, hz2, hz3, hz4, hm1, h0, hp1, hp2, hp3]

private def fits (w : Nat) (b : Int) (x : Int → Bool) (mask : Nat) (y : Int → Bool) : Prop :=
  (∀ pos ≤ b, y pos = x pos) ∧ mask.testBit (block w y b) = true

private def EqTo (a b : Int → Bool) (z : Int) : Prop := ∀ j ≤ z, a j = b j

private theorem evolve_prefix {a b inj : Int → Bool} {z : Int} (h : EqTo a b (z+3)) :
    EqTo (evolve a inj) (evolve b inj) z := by
  intro j hj
  exact evolve_congr (h _ (by omega)) (h _ (by omega)) (h _ (by omega))
    (h _ (by omega)) (h _ (by omega))

private theorem evolve_diff_at {x y inj : Int → Bool} {z : Int}
    (hd : y (z - 1) ≠ x (z - 1)) (he : ∀ j > z - 1, y j = x j) :
    evolve y inj z ≠ evolve x inj z := by
  intro h
  have hz1 : z + 1 - 1 = z := by omega
  have hz2 : z + 1 + 1 = z + 2 := by omega
  have hz3 : z + 2 - 1 = z + 1 := by omega
  have hz4 : z + 2 + 1 = z + 3 := by omega
  have h0 := he z (by omega)
  have hp1 := he (z + 1) (by omega)
  have hp2 := he (z + 2) (by omega)
  have hp3 := he (z + 3) (by omega)
  simp only [evolve, mix, hz1, hz2, hz3, hz4, h0, hp1, hp2, hp3, Bool.xor_left_inj] at h
  exact hd h

private theorem evolve_rightmost {x y inj : Int → Bool} {p : Int}
    (hd : y p ≠ x p) (he : ∀ j > p, y j = x j) :
    evolve y inj (p + 1) ≠ evolve x inj (p + 1) ∧
      ∀ j > p + 1, evolve y inj j = evolve x inj j := by
  constructor
  · apply evolve_diff_at
    · simpa only [show p + 1 - 1 = p by omega] using hd
    · intro j hj
      exact he j (by omega)
  · intro j hj
    apply evolve_congr <;> apply he <;> omega

private def run (inj : Nat → Int → Bool) (length : Nat) (seed : Int → Bool) : Int → Bool :=
  (List.range length).foldl (fun st tick => evolve st (inj tick)) seed

private theorem run_succ (inj : Nat → Int → Bool) (n : Nat) (seed : Int → Bool) :
    run inj (n + 1) seed = evolve (run inj n seed) (inj n) := by
  dsimp only [run]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_eqTo {x y : Int → Bool} {b : Int} (inj : Nat → Int → Bool)
    (n : Nat) (he : EqTo y x b) : EqTo (run inj n y) (run inj n x) (b - 3 * (n : Int)) := by
  induction n with
  | zero => simpa [run] using he
  | succ n ih =>
    intro j hj
    rw [run_succ, run_succ]
    apply evolve_congr <;> apply ih <;> omega

private theorem run_rightmost {x y : Int → Bool} {p : Int} (inj : Nat → Int → Bool) (n : Nat)
    (hd : y p ≠ x p) (he : ∀ j > p, y j = x j) :
    run inj n y (p + (n : Int)) ≠ run inj n x (p + (n : Int)) ∧
      ∀ j > p + (n : Int), run inj n y j = run inj n x j := by
  induction n with
  | zero => simpa [run] using And.intro hd he
  | succ n ih =>
    have hp : p + (n.succ : Int) = (p + (n : Int)) + 1 := by omega
    change run inj (n + 1) y (p + (n.succ : Int)) ≠
        run inj (n + 1) x (p + (n.succ : Int)) ∧
      ∀ j > p + (n.succ : Int), run inj (n + 1) y j = run inj (n + 1) x j
    rw [hp, run_succ, run_succ]
    exact evolve_rightmost ih.1 ih.2

private def RealEdge (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (length : Nat) (edge : Int) : Prop :=
  (∀ seed, fits u b x mask seed → ∀ z ≤ edge, run inj length seed z = run inj length x z) ∧
  (∃ seed, fits u b x mask seed ∧ run inj length seed (edge + 1) ≠ run inj length x (edge + 1))

private theorem run_realEdge (u n : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (hx : mask.testBit (block u x b) = true) :
    ∃ E, RealEdge u b x mask inj n E ∧ E ≤ b + (u : Int) + (n : Int) := by
  classical
  let p : Int := b + (u : Int) + 1
  let seed : Int → Bool := fun j => if j = p then !(x j) else x j
  have hseed_eq (j : Int) (hj : j ≠ p) : seed j = x j := by simp [seed, hj]
  have hblock : block u seed b = block u x b := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [(block_spec seed b u).2 k, (block_spec x b u).2 k]
    by_cases hk : k < u
    · simpa only [ite_eq_left hk] using hseed_eq (b + 1 + (k : Int)) (by dsimp [p]; omega)
    · simp only [ite_eq_right hk]
  have hseed : fits u b x mask seed := by
    refine ⟨fun j hj => hseed_eq j (by dsimp [p]; omega), ?_⟩
    rwa [hblock]
  have hflip : seed p ≠ x p := by
    simp only [seed, ite_eq_left rfl]
    cases x p <;> decide
  have hright : ∀ j > p, seed j = x j := fun j hj => hseed_eq j (by omega)
  have hupper := (run_rightmost inj n hflip hright).1
  let lo : Int := b - 3 * (n : Int)
  let bad : Nat → Prop := fun k => ∃ y, fits u b x mask y ∧
    run inj n y (lo + (k : Int) + 1) ≠ run inj n x (lo + (k : Int) + 1)
  have htop : bad (u + 4 * n) := by
    have hsite : lo + ((u + 4 * n : Nat) : Int) + 1 = p + (n : Int) := by
      dsimp [lo, p]
      omega
    exact ⟨seed, hseed, by simpa only [hsite] using hupper⟩
  have hex : ∃ k, bad k := ⟨u + 4 * n, htop⟩
  have hmin : Nat.find hex ≤ u + 4 * n := Nat.find_min' hex htop
  refine ⟨lo + (Nat.find hex : Int), ⟨?_, Nat.find_spec hex⟩, ?_⟩
  · intro y hy z hz
    by_cases hlo : z ≤ lo
    · exact run_eqTo inj n hy.1 z hlo
    · by_contra hdiff
      let k : Nat := (z - lo - 1).toNat
      have hk : (k : Int) = z - lo - 1 := Int.toNat_of_nonneg (by omega)
      have hsite : lo + (k : Int) + 1 = z := by omega
      have hbad : bad k := ⟨y, hy, by simpa only [hsite] using hdiff⟩
      exact Nat.find_min hex (show k < Nat.find hex by omega) hbad
  · dsimp [lo]
    omega
private def pad (u mask w : Nat) : Nat :=
  (List.range (2^w)).foldl (fun (acc pat : Nat) =>
    if mask.testBit (pat % (2^u)) then acc ||| ((1 : Nat) <<< pat) else acc) 0

private theorem pad_fold_filter (p : Nat → Bool) (l : List Nat) (acc : Nat) :
    l.foldl (fun a pat => if p pat then a ||| ((1 : Nat) <<< pat) else a) acc =
      (l.filter p).foldl (fun a pat => a ||| ((1 : Nat) <<< pat)) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a l ih =>
    cases ha : p a <;> simp [ha, ih]

private theorem pad_bit (u mask w pat : Nat) (h : pat < 2^w) :
    (pad u mask w).testBit pat = true ↔ mask.testBit (pat % 2^u) = true := by
  unfold pad
  rw [pad_fold_filter]
  have hb := foldl_mask_testBit
    ((List.range (2^w)).filter (fun p => mask.testBit (p % 2^u))) id 0 pat
  simp only [id_eq] at hb
  rw [hb]
  simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, List.mem_filter,
    List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨q, ⟨_, hq⟩, rfl⟩
    exact hq
  · intro hp
    exact ⟨pat, ⟨h, hp⟩, rfl⟩

private theorem block_mod (u w : Nat) (huw : u ≤ w) (tape : Int → Bool) (b : Int) :
    block w tape b % 2^u = block u tape b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow, (block_spec tape b w).2 k, (block_spec tape b u).2 k]
  by_cases hk : k < u
  · simp [hk, lt_of_lt_of_le hk huw]
  · simp [hk]

private theorem fits_pad {u w : Nat} (huw : u ≤ w) (b : Int) (x : Int → Bool)
    (mask : Nat) (y : Int → Bool) :
    fits w b x (pad u mask w) y ↔ fits u b x mask y := by
  unfold fits
  rw [pad_bit u mask w (block w y b) (block_spec y b w).1, block_mod u w huw y b]



private theorem block_prefix {a c : Int → Bool} {b : Int} {w : Nat}
    (h : EqTo a c (b+w)) : block w a b = block w c b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [(block_spec a b w).2, (block_spec c b w).2]
  split
  · exact h _ (by omega)
  · rfl

private theorem prefix_from_block {a c : Int → Bool} {b : Int} {w : Nat}
    (he : EqTo a c b) (hb : block w a b = block w c b) : EqTo a c (b+w) := by
  intro j hj
  by_cases h : j ≤ b
  · exact he j h
  · let k := (j-b-1).toNat
    have hk : (k : Int) = j-b-1 := Int.toNat_of_nonneg (by omega)
    have hkw : k < w := by omega
    have hbit := congrArg (fun m : Nat => m.testBit k) hb
    simpa only [(block_spec a b w).2, (block_spec c b w).2, hkw, ite_true,
      show b+1+(k : Int) = j by omega] using hbit

private def trial (b : Int) (x : Int → Bool) (c : Nat) (site : Int) : Bool :=
  if site ≤ b then x site else c.testBit (site-b-1).toNat

private def tails (w : Nat) (allowed : Nat) : List Nat :=
  (List.range (2 ^ (2*w+5))).filter (fun c => allowed.testBit (c % 2^w))

private theorem trial_block (b : Int) (x : Int → Bool) (w c : Nat) :
    block w (trial b x c) b = c % 2^w := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [(block_spec _ b w).2, Nat.testBit_mod_two_pow]
  by_cases hk : k < w
  · simp [trial, hk, show ¬ b+1+(k : Int) ≤ b by omega,
      show (b+1+(k : Int)-b-1).toNat = k by omega]
  · simp [hk]

private theorem trial_fits {b : Int} {x : Int → Bool} {w allowed c : Nat}
    (hc : c ∈ tails w allowed) : fits w b x allowed (trial b x c) := by
  refine ⟨fun j hj => by simp [trial, hj], ?_⟩
  rw [trial_block]
  exact (List.mem_filter.mp hc).2

private theorem encode_trial {b : Int} {x y : Int → Bool} {w allowed : Nat}
    (hy : fits w b x allowed y) :
    ∃ c ∈ tails w allowed, EqTo (trial b x c) y (b+(2*w+5 : Nat)) := by
  let c := block (2*w+5) y b
  have he : EqTo (trial b x c) y (b+(2*w+5 : Nat)) := by
    apply prefix_from_block (w := 2*w+5)
    · intro j hj
      simp only [trial, hj, ite_true]
      exact (hy.1 j hj).symm
    · rw [trial_block, Nat.mod_eq_of_lt (block_spec y b (2*w+5)).1]
  refine ⟨c, List.mem_filter.mpr ⟨List.mem_range.mpr (block_spec y b _).1, ?_⟩, he⟩
  have hblock : block w (trial b x c) b = block w y b :=
    block_prefix (fun j hj => he j (by omega))
  rw [trial_block] at hblock
  rw [hblock]
  exact hy.2

private theorem range_first_failure (N : Nat) (p : Nat → Bool)
    (h : ∃ k < N, p k = false) :
    let m := ((List.range N).takeWhile p).length
    m < N ∧ p m = false ∧ ∀ k < m, p k = true := by
  let l := List.range N
  let q := fun k => !p k
  have hm : ((List.range N).takeWhile p).length = l.findIdx q := by
    rw [List.takeWhile_eq_take_findIdx_not, List.length_take, min_eq_left List.findIdx_le_length]
  have hf : l.findIdx q < l.length := by
    obtain ⟨k, hk, hp⟩ := h
    exact List.findIdx_lt_length_of_exists ⟨k, List.mem_range.mpr hk, by simp [q, hp]⟩
  have eqElem (k : Nat) (hk : k < l.length) : l[k] = k := by simp [l]
  dsimp only
  rw [hm]
  refine ⟨by simpa [l] using hf, ?_, ?_⟩
  · have ht := List.findIdx_getElem (p := q) (w := hf)
    simpa [q, eqElem] using ht
  · intro k hk
    have ht := List.not_of_lt_findIdx (p := q) hk
    simpa [q, eqElem] using ht

private theorem fits_flip {w allowed : Nat} {b : Int} {x : Int → Bool}
    (hx : fits w b x allowed x) :
    fits w b x allowed (fun j => if j = b+w+1 then !x j else x j) := by
  have h : EqTo (fun j => if j = b+w+1 then !x j else x j) x (b+w) := by
    intro j hj
    exact ite_eq_right (show j ≠ b+w+1 by omega)
  exact ⟨fun j hj => h j (by omega), by rw [block_prefix h]; exact hx.2⟩

private theorem advance_spec {w allowed : Nat} {b : Int} {x inj : Int → Bool}
    (hx : fits w b x allowed x) :
    let a := advance w b x inj allowed
    b-3 ≤ a.1 ∧
    (∀ seed, fits w b x allowed seed → EqTo (evolve seed inj) (evolve x inj) a.1) ∧
    (∃ seed, fits w b x allowed seed ∧ evolve seed inj (a.1+1) ≠ evolve x inj (a.1+1)) ∧
    (∀ y, fits w a.1 (evolve x inj) a.2 y ↔
      ∃ seed, fits w b x allowed seed ∧ EqTo y (evolve seed inj) (a.1+w)) := by
  let l := tails w allowed
  let f := fun k : Nat => l.all (fun c => evolve (trial b x c) inj (b-2+(k : Int)) ==
    evolve x inj (b-2+(k : Int)))
  let m := ((List.range (w+5)).takeWhile f).length
  let F := b-3+(m : Int)
  let M := l.foldl (fun acc c => acc ||| ((1 : Nat) <<< block w (evolve (trial b x c) inj) F)) 0
  change b-3 ≤ F ∧
    (∀ seed, fits w b x allowed seed → EqTo (evolve seed inj) (evolve x inj) F) ∧
    (∃ seed, fits w b x allowed seed ∧ evolve seed inj (F+1) ≠ evolve x inj (F+1)) ∧
    (∀ y, fits w F (evolve x inj) M y ↔
      ∃ seed, fits w b x allowed seed ∧ EqTo y (evolve seed inj) (F+w))
  have aux {y : Int → Bool} (hy : fits w b x allowed y) :
      ∃ c ∈ l, EqTo (evolve (trial b x c) inj) (evolve y inj) (b+(2*w+5 : Nat)-3) := by
    obtain ⟨c, hc, he⟩ := encode_trial hy
    exact ⟨c, hc, evolve_prefix (fun j hj => he j (by omega))⟩
  -- The last site checked is reached by flipping the first unrestricted bit.
  have hfail : f (w+4) = false := by
    let p := b+w+1
    let y := fun j => if j = p then !x j else x j
    have hy : fits w b x allowed y := fits_flip hx
    have hd : evolve y inj (p+1) ≠ evolve x inj (p+1) :=
      (evolve_rightmost (p := p) (by simp [y]) (fun j hj => by simp [y, ne_of_gt hj])).1
    obtain ⟨c, hc, he⟩ := aux hy
    apply Bool.eq_false_iff.mpr
    intro hit
    have hac := List.all_eq_true.mp hit c hc
    have hp : b-2+((w+4 : Nat) : Int) = p+1 := by dsimp [p]; omega
    have hp' : p+1 ≤ b+(2*w+5 : Nat)-3 := by dsimp [p]; omega
    rw [hp] at hac
    exact hd ((he _ hp').symm.trans (beq_iff_eq.mp hac))
  have hm : m < w+5 ∧ f m = false ∧ ∀ k < m, f k = true :=
    range_first_failure (w+5) f ⟨w+4, by omega, hfail⟩
  have hlower : b-3 ≤ F := by dsimp [F]; omega
  have hcap : F+w ≤ b+(2*w+5 : Nat)-3 := by dsimp [F]; omega
  have htrue (y : Int → Bool) (hy : fits w b x allowed y) :
      EqTo (evolve y inj) (evolve x inj) F := by
    intro j hj
    by_cases hj0 : j ≤ b-3
    · exact evolve_prefix (z := b-3) (fun k hk => hy.1 k (by omega)) j hj0
    · let k := (j-(b-2)).toNat
      have hk : (k : Int) = j-(b-2) := Int.toNat_of_nonneg (by omega)
      have hkm : k < m := by dsimp [F] at hj; omega
      obtain ⟨c, hc, he⟩ := aux hy
      have hac := List.all_eq_true.mp (hm.2.2 k hkm) c hc
      rw [show b-2+(k : Int) = j by omega] at hac
      exact (he j (by omega)).symm.trans (beq_iff_eq.mp hac)
  refine ⟨hlower, htrue, ?_, ?_⟩
  · have hh := hm.2.1
    change l.all (fun c => evolve (trial b x c) inj (b-2+(m : Int)) ==
      evolve x inj (b-2+(m : Int))) = false at hh
    rw [show b-2+(m : Int) = F+1 by dsimp [F]; omega] at hh
    by_contra h
    apply Bool.false_ne_true (hh.symm.trans ?_)
    apply List.all_eq_true.mpr
    intro c hc
    exact beq_iff_eq.mpr (by_contra fun hd => h ⟨_, trial_fits hc, hd⟩)
  · intro y
    have hmask (k : Nat) : M.testBit k = true ↔
        ∃ c ∈ l, block w (evolve (trial b x c) inj) F = k := by
      dsimp only [M]
      rw [foldl_mask_testBit]
      simp only [Nat.zero_testBit, Bool.false_or, List.any_eq_true, decide_eq_true_eq]
    constructor
    · intro hy
      obtain ⟨c, hc, he⟩ := (hmask _).mp hy.2
      have hfit := trial_fits (b := b) (x := x) hc
      refine ⟨_, hfit, prefix_from_block (fun j hj => ?_) he.symm⟩
      exact (hy.1 j hj).trans (htrue _ hfit j hj).symm
    · rintro ⟨seed, hs, he⟩
      obtain ⟨c, hc, hcEq⟩ := aux hs
      refine ⟨fun j hj => (he j (by omega)).trans (htrue _ hs j hj), (hmask _).mpr ⟨c, hc, ?_⟩⟩
      exact block_prefix (fun j hj => (hcEq j (by omega)).trans (he j hj).symm)

private abbrev State := (Int → Bool) × Int × Nat

private def track (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (w len : Nat) : State :=
  (List.range len).foldl (fun (st : State) tick =>
    let nxt := advance w st.2.1 st.1 (inj tick) st.2.2
    (evolve st.1 (inj tick), nxt.1, nxt.2)) (x, b, pad u mask w)

private def FitsState (w : Nat) (st : State) (y : Int → Bool) : Prop :=
  fits w st.2.1 st.1 st.2.2 y

private def step (w : Nat) (st : State) (a : Int → Bool) : State :=
  let h := advance w st.2.1 st.1 a st.2.2
  (evolve st.1 a, h.1, h.2)

private theorem track_succ (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (w n : Nat) :
    track u b x mask inj w (n+1) = step w (track u b x mask inj w n) (inj n) := by
  dsimp only [track]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

private theorem track_ref (u : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (w n : Nat) :
    (track u b x mask inj w n).1 = run inj n x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [track_succ, run_succ]
    change evolve (track u b x mask inj w n).1 (inj n) = _
    rw [ih]

private theorem step_spec {w : Nat} {st : State} {a : Int → Bool}
    (h : FitsState w st st.1) :
    let s := step w st a
    st.2.1-3 ≤ s.2.1 ∧
    (∀ y, FitsState w st y → EqTo (evolve y a) s.1 s.2.1) ∧
    (∃ y, FitsState w st y ∧ evolve y a (s.2.1+1) ≠ s.1 (s.2.1+1)) ∧
    (∀ y, FitsState w s y ↔ ∃ seed, FitsState w st seed ∧ EqTo y (evolve seed a) (s.2.1+w)) :=
  advance_spec h

private theorem track_spec {u w : Nat} {b : Int} {x : Int → Bool} {mask : Nat}
    {inj : Nat → Int → Bool} (huw : u ≤ w) (hx : fits u b x mask x) (k : Nat) :
    let first := (track u b x mask inj w 1).2.1
    let s := track u b x mask inj w (k+1)
    first-3*(k : Int) ≤ s.2.1 ∧
    (∀ seed, fits u b x mask seed → FitsState w s (run inj (k+1) seed)) ∧
    (∃ y, FitsState w s y ∧ y (s.2.1+1) ≠ s.1 (s.2.1+1)) ∧
    (∀ y, FitsState w s y → ∃ seed, fits u b x mask seed ∧
      EqTo y (run inj (k+1) seed) (first+w-3*(k : Int))) := by
  let t := track u b x mask inj w
  let f := (t 1).2.1
  change f-3*(k : Int) ≤ (t (k+1)).2.1 ∧ _ ∧ _ ∧ _
  induction k with
  | zero =>
    let s₀ := t 0
    let s₁ := step w s₀ (inj 0)
    have h₀ (y : Int → Bool) : FitsState w s₀ y ↔ fits u b x mask y := fits_pad huw b x mask y
    have hs := step_spec (a := inj 0) ((h₀ x).mpr hx)
    change f-3*(0 : Int) ≤ s₁.2.1 ∧
      (∀ seed, fits u b x mask seed → FitsState w s₁ (evolve seed (inj 0))) ∧
      (∃ y, FitsState w s₁ y ∧ y (s₁.2.1+1) ≠ s₁.1 (s₁.2.1+1)) ∧
      (∀ y, FitsState w s₁ y → ∃ seed, fits u b x mask seed ∧
        EqTo y (evolve seed (inj 0)) (f+w-3*(0 : Int)))
    have hf : f = s₁.2.1 := by
      dsimp only [f, t, s₁, s₀]
      rw [track_succ]
    rw [hf]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro seed h
      exact (hs.2.2.2 _).mpr ⟨seed, (h₀ _).mpr h, fun _ _ => rfl⟩
    · obtain ⟨seed, h, hd⟩ := hs.2.2.1
      exact ⟨_, (hs.2.2.2 _).mpr ⟨seed, h, fun _ _ => rfl⟩, hd⟩
    · intro y h
      obtain ⟨seed, ha, he⟩ := (hs.2.2.2 _).mp h
      change EqTo y (evolve seed (inj 0)) (s₁.2.1+w) at he
      exact ⟨seed, (h₀ _).mp ha, fun j hj => he j (by omega)⟩
  | succ k ih =>
    let s := t (k+1)
    let a := inj (k+1)
    let s' := step w s a
    have href : s.1 = run inj (k+1) x := track_ref u b x mask inj w (k+1)
    have hs : FitsState w s s.1 := href ▸ ih.2.1 x hx
    have h := step_spec (a := a) hs
    have ht : t (k+1+1) = s' := track_succ u b x mask inj w (k+1)
    change f-3*((k+1 : Nat) : Int) ≤ (t (k+1+1)).2.1 ∧
      (∀ seed, fits u b x mask seed → FitsState w (t (k+1+1)) (run inj (k+1+1) seed)) ∧
      (∃ y, FitsState w (t (k+1+1)) y ∧ y ((t (k+1+1)).2.1+1) ≠ (t (k+1+1)).1 ((t (k+1+1)).2.1+1)) ∧
      (∀ y, FitsState w (t (k+1+1)) y → ∃ seed, fits u b x mask seed ∧
        EqTo y (run inj (k+1+1) seed) (f+w-3*((k+1 : Nat) : Int)))
    rw [ht]
    have hlo : f-3*((k+1 : Nat) : Int) ≤ s'.2.1 := by
      have hi : f-3*(k : Int) ≤ s.2.1 := ih.1
      have hh : s.2.1-3 ≤ s'.2.1 := h.1
      omega
    refine ⟨hlo, ?_, ?_, ?_⟩
    · intro seed hseed
      rw [run_succ]
      exact (h.2.2.2 _).mpr ⟨_, ih.2.1 seed hseed, fun _ _ => rfl⟩
    · obtain ⟨seed, he, hd⟩ := h.2.2.1
      exact ⟨_, (h.2.2.2 _).mpr ⟨seed, he, fun _ _ => rfl⟩, hd⟩
    · intro y hy
      obtain ⟨z, hz, hyz⟩ := (h.2.2.2 _).mp hy
      obtain ⟨seed, hseed, hzs⟩ := ih.2.2.2 z hz
      change EqTo y (evolve z a) (s'.2.1+w) at hyz
      change EqTo z (run inj (k+1) seed) (f+w-3*(k : Int)) at hzs
      refine ⟨seed, hseed, ?_⟩
      rw [run_succ]
      intro j hj
      exact (hyz j (by omega)).trans
        (evolve_prefix (z := f+w-3*((k+1 : Nat) : Int))
           (fun l hl => hzs l (by omega)) j hj)

private theorem realEdge_unique {u n : Nat} {b : Int} {x : Int → Bool} {mask : Nat}
    {inj : Nat → Int → Bool} {E F : Int} (he : RealEdge u b x mask inj n E)
    (hf : RealEdge u b x mask inj n F) : E = F := by
  apply le_antisymm
  · by_contra h
    obtain ⟨y, hy, hd⟩ := hf.2
    exact hd (he.1 y hy _ (by omega))
  · by_contra h
    obtain ⟨y, hy, hd⟩ := he.2
    exact hd (hf.1 y hy _ (by omega))

private theorem track_first {u w : Nat} {b : Int} {x : Int → Bool} {mask : Nat}
    {inj : Nat → Int → Bool} (huw : u ≤ w) (hx : fits u b x mask x) :
    let f := (track u b x mask inj w 1).2.1
    b-3 ≤ f ∧ RealEdge u b x mask inj 1 f := by
  have hs := advance_spec (inj := inj 0) ((fits_pad huw b x mask x).mpr hx)
  refine ⟨hs.1, ⟨?_, ?_⟩⟩
  · intro y hy
    exact hs.2.1 y ((fits_pad huw b x mask y).mpr hy)
  · obtain ⟨y, hy, hd⟩ := hs.2.2.1
    exact ⟨y, (fits_pad huw b x mask y).mp hy, hd⟩

set_option maxHeartbeats 1000000 in
theorem solve (u n v : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool) (hn : 0 < n) (hm : mask.testBit (block u x b) = true) :
    let t := max 1 v
    ∃ E₁ E : Int, RealEdge u b x mask inj 1 E₁ ∧ RealEdge u b x mask inj n E ∧
      E ≤ b+(u : Int)+(n : Int) ∧
      let G := E-E₁+3*((n-1 : Nat) : Int)
      0 ≤ G ∧
      (∀ w : Nat, u ≤ w →
        let first := (track u b x mask inj w 1).2.1
        let final := track u b x mask inj w n
        let F := final.2.1
        let pass := F+(t : Int)+3*((n-1 : Nat) : Int) ≤ first+(w : Int)
        first = E₁ ∧ F ≤ E ∧
        (∀ z : Int, z+3*((n-1 : Nat) : Int) ≤ first+(w : Int) →
          ∀ observed : Int → Bool,
            (∃ y, fits w F final.1 final.2.2 y ∧ ∀ j ≤ z, y j = observed j) ↔
            (∃ seed, fits u b x mask seed ∧ ∀ j ≤ z, run inj n seed j = observed j)) ∧
        (pass ↔ G+(t : Int) ≤ (w : Int)) ∧
        (pass → F = E ∧
          ∀ val : Fin (2^v),
            (∃ word : Fin (2^w), final.2.2.testBit word.val = true ∧
              word.val % (2^v) = val.val) ↔
            (∃ seed, fits u b x mask seed ∧ block v (run inj n seed) E = val.val))) ∧
      G+(t : Int) ≤ (u : Int)+4*(n : Int)+(t : Int) := by
  have hx : fits u b x mask x := ⟨fun _ _ => rfl, hm⟩
  obtain ⟨E₁, hE₁, _⟩ := run_realEdge u 1 b x mask inj hm
  obtain ⟨E, hE, htop⟩ := run_realEdge u n b x mask inj hm
  let g : Int := 3*((n-1 : Nat) : Int)
  let t := max 1 v
  let G := E-E₁+g
  have hfirst (w : Nat) (hw : u ≤ w) : (track u b x mask inj w 1).2.1 = E₁ :=
    realEdge_unique (track_first hw hx (inj := inj)).2 hE₁
  have hfirstLower : b-3 ≤ E₁ := by
    rw [← hfirst u le_rfl]
    exact (track_first (w := u) le_rfl hx (inj := inj)).1
  have hstep (w : Nat) (hw : u ≤ w) :
      let s := track u b x mask inj w n
      E₁-g ≤ s.2.1 ∧
      (∀ seed, fits u b x mask seed → FitsState w s (run inj n seed)) ∧
      (∃ y, FitsState w s y ∧ y (s.2.1+1) ≠ s.1 (s.2.1+1)) ∧
      (∀ y, FitsState w s y → ∃ seed, fits u b x mask seed ∧
        EqTo y (run inj n seed) (E₁+w-g)) := by
    have hs := track_spec (inj := inj) hw hx (n-1)
    dsimp only at hs ⊢
    rwa [show n-1+1 = n by omega, hfirst w hw] at hs
  have hedge (w : Nat) (hw : u ≤ w) : (track u b x mask inj w n).2.1 ≤ E := by
    by_contra hnle
    obtain ⟨seed, hseed, hd⟩ := hE.2
    have hf := (hstep w hw).2.1 seed hseed
    exact hd ((hf.1 (E+1) (by omega)).trans (congrFun (track_ref u b x mask inj w n) (E+1)))
  have hG : 0 ≤ G := by
    have h := (hstep u le_rfl).1
    have he := hedge u le_rfl
    dsimp [G]
    omega
  refine ⟨E₁, E, hE₁, hE, htop, hG, ?_, ?_⟩
  · intro w hw
    let first := (track u b x mask inj w 1).2.1
    let s := track u b x mask inj w n
    let F := s.2.1
    let pass : Prop := F+(t : Int)+g ≤ first+(w : Int)
    change first = E₁ ∧ F ≤ E ∧ _ ∧ (pass ↔ G+(t : Int) ≤ (w : Int)) ∧ (pass → F = E ∧ _)
    have hf : first = E₁ := hfirst w hw
    have hFe : F ≤ E := hedge w hw
    have hs := hstep w hw
    have hlo : E₁-g ≤ F := hs.1
    have ht : 1 ≤ t := le_max_left _ _
    have hvt : v ≤ t := le_max_right _ _
    have hp (hp : pass) : F = E := by
      apply le_antisymm hFe
      by_contra h
      obtain ⟨y, hy, hd⟩ := hs.2.2.1
      obtain ⟨seed, hseed, he⟩ := hs.2.2.2 y hy
      have hz : F+1 ≤ E₁+w-g := by dsimp [pass] at hp; omega
      have hzE : F+1 ≤ E := by omega
      exact hd ((he _ hz).trans ((hE.1 seed hseed _ hzE).trans
        (congrFun (track_ref u b x mask inj w n) (F+1)).symm))
    refine ⟨hf, hFe, ?_, ⟨?_, ?_⟩, ?_⟩
    · intro z hz observed
      change z+g ≤ first+(w : Int) at hz
      constructor
      · rintro ⟨y, hy, hobs⟩
        obtain ⟨seed, hseed, he⟩ := hs.2.2.2 y hy
        exact ⟨seed, hseed, fun j hj => (he j (by omega)).symm.trans (hobs j hj)⟩
      · rintro ⟨seed, hseed, hobs⟩
        exact ⟨_, hs.2.1 seed hseed, hobs⟩
    · intro h
      have he := hp h
      dsimp [pass] at h
      dsimp [G]
      omega
    · intro h
      dsimp [pass]
      dsimp [G] at h
      omega
    · intro h
      have he := hp h
      refine ⟨he, ?_⟩
      have hz : F+v ≤ E₁+w-g := by dsimp [pass] at h; omega
      have hvw : v ≤ w := by omega
      intro val
      constructor
      · rintro ⟨word, hword, hval⟩
        let y := trial F s.1 word.val
        have hb : block w y F = word.val := by
          change block w (trial F s.1 word.val) F = word.val
          rw [trial_block, Nat.mod_eq_of_lt word.isLt]
        have hy : FitsState w s y := ⟨fun j hj => by simp [y, trial, F, hj], by
          change s.2.2.testBit (block w y F) = true
          rwa [hb]⟩
        obtain ⟨seed, hseed, hpref⟩ := hs.2.2.2 y hy
        refine ⟨seed, hseed, ?_⟩
        rw [← he, ← block_prefix (w := v) (fun j hj => hpref j (by omega)),
          ← block_mod v w hvw, hb, hval]
      · rintro ⟨seed, hseed, hval⟩
        let word : Fin (2^w) := ⟨block w (run inj n seed) F, (block_spec _ _ _).1⟩
        refine ⟨word, (hs.2.1 seed hseed).2, ?_⟩
        change block w (run inj n seed) F % 2^v = val.val
        rwa [block_mod v w hvw, he]
  · change G+(t : Int) ≤ (u : Int)+4*(n : Int)+(t : Int)
    dsimp [G, g]
    omega

end PEqualNP.Outside.L_meta_25605_aux

theorem PEqualNP.Outside.L_meta_25605 : (
let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x injection : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (injection z)
let block := fun (width : Nat) (tape : Int → Bool) (edge : Int) =>
  (List.range width).foldl (fun (number bitIndex : Nat) =>
    number ||| ((tape (edge+1+(bitIndex : Int))).toNat <<< bitIndex)) 0
let fits := fun (width : Nat) (edge : Int) (sample : Int → Bool) (mask : Nat) (tape : Int → Bool) =>
  (∀ pos ≤ edge, tape pos = sample pos) ∧ mask.testBit (block width tape edge) = true
let advance := fun (w : Nat) (b : Int) (x inj : Int → Bool) (allowed : Nat) =>
  let tails := (List.range (2 ^ (2*w+5))).filter (fun pattern => allowed.testBit (pattern % 2^w))
  let trial := fun (completionCode : Nat) (site : Int) =>
    if site ≤ b then x site else completionCode.testBit (site-b-1).toNat
  let reference := evolve x inj
  let fixed := fun (offset : Nat) =>
    let site := b-2+(offset : Int)
    tails.all (fun comparisonCode => evolve (trial comparisonCode) inj site == reference site)
  let newEdge := b-3+(((List.range (w+5)).takeWhile fixed).length : Int)
  let newMask := tails.foldl (fun acc outputCode =>
    acc ||| ((1 : Nat) <<< block w (evolve (trial outputCode) inj) newEdge)) 0
  (newEdge, newMask)
∀ (u n v : Nat) (b : Int) (x : Int → Bool) (mask : Nat)
    (inj : Nat → Int → Bool), 0 < n → mask.testBit (block u x b) = true →
  let run := fun (length : Nat) (seed : Int → Bool) =>
    (List.range length).foldl (fun st tick => evolve st (inj tick)) seed
  let realEdge := fun (length : Nat) (edge : Int) =>
    (∀ seed, fits u b x mask seed → ∀ z ≤ edge, run length seed z = run length x z) ∧
    (∃ seed, fits u b x mask seed ∧ run length seed (edge+1) ≠ run length x (edge+1))
  let pad := fun (w : Nat) => (List.range (2^w)).foldl (fun (acc pat : Nat) =>
    if mask.testBit (pat % (2^u)) then acc ||| ((1 : Nat) <<< pat) else acc) 0
  let track := fun (w len : Nat) =>
    (List.range len).foldl (fun (st : (Int → Bool) × Int × Nat) tick =>
      let nxt := advance w st.2.1 st.1 (inj tick) st.2.2
      (evolve st.1 (inj tick), nxt.1, nxt.2)) (x, b, pad w)
  let t := max 1 v
  ∃ E₁ E : Int, realEdge 1 E₁ ∧ realEdge n E ∧ E ≤ b+(u : Int)+(n : Int) ∧
    let G := E-E₁+3*((n-1 : Nat) : Int)
    0 ≤ G ∧
    (∀ w : Nat, u ≤ w →
      let first := (track w 1).2.1
      let final := track w n
      let F := final.2.1
      let pass := F+(t : Int)+3*((n-1 : Nat) : Int) ≤ first+(w : Int)
      first = E₁ ∧ F ≤ E ∧
      (∀ z : Int, z+3*((n-1 : Nat) : Int) ≤ first+(w : Int) →
        ∀ observed : Int → Bool,
          (∃ y, fits w F final.1 final.2.2 y ∧ ∀ j ≤ z, y j = observed j) ↔
          (∃ seed, fits u b x mask seed ∧ ∀ j ≤ z, run n seed j = observed j)) ∧
      (pass ↔ G+(t : Int) ≤ (w : Int)) ∧
      (pass → F = E ∧
        ∀ val : Fin (2^v),
          (∃ word : Fin (2^w), final.2.2.testBit word.val = true ∧
            word.val % (2^v) = val.val) ↔
          (∃ seed, fits u b x mask seed ∧ block v (run n seed) E = val.val))) ∧
    G+(t : Int) ≤ (u : Int)+4*(n : Int)+(t : Int)
) := by
  exact PEqualNP.Outside.L_meta_25605_aux.solve
