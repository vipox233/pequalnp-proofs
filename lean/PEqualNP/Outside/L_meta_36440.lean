import Mathlib

namespace PEqualNP.Outside.L_meta_36440_aux

def ch (f : Nat → Bool) (i : Nat) : Bool := xor (f i) (!(f (i+1)) && f (i+2))

def sh (f p : Nat → Bool) (i : Nat) : Bool := xor (f i) (p i)

def pack : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (pack n (fun i => f (i+1)))

lemma pack_lt (n : Nat) (f : Nat → Bool) : pack n f < 2^n := by
  induction n generalizing f with
  | zero => change 0 < 1; decide
  | succ n ih => exact Nat.bit_lt_two_pow_succ_iff.mpr (ih _)

lemma pack_bit (n : Nat) (f : Nat → Bool) {i : Nat} (hi : i<n) :
    (pack n f).testBit i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero _ _
    | succ i => exact (Nat.testBit_bit_succ _ _ _).trans (ih _ (by omega))

def rd (h l : Nat) (f : Nat → Bool) : Finset Nat :=
  (Finset.range l).filter (fun j => ch f (h-l+j))

lemma rd_eq {h l : Nat} {f g : Nat → Bool} (hl : l ≤ h) :
    rd h l f = rd h l g ↔ ∀ i, h-l ≤ i → i < h → ch f i = ch g i := by
  constructor
  · intro eq i lo hi
    have e := Finset.ext_iff.mp eq (i-(h-l))
    have m : i-(h-l) < l := by omega
    have t : h-l+(i-(h-l)) = i := by omega
    simpa [rd, m, t] using e
  · intro eq
    ext j
    simp only [rd, Finset.mem_filter, Finset.mem_range]
    by_cases hj : j < l
    · simp [hj, eq (h-l+j) (by omega) (by omega)]
    · simp [hj]

lemma pack_ch {h i : Nat} (f : Nat → Bool) (hi : i < h) :
    ch (pack (h+2) f).testBit i = ch f i := by
  simp only [ch, pack_bit _ _ (show i < h+2 by omega),
    pack_bit _ _ (show i+1 < h+2 by omega), pack_bit _ _ (show i+2 < h+2 by omega)]

lemma pack_sh_ch {h i : Nat} (f p : Nat → Bool) (hi : i < h) :
    ch (sh (pack (h+2) f).testBit p) i = ch (sh f p) i := by
  simp only [ch, sh, pack_bit _ _ (show i < h+2 by omega),
    pack_bit _ _ (show i+1 < h+2 by omega), pack_bit _ _ (show i+2 < h+2 by omega)]

def step (z s t : Bool) : Bool := xor z (!s && t)

lemma unstep (x s t : Bool) : step (xor x (!s && t)) s t = x := by
  cases x <;> cases s <;> cases t <;> decide

lemma step_ch (f : Nat → Bool) (i : Nat) : step (ch f i) (f (i+1)) (f (i+2)) = f i :=
  unstep _ _ _

def rev (z : Nat → Bool) (s t : Bool) : Nat → Bool
  | 0 => t
  | 1 => s
  | n+2 => step (z n) (rev z s t (n+1)) (rev z s t n)

def decode (h : Nat) (z : Nat → Bool) (s t : Bool) (i : Nat) : Bool :=
  rev z s t (h+1-i)

lemma decode_ch {h i : Nat} (z : Nat → Bool) (s t : Bool) (hi : i < h) :
    ch (decode h z s t) i = z (h-1-i) := by
  let n := h-1-i
  have e0 : h+1-i = n+2 := by dsimp [n]; omega
  have e1 : h+1-(i+1) = n+1 := by dsimp [n]; omega
  have e2 : h+1-(i+2) = n := by dsimp [n]; omega
  simp only [ch, decode, e0, e1, e2, rev, step]
  generalize z n = a
  generalize rev z s t (n+1) = b
  generalize rev z s t n = c
  cases a <;> cases b <;> cases c <;> decide

lemma decode_ends (h : Nat) (z : Nat → Bool) (s t : Bool) :
    decode h z s t h = s ∧ decode h z s t (h+1) = t := by
  simp [decode, show h+1-h = 1 by omega, rev]

lemma equal_down {h : Nat} {f g : Nat → Bool}
    (hz : ∀ i < h, ch f i = ch g i) (hs : f h = g h) (ht : f (h+1) = g (h+1)) :
    ∀ i < h+2, f i = g i := by
  have aux (n : Nat) : ∀ i ≤ h+1, h+1-i = n → f i = g i := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro i hi hn
      by_cases vip : i < h
      · rw [← step_ch f i, ← step_ch g i, hz i vip,
          ih (h+1-(i+1)) (by omega) (i+1) (by omega) rfl,
          ih (h+1-(i+2)) (by omega) (i+2) (by omega) rfl]
      · rcases (show i = h ∨ i = h+1 by omega) with rfl | rfl
        · exact hs
        · exact ht
  exact fun i hi => aux _ i (by omega) rfl

lemma bounded_ext {n x y : Nat} (hx : x < 2^n) (hy : y < 2^n)
    (e : ∀ i < n, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact e i hi
  · have hn : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (hx.trans_le hn), Nat.testBit_eq_false_of_lt (hy.trans_le hn)]

def mix (a b s t : Bool) : Bool := xor (b && s) (a && t)

lemma shifted_congr (f g p : Nat → Bool) (i : Nat) (e : ch f i = ch g i) :
    ch (sh f p) i = ch (sh g p) i ↔
      mix (p (i+1)) (p (i+2)) (f (i+1)) (f (i+2)) =
      mix (p (i+1)) (p (i+2)) (g (i+1)) (g (i+2)) := by
  simp only [ch, sh] at e ⊢
  unfold mix
  generalize f i = a at e ⊢
  generalize f (i+1) = b at e ⊢
  generalize f (i+2) = c at e ⊢
  generalize g i = d at e ⊢
  generalize g (i+1) = e' at e ⊢
  generalize g (i+2) = f' at e ⊢
  generalize p i = j
  generalize p (i+1) = k
  generalize p (i+2) = l
  revert e
  exact (by decide : ∀ a b c d e' f' j k l : Bool,
    xor a (!b && c) = xor d (!e' && f') →
    (xor (xor a j) (!(xor b k) && xor c l) = xor (xor d j) (!(xor e' k) && xor f' l) ↔
      xor (l && b) (k && c) = xor (l && e') (k && f'))) a b c d e' f' j k l

def tap (k start x j back : Nat) : Bool := x.testBit ((start + j + k - back) % k)

def pulse (k start : Nat) (col : Bool) (x j : Nat) : Bool :=
  if col then xor (tap k start x j 1) (xor (tap k start x j 3) (tap k start x j 5))
  else xor (tap k start x j 0) (xor (tap k start x j 1) (tap k start x j 2))

private theorem pulseOffset (k base i : Nat) (hk : 0 < k) (hi : i < k) :
    (((base + i) % k) + (k - base % k)) % k = i := by
  have hb := Nat.mod_lt base hk
  have he : base % k + i + (k - base % k) = i + k := by omega
  calc
    (((base + i) % k) + (k - base % k)) % k =
        (base + i + (k - base % k)) % k := Nat.mod_add_mod _ _ _
    _ = (base % k + i + (k - base % k)) % k := by
      simp only [Nat.add_assoc, Nat.mod_add_mod]
    _ = i := by rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

private def pulseBits (a b : Bool) : Nat → Bool
  | 0 => xor b a
  | 1 => !a
  | 2 => a
  | 5 => a
  | 6 => !a
  | _ => false

-- The eight positions are offsets from the first column tap. The four fixed
-- pulse bits are true, and the two remaining bits are independently prescribed.
theorem pulse_key (h k start : Nat) (hh : 4 ≤ h) (hk : h + 6 ≤ k) (a b : Bool) :
    ∃ x < 2 ^ k,
      pulse k start false x (h - 2) = a ∧
      pulse k start false x (h - 1) = true ∧
      pulse k start false x h = true ∧
      pulse k start true x (h - 2) = b ∧
      pulse k start true x (h - 1) = true ∧
      pulse k start true x h = true := by
  let base := start + (h - 2) + k - 5
  let f := fun n : Nat => pulseBits a b ((n + (k - base % k)) % k)
  let x := pack k f
  have hk0 : 0 < k := by omega
  have ht (j back i : Nat) (hji : start + j + k - back = base + i)
      (hi : i < 8) : tap k start x j back = pulseBits a b i := by
    have hik : i < k := by omega
    have hm : (base + i) % k < k := Nat.mod_lt _ hk0
    unfold tap
    rw [hji]
    change (pack k f).testBit ((base + i) % k) = pulseBits a b i
    rw [pack_bit k f hm]
    change pulseBits a b ((((base + i) % k) + (k - base % k)) % k) = pulseBits a b i
    rw [pulseOffset k base i hk0 hik]
  refine ⟨x, pack_lt k f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change xor (tap k start x (h - 2) 0)
      (xor (tap k start x (h - 2) 1) (tap k start x (h - 2) 2)) = a
    rw [ht (h - 2) 0 5 (by dsimp [base]; omega) (by decide),
      ht (h - 2) 1 4 (by dsimp [base]; omega) (by decide),
      ht (h - 2) 2 3 (by dsimp [base]; omega) (by decide)]
    cases a <;> rfl
  · change xor (tap k start x (h - 1) 0)
      (xor (tap k start x (h - 1) 1) (tap k start x (h - 1) 2)) = true
    rw [ht (h - 1) 0 6 (by dsimp [base]; omega) (by decide),
      ht (h - 1) 1 5 (by dsimp [base]; omega) (by decide),
      ht (h - 1) 2 4 (by dsimp [base]; omega) (by decide)]
    cases a <;> rfl
  · change xor (tap k start x h 0) (xor (tap k start x h 1) (tap k start x h 2)) = true
    rw [ht h 0 7 (by dsimp [base]; omega) (by decide),
      ht h 1 6 (by dsimp [base]; omega) (by decide),
      ht h 2 5 (by dsimp [base]; omega) (by decide)]
    cases a <;> rfl
  · change xor (tap k start x (h - 2) 1)
      (xor (tap k start x (h - 2) 3) (tap k start x (h - 2) 5)) = b
    rw [ht (h - 2) 1 4 (by dsimp [base]; omega) (by decide),
      ht (h - 2) 3 2 (by dsimp [base]; omega) (by decide),
      ht (h - 2) 5 0 (by rfl) (by decide)] <;>
      cases a <;> cases b <;> rfl
  · change xor (tap k start x (h - 1) 1)
      (xor (tap k start x (h - 1) 3) (tap k start x (h - 1) 5)) = true
    rw [ht (h - 1) 1 5 (by dsimp [base]; omega) (by decide),
      ht (h - 1) 3 3 (by dsimp [base]; omega) (by decide),
      ht (h - 1) 5 1 (by dsimp [base]; omega) (by decide)]
    cases a <;> rfl
  · change xor (tap k start x h 1) (xor (tap k start x h 3) (tap k start x h 5)) = true
    rw [ht h 1 6 (by dsimp [base]; omega) (by decide),
      ht h 3 4 (by dsimp [base]; omega) (by decide),
      ht h 5 2 (by dsimp [base]; omega) (by decide)]
    cases a <;> rfl

theorem pulse_col_eq (h k start x : Nat) (hh : 4 ≤ h) (hk : h + 6 ≤ k) :
    pulse k start true x h =
      xor (pulse k start false x (h - 3))
        (xor (pulse k start false x (h - 2)) (pulse k start false x (h - 1))) := by
  have ht (j back d : Nat) (he : start + j + k - back = start + h + k - d) :
      tap k start x j back = tap k start x h d :=
    congrArg (fun n : Nat => x.testBit (n % k)) he
  change xor (tap k start x h 1) (xor (tap k start x h 3) (tap k start x h 5)) =
    xor (xor (tap k start x (h - 3) 0)
      (xor (tap k start x (h - 3) 1) (tap k start x (h - 3) 2)))
      (xor (xor (tap k start x (h - 2) 0)
        (xor (tap k start x (h - 2) 1) (tap k start x (h - 2) 2)))
        (xor (tap k start x (h - 1) 0)
          (xor (tap k start x (h - 1) 1) (tap k start x (h - 1) 2))))
  rw [ht (h - 3) 0 3 (by omega), ht (h - 3) 1 4 (by omega), ht (h - 3) 2 5 (by omega),
    ht (h - 2) 0 2 (by omega), ht (h - 2) 1 3 (by omega), ht (h - 2) 2 4 (by omega),
    ht (h - 1) 0 1 (by omega), ht (h - 1) 1 2 (by omega), ht (h - 1) 2 3 (by omega)]
  have parity (p q r s t : Bool) :
      xor p (xor r t) =
        xor (xor r (xor s t)) (xor (xor q (xor r s)) (xor p (xor q r))) := by
    cases p <;> cases q <;> cases r <;> cases s <;> cases t <;> rfl
  exact parity _ _ _ _ _

private def columnFill (d : Nat → Bool) : Nat → Bool
  | 0 => true
  | 1 => true
  | i + 2 => bif d (i+1) then xor (d i) (columnFill d (i+1) && d (i+2)) else true

private theorem column_fill_seed (d : Nat → Bool) (i : Nat) (hi : d i = false) :
    columnFill d (i+1) = true := by
  cases i with
  | zero => rfl
  | succ i =>
    change d (i+1) = false at hi
    change columnFill d (i+2) = true
    simp only [columnFill, hi, Bool.cond_false]

private theorem column_fill_step : ∀ x a b u v w : Bool,
    (u = true → v = true) → (u = false → a = true) →
    b = (bif v then xor u (a && w) else true) →
    xor x (!a && b) = xor (xor x u) (!(xor a v) && xor b w) := by decide

private theorem column_shift_step (x q : Bool) : ∀ a b u v w r s : Bool,
    (s && v) = (r && w) →
    xor x (!a && b) = xor (xor x u) (!(xor a v) && xor b w) →
    xor (xor x q) (!(xor a r) && xor b s) =
      xor (xor (xor x u) q) (!(xor (xor a v) r) && xor (xor b w) s) := by
  cases x <;> cases q <;> decide

private theorem column_cross : ∀ a b v w : Bool,
    (v = true → a = true) → (w = true → b = true) →
    (v = true → w = true) → (a = true → w = true → v = true) →
    (b && v) = (a && w) := by decide

lemma miss (h : Nat) (p : Nat → Bool) (hh : 4 ≤ h) :
    ∃ f g : Nat → Bool, (f h ≠ g h ∨ f (h+1) ≠ g (h+1)) ∧
      (∀ i < h, ch f i = ch g i) ∧
      (∀ i < h, ch (sh f p) i = ch (sh g p) i) := by
  classical
  have mask : ∃ d : Nat → Bool, (d h = true ∨ d (h+1) = true) ∧
      (∀ i < h, d i = true → d (i+1) = true) ∧
      (∀ i < h, (p (i+2) && d (i+1)) = (p (i+1) && d (i+2))) := by
    cases ph : p h with
    | false =>
      let d (i : Nat) : Bool := decide (i = h+1)
      have hd0 (i : Nat) (hi : i ≤ h) : d i = false := by
        simp [d, show i ≠ h+1 by omega]
      refine ⟨d, Or.inr (by simp [d]), ?_, ?_⟩
      · intro i hi hd
        rw [hd0 i (by omega)] at hd
        cases hd
      · intro i hi
        rw [hd0 (i+1) (by omega)]
        by_cases hb : i+2 = h+1
        · have ha : i+1 = h := by omega
          simp [d, ha, hb, ph]
        · simp [d, hb]
    | true =>
      let run (i : Nat) : Prop := ∀ j, i ≤ j → j ≤ h → p j = true
      let d (i : Nat) : Bool := if i ≤ h then decide (run i) else p i
      have hd (i : Nat) (hi : i ≤ h) : d i = true ↔ run i := by
        simp only [d, if_pos hi, decide_eq_true_eq]
      have dh : d h = true := by
        apply (hd h (by omega)).mpr
        intro j hj1 hj2
        have hj : j = h := by omega
        simpa only [hj] using ph
      have hp (i : Nat) (hdi : d i = true) : p i = true := by
        by_cases hi : i ≤ h
        · exact ((hd i hi).mp hdi) i (by omega) hi
        · simpa only [d, if_neg hi] using hdi
      have hm (i : Nat) (hi : i < h) (hdi : d i = true) : d (i+1) = true := by
        apply (hd (i+1) (by omega)).mpr
        intro j hj1 hj2
        exact ((hd i (by omega)).mp hdi) j (by omega) hj2
      refine ⟨d, Or.inl dh, hm, ?_⟩
      intro i hi
      by_cases hlast : i+1 = h
      · have ha : d (i+1) = p (i+1) := by rw [hlast, dh, ph]
        have hb : d (i+2) = p (i+2) := by
          simp only [d, if_neg (show ¬ i+2 ≤ h by omega)]
        simpa only [ha, hb] using Bool.and_comm (p (i+2)) (p (i+1))
      · have hle : i+2 ≤ h := by omega
        apply column_cross _ _ _ _ (hp _) (hp _) (hm (i+1) (by omega))
        intro hpa hdb
        apply (hd (i+1) (by omega)).mpr
        intro j hj1 hj2
        by_cases hej : j = i+1
        · simpa only [hej] using hpa
        · exact ((hd (i+2) hle).mp hdb) j (by omega) hj2
  obtain ⟨d, hd, hm, hc⟩ := mask
  let f := columnFill d
  let g := sh f d
  have hneq (i : Nat) (hi : d i = true) : f i ≠ g i := by
    simp [g, sh, hi, Bool.xor_true]
  have hbase (i : Nat) (hi : i < h) : ch f i = ch g i := by
    exact column_fill_step (f i) (f (i+1)) (f (i+2)) (d i) (d (i+1)) (d (i+2))
      (hm i hi) (column_fill_seed d i) (by simp only [f, columnFill])
  refine ⟨f, g, hd.imp (hneq h) (hneq (h+1)), hbase, ?_⟩
  intro i hi
  exact column_shift_step (f i) (p i) (f (i+1)) (f (i+2))
    (d i) (d (i+1)) (d (i+2)) (p (i+1)) (p (i+2)) (hc i hi) (hbase i hi)


def zero (h : Nat) (u : Nat) : Finset Nat :=
  (Finset.range h).filter (fun j => ch u.testBit j)

lemma zero_rd (h u : Nat) : zero h u = rd h h u.testBit := by
  simp [zero, rd]

def replies (h : Nat) : Finset (Finset Nat) := (Finset.range (2^(h+2))).image (zero h)

def fiber (h : Nat) (z : Finset Nat) : Set Nat := {u | u ∈ Finset.range (2^(h+2)) ∧ zero h u = z}

def good (h l : Nat) (p : Nat → Bool) (z : Finset Nat) : Prop :=
  Set.InjOn (fun u : Nat => rd h l (sh u.testBit p)) (fiber h z)

lemma zero_pack {h : Nat} (f : Nat → Bool) : zero h (pack (h+2) f) = rd h h f := by
  rw [zero_rd]
  apply (rd_eq (Nat.le_refl h)).2
  exact fun i _ hi => pack_ch f hi

lemma pack_reply (h : Nat) (f : Nat → Bool) : rd h h f ∈ replies h :=
  Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (pack_lt _ _), zero_pack _⟩

lemma no_collision {h l : Nat} {p f g : Nat → Bool} {z : Finset Nat} (hl : l ≤ h)
    (eqz : rd h h f = z) (efg : ∀ i < h, ch f i = ch g i)
    (es : ∀ i, h-l ≤ i → i < h → ch (sh f p) i = ch (sh g p) i)
    (ne : f h ≠ g h ∨ f (h+1) ≠ g (h+1)) : ¬ good h l p z := by
  intro inj
  have ef : pack (h+2) f ∈ fiber h z := ⟨Finset.mem_range.mpr (pack_lt _ _), (zero_pack _).trans eqz⟩
  have eg : pack (h+2) g ∈ fiber h z := ⟨Finset.mem_range.mpr (pack_lt _ _),
    (zero_pack _).trans (((rd_eq (Nat.le_refl h)).2 (fun i _ hi => (efg i hi).symm)).trans eqz)⟩
  have e : pack (h+2) f = pack (h+2) g := inj ef eg ((rd_eq hl).2 (fun i lo hi => by
    rw [pack_sh_ch f p hi, pack_sh_ch g p hi, es i lo hi]))
  rcases ne with n | n
  · exact n ((pack_bit _ _ (show h < h+2 by omega)).symm.trans
      ((congrArg (fun u : Nat => u.testBit h) e).trans (pack_bit _ _ (by omega))))
  · exact n ((pack_bit _ _ (show h+1 < h+2 by omega)).symm.trans
      ((congrArg (fun u : Nat => u.testBit (h+1)) e).trans (pack_bit _ _ (by omega))))

lemma column_misses (h : Nat) (p : Nat → Bool) (hh : 4 ≤ h) :
    ∃ w ∈ replies h, ¬ good h h p w := by
  obtain ⟨f,g,ne,e0,e1⟩ := miss h p hh
  exact ⟨_, pack_reply h f, no_collision (Nat.le_refl h) rfl e0 (fun i _ hi => e1 i hi) ne⟩

lemma local_bits {h : Nat} (hh : 4 ≤ h) (f : Nat → Bool) :
    f (h-1) = step (ch f (h-1)) (f h) (f (h+1)) ∧
    f (h-2) = step (ch f (h-2)) (f (h-1)) (f h) ∧
    f (h-3) = step (ch f (h-3)) (f (h-2)) (f (h-1)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [show h-1+1=h by omega, show h-1+2=h+1 by omega] using (step_ch f (h-1)).symm
  · simpa only [show h-2+1=h-1 by omega, show h-2+2=h by omega] using (step_ch f (h-2)).symm
  · simpa only [show h-3+1=h-2 by omega, show h-3+2=h-1 by omega] using (step_ch f (h-3)).symm

def sig3 (z v a b c d s t : Bool) : Bool × Bool × Bool :=
  let x := step z s t
  let y := step v x s
  (mix a b y x, mix b c x s, mix c d s t)

def sig4 (z v w e a b c d s t : Bool) : Bool × (Bool × Bool × Bool) :=
  let x := step z s t
  let y := step v x s
  let q := step w y x
  (mix e a q y, sig3 z v a b c d s t)

lemma sig3_inj : ∀ z v d s t s' t' : Bool,
    sig3 z v z true true d s t = sig3 z v z true true d s' t' → s=s' ∧ t=t' := by decide

lemma sig4_collision : ∀ j w e a b c d : Bool,
    xor e (xor a b) = true → (e && a && b && c) ≠ j →
    ∃ s t s' t' : Bool, (s ≠ s' ∨ t ≠ t') ∧
      sig4 j j w e a b c d s t = sig4 j j w e a b c d s' t' := by decide

lemma read_sig3 {h : Nat} (hh : 4 ≤ h) (p f g : Nat → Bool)
    (ez : ch f (h-1) = ch g (h-1)) (ev : ch f (h-2) = ch g (h-2))
    (es : ∀ i, h-3 ≤ i → i < h → ch (sh f p) i = ch (sh g p) i)
    (e0 : ch f (h-3) = ch g (h-3)) :
    sig3 (ch f (h-1)) (ch f (h-2)) (p (h-2)) (p (h-1)) (p h) (p (h+1)) (f h) (f (h+1)) =
    sig3 (ch f (h-1)) (ch f (h-2)) (p (h-2)) (p (h-1)) (p h) (p (h+1)) (g h) (g (h+1)) := by
  have m0 := (shifted_congr f g p (h-3) e0).mp (es (h-3) (by omega) (by omega))
  have m1 := (shifted_congr f g p (h-2) ev).mp (es (h-2) (by omega) (by omega))
  have m2 := (shifted_congr f g p (h-1) ez).mp (es (h-1) (by omega) (by omega))
  simp only [show h-3+1=h-2 by omega, show h-3+2=h-1 by omega,
    show h-2+1=h-1 by omega, show h-2+2=h by omega,
    show h-1+1=h by omega, show h-1+2=h+1 by omega] at m0 m1 m2
  obtain ⟨fx,fy,_⟩ := local_bits hh f
  obtain ⟨gx,gy,_⟩ := local_bits hh g
  simp only [fy, gy, fx, gx, ← ez, ← ev] at m0 m1 m2
  exact Prod.ext m0 (Prod.ext m1 m2)

lemma good3 {h : Nat} (hh : 4 ≤ h) (p : Nat → Bool) (z : Finset Nat)
    (ha : p (h-2) = decide (h-1 ∈ z)) (hb : p (h-1) = true) (hc : p h = true) : good h 3 p z := by
  intro x hx y hy et
  have e : rd h h x.testBit = rd h h y.testBit :=
    (zero_rd h x).symm.trans (hx.2.trans (hy.2.symm.trans (zero_rd h y)))
  have ez := (rd_eq (Nat.le_refl h)).mp e
  have ev (i : Nat) (hi : i<h) := ez i (by omega) hi
  have et' := (rd_eq (show 3 ≤ h by omega)).mp et
  have sa : p (h-2) = ch x.testBit (h-1) := by
    rw [ha, ← hx.2]
    simp [zero, rd, show h-1<h by omega]
  have eq := read_sig3 hh p x.testBit y.testBit (ev _ (by omega)) (ev _ (by omega)) et' (ev _ (by omega))
  rw [sa, hb, hc] at eq
  obtain ⟨s,t⟩ := sig3_inj _ _ _ _ _ _ _ eq
  exact bounded_ext (Finset.mem_range.mp hx.1) (Finset.mem_range.mp hy.1) (equal_down ev s t)


lemma column_one {h : Nat} (hh : 4 ≤ h) (p : Nat → Bool) (w : Finset Nat)
    (hw : w ∈ replies h) (ok : good h h p w) : p h = true := by
  cases ph : p h with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨u, _, eqw⟩ := Finset.mem_image.mp hw
    let z := fun i => ch u.testBit (h-1-i)
    let f := decode h z true false
    let g := decode h z true true
    have base (i : Nat) (hi : i<h) : ch f i = ch u.testBit i := by
      simpa only [z, show h-1-(h-1-i) = i by omega] using decode_ch z true false hi
    have eq (i : Nat) (hi : i<h) : ch f i = ch g i :=
      (decode_ch z true false hi).trans (decode_ch z true true hi).symm
    obtain ⟨fs,ft⟩ := decode_ends h z true false
    obtain ⟨gs,gt⟩ := decode_ends h z true true
    have hp : f (h-1) = g (h-1) := by
      change rev z true false (h+1-(h-1)) = rev z true true (h+1-(h-1))
      rw [show h+1-(h-1)=2 by omega]
      simp [rev, step]
    have low (i : Nat) (hi : i≤h) : f i = g i := by
      have b : h-1+1=h := by omega
      apply equal_down (h := h-1) (fun j hj => eq j (by omega)) hp
      · rw [b]; exact fs.trans gs.symm
      · omega
    apply no_collision (Nat.le_refl h) (f := f) (g := g) ?_ eq ?_ (Or.inr ?_) ok
    · exact ((rd_eq (Nat.le_refl h)).2 (fun i _ hi => base i hi)).trans ((zero_rd h u).symm.trans eqw)
    · intro i _ hi
      apply (shifted_congr f g p i (eq i hi)).2
      by_cases he : i+1=h
      · rw [he, ph, low h (by omega)]
        simp [mix]
      · rw [low (i+1) (by omega), low (i+2) (by omega)]
    · change f (h+1) ≠ g (h+1)
      change f (h+1) = false at ft
      change g (h+1) = true at gt
      rw [ft, gt]
      decide

def rowReply (h : Nat) (j : Bool) : Finset Nat := rd h h (decode h (fun _ => j) false false)

lemma row_reply_mem (h : Nat) (j : Bool) : rowReply h j ∈ replies h := pack_reply _ _

lemma row_class {h : Nat} (hh : 4 ≤ h) (p : Nat → Bool) (j : Bool)
    (par : xor (p (h-3)) (xor (p (h-2)) (p (h-1))) = true)
    (ok : good h 4 p (rowReply h j)) : (p (h-3) && p (h-2) && p (h-1) && p h) = j := by
  by_contra ne
  obtain ⟨s,t,s',t',ends,cert⟩ := sig4_collision j j _ _ _ _ (p (h+1)) par ne
  let z : Nat → Bool := fun _ => j
  let f := decode h z s t
  let g := decode h z s' t'
  have hf (i : Nat) (hi : i<h) : ch f i = j := decode_ch z s t hi
  have hg (i : Nat) (hi : i<h) : ch g i = j := decode_ch z s' t' hi
  have eq (i : Nat) (hi : i<h) : ch f i = ch g i := (hf i hi).trans (hg i hi).symm
  obtain ⟨fs,ft⟩ := decode_ends h z s t
  obtain ⟨gs,gt⟩ := decode_ends h z s' t'
  change f h = s at fs
  change f (h+1) = t at ft
  change g h = s' at gs
  change g (h+1) = t' at gt
  obtain ⟨fx,fy,fq⟩ := local_bits hh f
  obtain ⟨gx,gy,gq⟩ := local_bits hh g
  have m0 := congrArg Prod.fst cert
  have m1 := congrArg (fun u => u.2.1) cert
  have m2 := congrArg (fun u => u.2.2.1) cert
  have m3 := congrArg (fun u => u.2.2.2) cert
  apply no_collision (show 4 ≤ h from hh) (f := f) (g := g) ?_ eq ?_ ?_ ok
  · apply (rd_eq (Nat.le_refl h)).2
    exact fun i _ hi => (hf i hi).trans (decode_ch z false false hi).symm
  · intro i lo hi
    apply (shifted_congr f g p i (eq i hi)).2
    rcases (show i=h-4 ∨ i=h-3 ∨ i=h-2 ∨ i=h-1 by omega) with rfl | rfl | rfl | rfl
    all_goals
      simp only [show h-4+1=h-3 by omega, show h-4+2=h-2 by omega,
        show h-3+1=h-2 by omega, show h-3+2=h-1 by omega,
        show h-2+1=h-1 by omega, show h-2+2=h by omega,
        show h-1+1=h by omega, show h-1+2=h+1 by omega,
        fq, gq, fy, gy, fx, gx, hf (h-3) (by omega), hf (h-2) (by omega), hf (h-1) (by omega),
        hg (h-3) (by omega), hg (h-2) (by omega), hg (h-1) (by omega), fs, ft, gs, gt]
    · exact m0
    · exact m1
    · exact m2
    · exact m3
  · rwa [fs,ft,gs,gt]


def works (h k start r c : Nat) (B : Finset Nat) : Prop :=
  B ⊆ Finset.range (2^k) ∧ ∀ z ∈ replies h, ∀ w ∈ replies h, ∃ x ∈ B,
    good h r (pulse k start false x) z ∧ good h c (pulse k start true x) w

lemma upper (h k start : Nat) (hh : 4 ≤ h) (hk : h+6 ≤ k) :
    ∃ B, B.card = 4 ∧ works h k start 3 3 B := by
  have keys (i : Bool × Bool) := pulse_key h k start hh hk i.1 i.2
  choose key hkbound h₁ h₂ h₃ h₄ h₅ h₆ using keys
  have inj : Function.Injective key := by
    intro a b eq
    apply Prod.ext
    · rw [← h₁ a, ← h₁ b, eq]
    · rw [← h₄ a, ← h₄ b, eq]
  refine ⟨Finset.univ.image key, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
    decide
  · intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hkbound i)
  · intro z _ w _
    let i : Bool × Bool := (decide (h-1 ∈ z), decide (h-1 ∈ w))
    exact ⟨key i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩,
      good3 hh _ _ (h₁ i) (h₂ i) (h₃ i), good3 hh _ _ (h₄ i) (h₅ i) (h₆ i)⟩

lemma lower (h k start : Nat) (hh : 4 ≤ h) (hk : h+6 ≤ k)
    (B : Finset Nat) (ok : works h k start 4 h B) : 4 ≤ B.card := by
  let mark (x : Nat) : Bool :=
    pulse k start false x (h-3) && pulse k start false x (h-2) &&
      pulse k start false x (h-1) && pulse k start false x h
  let cls (j : Bool) := B.filter (fun x => mark x = j)
  have cover (j : Bool) (w : Finset Nat) (hw : w ∈ replies h) :
      ∃ x ∈ cls j, good h h (pulse k start true x) w := by
    obtain ⟨x,hx,hr,hc⟩ := ok.2 _ (row_reply_mem h j) w hw
    have p := (pulse_col_eq h k start x hh hk).symm.trans (column_one hh _ w hw hc)
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, row_class hh _ j p hr⟩, hc⟩
  have many (j : Bool) : 1 < (cls j).card := by
    obtain ⟨x,hx,_⟩ := cover j _ (row_reply_mem h false)
    obtain ⟨w,hw,bad⟩ := column_misses h (pulse k start true x) hh
    obtain ⟨y,hy,good_y⟩ := cover j w hw
    exact Finset.one_lt_card.mpr ⟨x,hx,y,hy,fun e => bad (e ▸ good_y)⟩
  have dis : Disjoint (cls false) (cls true) := by
    apply Finset.disjoint_left.mpr
    intro x h0 h1
    exact Bool.false_ne_true ((Finset.mem_filter.mp h0).2.symm.trans (Finset.mem_filter.mp h1).2)
  have sub : cls false ∪ cls true ⊆ B :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have cnt := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at cnt
  have h0 := many false
  have h1 := many true
  omega

end PEqualNP.Outside.L_meta_36440_aux

open PEqualNP.Outside.L_meta_36440_aux

theorem PEqualNP.Outside.L_meta_36440 : ∀ (h k start : Nat), 4 ≤ h → h+6 ≤ k →
  let strips := Finset.range (2^(h+2))
  let keys := Finset.range (2^k)
  let tap := fun (x j back : Nat) => x.testBit ((start+j+k-back) % k)
  let pulse := fun (col : Bool) (x j : Nat) =>
    if col then xor (tap x j 1) (xor (tap x j 3) (tap x j 5))
    else xor (tap x j 0) (xor (tap x j 1) (tap x j 2))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let zero := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let replies := strips.image zero
  let fiber := fun (z : Finset Nat) => {u : Nat | u ∈ strips ∧ zero u = z}
  let tail := fun (col : Bool) (x len u : Nat) =>
    let bits := fun i : Nat => xor (u.testBit i) (pulse col x i)
    (Finset.range len).filter (fun j => chi bits (h-len+j))
  let works := fun (r c : Nat) (B : Finset Nat) =>
    B ⊆ keys ∧ ∀ z ∈ replies, ∀ w ∈ replies, ∃ x ∈ B,
      Set.InjOn (tail false x r) (fiber z) ∧ Set.InjOn (tail true x c) (fiber w)
  (∃ B, B.card = 4 ∧ works 3 3 B) ∧ ∀ B, works 4 h B → 4 ≤ B.card := by
  intro h k start hh hk
  change (∃ B, B.card = 4 ∧ works h k start 3 3 B) ∧
    ∀ B, works h k start 4 h B → 4 ≤ B.card
  exact ⟨upper h k start hh hk, lower h k start hh hk⟩
