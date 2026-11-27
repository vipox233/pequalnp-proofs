import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25597

def mx (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evo (x inj : ℤ → Bool) (z : ℤ) : Bool :=
  xor (xor (mx x z) (!(mx x (z+1)) && mx x (z+2))) (inj z)

def ev5 (t0 t1 t2 t3 t4 k : Bool) : Bool :=
  xor (xor (xor (xor t0 t1) t2) (!(xor (xor t1 t2) t3) && xor (xor t2 t3) t4)) k

theorem evo_eq (x inj : ℤ → Bool) (z : ℤ) :
    evo x inj z = ev5 (x (z-1)) (x z) (x (z+1)) (x (z+2)) (x (z+3)) (inj z) := by
  unfold evo mx ev5
  rw [show z+1-1 = z by ring, show z+1+1 = z+2 by ring, show z+2-1 = z+1 by ring,
    show z+2+1 = z+3 by ring]

theorem ev5_lin (a t1 t2 t3 t4 k : Bool) :
    ev5 a t1 t2 t3 t4 k = xor a (ev5 false t1 t2 t3 t4 k) := by
  cases a <;> cases t1 <;> cases t2 <;> cases t3 <;> cases t4 <;> cases k <;> rfl

theorem ev5_sol (T b1 b2 b3 b4 k : Bool) :
    ev5 (xor T (ev5 false b1 b2 b3 b4 k)) b1 b2 b3 b4 k = T := by
  cases T <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases k <;> rfl

theorem evo_at (y inj : ℤ → Bool) (c : ℤ) (j : ℕ) : evo y inj (c+1+(j:ℤ)) =
    ev5 (y (c+(j:ℤ))) (y (c+((j+1:ℕ):ℤ))) (y (c+((j+2:ℕ):ℤ))) (y (c+((j+3:ℕ):ℤ)))
      (y (c+((j+4:ℕ):ℤ))) (inj (c+1+(j:ℤ))) := by
  have e : ∀ u u' : ℤ, u = u' → y u = y u' := fun _ _ h => h ▸ rfl
  rw [evo_eq, e (c+1+(j:ℤ)-1) (c+(j:ℤ)) (by ring), e (c+1+(j:ℤ)+1) (c+((j+2:ℕ):ℤ)) (by push_cast; ring),
    e (c+1+(j:ℤ)+2) (c+((j+3:ℕ):ℤ)) (by push_cast; ring),
    e (c+1+(j:ℤ)+3) (c+((j+4:ℕ):ℤ)) (by push_cast; ring),
    e (c+1+(j:ℤ)) (c+((j+1:ℕ):ℤ)) (by push_cast; ring)]

def bitsOf (c : ℤ) (p : ℕ) (z : ℤ) : Bool := p.testBit (z-c).toNat

theorem bitsOf_at (c : ℤ) (p i : ℕ) : bitsOf c p (c + (i:ℤ)) = p.testBit i := by
  simp [bitsOf]

def Good (inj : ℤ → Bool) (c : ℤ) (t : ℕ) (f : ℕ → Bool) (k : ℕ) : Prop :=
  ∀ j < k, ev5 (f j) (f (j+1)) (f (j+2)) (f (j+3)) (f (j+4)) (inj (c+1+(j:ℤ))) = t.testBit j

theorem uniq (inj : ℤ → Bool) (c : ℤ) (t : ℕ) (f g : ℕ → Bool) (k : ℕ)
    (hf : Good inj c t f k) (hg : Good inj c t g k)
    (h : ∀ i, k ≤ i → i < k+4 → f i = g i) : ∀ i, i < k+4 → f i = g i := by
  have key : ∀ d i, k ≤ i + d → i < k+4 → f i = g i := by
    intro d
    induction d with
    | zero => intro i h1 h2; exact h i (by omega) h2
    | succ d ih =>
      intro i h1 h2
      by_cases hd : k ≤ i + d
      · exact ih i hd h2
      · have hi : i < k := by omega
        have A := hf i hi
        have B := hg i hi
        rw [ih (i+1) (by omega) (by omega), ih (i+2) (by omega) (by omega),
          ih (i+3) (by omega) (by omega), ih (i+4) (by omega) (by omega), ← B, ev5_lin (f i),
          ev5_lin (g i)] at A
        have := congrArg (fun q => xor q (ev5 false (g (i+1)) (g (i+2)) (g (i+3)) (g (i+4))
          (inj (c+1+(i:ℤ))))) A
        simpa using this
  intro i hi
  exact key k i (by omega) hi

def stepR (c : ℤ) (inj : ℤ → Bool) (t : ℕ) (pw j : ℕ) : ℕ :=
  pw ||| ((xor (t.testBit j) (evo (bitsOf c pw) inj (c+1+(j:ℤ)))).toNat <<< j)

def Rec (c : ℤ) (inj : ℤ → Bool) (t k init : ℕ) : ℕ :=
  ((List.range k).reverse).foldl (stepR c inj t) init

theorem tb_sh (b : Bool) (j i : ℕ) : (b.toNat <<< j).testBit i = (decide (i = j) && b) := by
  cases b
  · simp
  · by_cases h : i = j
    · subst h; simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]
    · simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, h, Ne.symm h]

theorem stepR_bit (c : ℤ) (inj : ℤ → Bool) (t pw j i : ℕ) : (stepR c inj t pw j).testBit i =
    (pw.testBit i || (decide (i = j) &&
      xor (t.testBit j) (evo (bitsOf c pw) inj (c+1+(j:ℤ))))) := by
  unfold stepR; rw [Nat.testBit_or, tb_sh]

theorem Rec_succ (c : ℤ) (inj : ℤ → Bool) (t k init : ℕ) :
    Rec c inj t (k+1) init = Rec c inj t k (stepR c inj t init k) := by
  simp [Rec, List.range_succ]

theorem recA (c : ℤ) (inj : ℤ → Bool) (t : ℕ) : ∀ k init : ℕ, (∀ i < k, init.testBit i = false) →
    (∀ i, k ≤ i → (Rec c inj t k init).testBit i = init.testBit i) ∧
    Good inj c t (Rec c inj t k init).testBit k := by
  intro k
  induction k with
  | zero =>
    intro init _
    refine ⟨fun i _ => by simp [Rec], ?_⟩
    unfold Good; intro j hj; omega
  | succ k ih =>
    intro init hinit
    have hb := stepR_bit c inj t init k
    obtain ⟨A, B⟩ := ih (stepR c inj t init k)
      (fun i hi => by rw [hb]; simp [hinit i (by omega), show i ≠ k by omega])
    rw [Rec_succ]
    refine ⟨fun i hi => by rw [A i (by omega), hb]; simp [show i ≠ k by omega], ?_⟩
    unfold Good
    intro j hj
    by_cases hjk : j < k
    · exact B j hjk
    · have hj' : j = k := by omega
      rw [hj', A k le_rfl, A (k+1) (by omega), A (k+2) (by omega), A (k+3) (by omega),
        A (k+4) (by omega), hb, hb, hb, hb, hb, hinit k (by omega)]
      have hev : evo (bitsOf c init) inj (c+1+(k:ℤ)) = ev5 false (init.testBit (k+1))
          (init.testBit (k+2)) (init.testBit (k+3)) (init.testBit (k+4)) (inj (c+1+(k:ℤ))) := by
        rw [evo_at]; simp only [bitsOf_at]; rw [hinit k (by omega)]
      rw [hev]
      simp
      exact ev5_sol _ _ _ _ _ _

theorem recS (c : ℤ) (inj : ℤ → Bool) (t v s : ℕ) :
    (∀ i, (Rec c inj t v (s <<< v)).testBit (v+i) = s.testBit i) ∧
    Good inj c t (Rec c inj t v (s <<< v)).testBit v := by
  obtain ⟨A, B⟩ := recA c inj t v (s <<< v)
    (fun i hi => by simp [Nat.testBit_shiftLeft, Nat.not_le.mpr hi])
  exact ⟨fun i => by rw [A (v+i) (by omega), Nat.testBit_shiftLeft]; simp, B⟩

def blockF (v : ℕ) (x : ℤ → Bool) (c : ℤ) : ℕ :=
  (List.range v).foldl (fun (acc pos : ℕ) => acc ||| ((x (c+1+(pos : ℤ))).toNat <<< pos)) 0

theorem blockF_bit (x : ℤ → Bool) (c : ℤ) (i : ℕ) :
    ∀ v, (blockF v x c).testBit i = (decide (i < v) && x (c+1+(i:ℤ))) := by
  intro v
  induction v with
  | zero => simp [blockF]
  | succ v ih =>
    have e : blockF (v+1) x c = blockF v x c ||| ((x (c+1+(v:ℤ))).toNat <<< v) := by
      simp [blockF, List.range_succ]
    rw [e, Nat.testBit_or, ih, tb_sh]
    by_cases h : i = v
    · subst h; simp
    · have h2 : (i < v+1) ↔ (i < v) := by omega
      simp [h, h2]

theorem blockF_lt (v : ℕ) (x : ℤ → Bool) (c : ℤ) : blockF v x c < 2^v :=
  Nat.lt_pow_two_of_testBit _ (fun i hi => by rw [blockF_bit]; simp [Nat.not_lt.mpr hi])

theorem blk_iff (v : ℕ) (x : ℤ → Bool) (c : ℤ) (t : ℕ) (ht : t < 2^v) :
    (blockF v x c == t) = true ↔ ∀ j < v, x (c+1+(j:ℤ)) = t.testBit j := by
  rw [beq_iff_eq]
  constructor
  · intro h j hj
    have := blockF_bit x c j v
    rw [h] at this
    simpa [hj] using this.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [blockF_bit]
    by_cases hi : i < v
    · simp [hi, h i hi]
    · simp only [hi, decide_false, Bool.false_and]
      exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ht
        (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

def Cs (v : ℕ) (c : ℤ) (x : ℤ → Bool) (R : ℕ) : Bool :=
  (List.range (v+4)).all (fun coord => x (c+(coord:ℤ)) == R.testBit coord)

theorem Cs_iff (v : ℕ) (c : ℤ) (x : ℤ → Bool) (R : ℕ) :
    Cs v c x R = true ↔ ∀ coord < v+4, x (c+(coord:ℤ)) = R.testBit coord := by
  simp [Cs]

theorem charA (c : ℤ) (inj x : ℤ → Bool) (t v s : ℕ)
    (hC : Cs v c x (Rec c inj t v (s <<< v)) = true) :
    ∀ j < v, evo x inj (c+1+(j:ℤ)) = t.testBit j := by
  rw [Cs_iff] at hC
  obtain ⟨_, G⟩ := recS c inj t v s
  intro j hj
  rw [evo_at, hC j (by omega), hC (j+1) (by omega), hC (j+2) (by omega), hC (j+3) (by omega),
    hC (j+4) (by omega)]
  exact G j hj

theorem charB (c : ℤ) (inj x : ℤ → Bool) (t v s s' : ℕ) (hs : s < 16) (hs' : s' < 16)
    (h1 : Cs v c x (Rec c inj t v (s <<< v)) = true)
    (h2 : Cs v c x (Rec c inj t v (s' <<< v)) = true) : s = s' := by
  rw [Cs_iff] at h1 h2
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 4
  · rw [← (recS c inj t v s).1 i, ← (recS c inj t v s').1 i, ← h1 (v+i) (by omega),
      ← h2 (v+i) (by omega)]
  · have h16 : (16:ℕ) ≤ 2^i := by
      calc (16:ℕ) = 2^4 := by norm_num
        _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs h16),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs' h16)]

theorem charC (c : ℤ) (inj x : ℤ → Bool) (t v : ℕ)
    (hblk : ∀ j < v, evo x inj (c+1+(j:ℤ)) = t.testBit j) :
    Cs v c x (Rec c inj t v (blockF 4 x (c+(v:ℤ)-1) <<< v)) = true := by
  rw [Cs_iff]
  obtain ⟨A, G⟩ := recS c inj t v (blockF 4 x (c+(v:ℤ)-1))
  have Gf : Good inj c t (fun i => x (c + (i:ℤ))) v := by
    unfold Good
    intro j hj
    beta_reduce
    rw [← hblk j hj, evo_at]
  have := uniq inj c t (fun i => x (c+(i:ℤ))) (Rec c inj t v (blockF 4 x (c+(v:ℤ)-1) <<< v)).testBit
    v Gf G (by
      intro i h1 h2
      obtain ⟨d, rfl⟩ : ∃ d, i = v + d := ⟨i - v, by omega⟩
      show x (c + ((v+d:ℕ):ℤ)) = _
      rw [A d, blockF_bit, show c + (v:ℤ) - 1 + 1 + (d:ℤ) = c + ((v+d:ℕ):ℤ) by push_cast; ring]
      simp [show d < 4 by omega])
  intro coord hc
  exact this coord hc

def trialF (b : ℤ) (ref : ℤ → Bool) (lo : ℕ) (site : ℤ) : Bool :=
  if site ≤ b then ref site else lo.testBit (site-b-1).toNat

def pOK (v : ℕ) (b c : ℤ) (ref : ℤ → Bool) (R : ℕ) : Bool :=
  (List.range (v+4)).all (fun coord =>
    decide (b < c+(coord:ℤ)) || (R.testBit coord == ref (c+(coord:ℤ))))

theorem modEq_iff (A B s o n : ℕ) :
    ((A >>> s) % 2^n == (B >>> o) % 2^n) = true ↔ ∀ i < n, A.testBit (s+i) = B.testBit (o+i) := by
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have := congrArg (fun q => Nat.testBit q i) h
    simpa [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, hi] using this
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      Nat.testBit_shiftRight]
    by_cases hi : i < n
    · rw [h i hi]
    · simp [hi]

theorem P6 (v : ℕ) (b c : ℤ) (ref : ℤ → Bool) (R lo : ℕ) (hc : b-3 ≤ c) :
    Cs v c (trialF b ref lo) R = (pOK v b c ref R &&
      ((lo >>> (c-b-1).toNat) % 2^((c+(v:ℤ)+3-b).toNat - (c-b-1).toNat) ==
        (R >>> (b+1+((c-b-1).toNat:ℤ)-c).toNat) % 2^((c+(v:ℤ)+3-b).toNat - (c-b-1).toNat))) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, Cs_iff, modEq_iff]
  simp only [pOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · intro h
    refine ⟨fun coord hc' => ?_, fun i hi => ?_⟩
    · by_cases hb : b < c + coord
      · exact Or.inl hb
      · right
        have := h coord hc'
        unfold trialF at this
        rw [if_pos (by omega)] at this
        exact this.symm
    · have := h ((b+1+((c-b-1).toNat:ℤ)-c).toNat + i) (by omega)
      unfold trialF at this
      rw [if_neg (by omega), show (c + (((b+1+((c-b-1).toNat:ℤ)-c).toNat + i : ℕ) : ℤ) - b - 1).toNat
        = (c-b-1).toNat + i by omega] at this
      exact this
  · rintro ⟨h1, h2⟩ coord hc'
    unfold trialF
    by_cases hb : c + (coord:ℤ) ≤ b
    · rw [if_pos hb]
      rcases h1 coord hc' with h | h
      · omega
      · exact h.symm
    · rw [if_neg hb]
      have := h2 (coord - (b+1+((c-b-1).toNat:ℤ)-c).toNat) (by omega)
      rw [show (c-b-1).toNat + (coord - (b+1+((c-b-1).toNat:ℤ)-c).toNat)
          = (c + (coord:ℤ) - b - 1).toNat by omega,
        show (b+1+((c-b-1).toNat:ℤ)-c).toNat + (coord - (b+1+((c-b-1).toNat:ℤ)-c).toNat)
          = coord by omega] at this
      exact this

def cnt (n : ℕ) (p : ℕ → Bool) : ℕ := ∑ i ∈ Finset.range n, if p i = true then 1 else 0

theorem len_cnt (n : ℕ) (p : ℕ → Bool) : ((List.range n).filter p).length = cnt n p := by
  rw [← List.countP_eq_length_filter]
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, cnt, cnt, Finset.sum_range_succ]
    simp

theorem lsum (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem dsum (F : ℕ → ℕ) (K L : ℕ) :
    ∑ i ∈ Finset.range (K*L), F i = ∑ j ∈ Finset.range L, ∑ i ∈ Finset.range K, F (i + K*j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]

theorem or_add (x y i : ℕ) (h : x < 2^i) : x ||| (y <<< i) = x + y * 2^i := by
  rw [Nat.lor_comm, ← Nat.shiftLeft_add_eq_or_of_lt h, Nat.shiftLeft_eq]
  ring

theorem hlp (a K X L : ℕ) (ha : a < K) (hX : X < L) : a + K*X < K*L := by
  have : K*(X+1) ≤ K*L := Nat.mul_le_mul_left K (by omega)
  nlinarith

theorem dm (a s X : ℕ) (ha : a < 2^s) : (a + 2^s*X) / 2^s = X ∧ (a + 2^s*X) % 2^s = a := by
  constructor
  · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

def oldF (skip span outside middle : ℕ) : ℕ :=
  (outside % 2^skip) ||| (middle <<< skip) ||| ((outside >>> skip) <<< (skip+span))

theorem NL (mask w r m s G : ℕ) (hs : s ≤ w) (hr : s ≤ r) (hw : w ≤ m) (hrm : r ≤ m)
    (hG : G < 2^(r-s)) :
    cnt (2^m) (fun lo => mask.testBit (lo % 2^w) && ((lo >>> s) % 2^(r-s) == G)) =
    2^(m - max w r) * cnt (2^(w - (min w r - s)))
      (fun o => mask.testBit (oldF s (min w r - s) o (G % 2^(min w r - s)))) := by
  have e1 : 2^m = 2^s * (2^(r-s) * 2^(m-r)) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have step1 : cnt (2^m) (fun lo => mask.testBit (lo % 2^w) && ((lo >>> s) % 2^(r-s) == G)) =
      ∑ h ∈ Finset.range (2^(m-r)), ∑ a ∈ Finset.range (2^s),
        (if mask.testBit ((a + 2^s*(G + 2^(r-s)*h)) % 2^w) = true then 1 else 0) := by
    unfold cnt
    rw [e1, dsum, dsum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_eq_single G]
    · apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mem_range] at ha
      beta_reduce
      rw [Nat.shiftRight_eq_div_pow, (dm a s _ ha).1, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hG]
      simp
    · intro g hg hne
      rw [Finset.mem_range] at hg
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range] at ha
      beta_reduce
      rw [Nat.shiftRight_eq_div_pow, (dm a s _ ha).1, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hg]
      simp [hne]
    · intro hG'
      exact absurd (Finset.mem_range.mpr hG) hG'
  rw [step1]
  rcases le_or_gt w r with hwr | hwr
  · rw [min_eq_left hwr, max_eq_right hwr, show w - (w - s) = s by omega]
    have inner : ∀ h a, a < 2^s →
        (a + 2^s*(G + 2^(r-s)*h)) % 2^w = oldF s (w-s) a (G % 2^(w-s)) := by
      intro h a ha
      have ew : 2^w = 2^s * 2^(w-s) := by rw [← pow_add]; congr 1; omega
      have er : 2^(r-s) = 2^(w-s) * 2^(r-w) := by rw [← pow_add]; congr 1; omega
      rw [ew, Nat.mod_mul, (dm a s _ ha).1, (dm a s _ ha).2, er, mul_assoc,
        Nat.add_mul_mod_self_left]
      unfold oldF
      rw [Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt ha, Nat.zero_shiftLeft,
        Nat.or_zero, or_add _ _ _ ha]
      ring
    have : ∀ h ∈ Finset.range (2^(m-r)), (∑ a ∈ Finset.range (2^s),
        (if mask.testBit ((a + 2^s*(G + 2^(r-s)*h)) % 2^w) = true then 1 else 0)) =
        cnt (2^s) (fun o => mask.testBit (oldF s (w-s) o (G % 2^(w-s)))) := by
      intro h _
      unfold cnt
      apply Finset.sum_congr rfl
      intro a ha
      rw [inner h a (Finset.mem_range.mp ha)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]
  · rw [min_eq_right hwr.le, max_eq_left hwr.le, show w - (r - s) = s + (w - r) by omega,
      Nat.mod_eq_of_lt hG]
    have e2 : 2^(m-r) = 2^(w-r) * 2^(m-w) := by rw [← pow_add]; congr 1; omega
    rw [e2, dsum]
    have inner2 : ∀ h1 h2 a, a < 2^s → h1 < 2^(w-r) →
        (a + 2^s*(G + 2^(r-s)*(h1 + 2^(w-r)*h2))) % 2^w = oldF s (r-s) (a + 2^s*h1) G := by
      intro h1 h2 a ha hh1
      have ew : 2^w = 2^s * (2^(r-s) * 2^(w-r)) := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have hX : G + 2^(r-s)*h1 < 2^(r-s) * 2^(w-r) := hlp _ _ _ _ hG hh1
      have hY : a + 2^s*(G + 2^(r-s)*h1) < 2^s * (2^(r-s) * 2^(w-r)) := hlp _ _ _ _ ha hX
      have key : a + 2^s*(G + 2^(r-s)*(h1 + 2^(w-r)*h2)) =
          (a + 2^s*(G + 2^(r-s)*h1)) + 2^s * (2^(r-s) * 2^(w-r)) * h2 := by ring
      rw [key, ew, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hY]
      unfold oldF
      have hGs : a + G * 2^s < 2^(s + (r-s)) := by
        rw [pow_add]; have := hlp _ _ _ _ ha hG; linarith
      rw [(dm a s _ ha).2, Nat.shiftRight_eq_div_pow, (dm a s _ ha).1, or_add _ _ _ ha,
        or_add _ _ _ hGs, pow_add]
      ring
    have : ∀ h2 ∈ Finset.range (2^(m-w)), (∑ h1 ∈ Finset.range (2^(w-r)),
        ∑ a ∈ Finset.range (2^s),
        (if mask.testBit ((a + 2^s*(G + 2^(r-s)*(h1 + 2^(w-r)*h2))) % 2^w) = true then 1 else 0)) =
        cnt (2^(s + (w-r))) (fun o => mask.testBit (oldF s (r-s) o G)) := by
      intro h2 _
      unfold cnt
      rw [pow_add, dsum]
      apply Finset.sum_congr rfl
      intro h1 hh1
      apply Finset.sum_congr rfl
      intro a ha
      rw [inner2 h1 h2 a (Finset.mem_range.mp ha) (Finset.mem_range.mp hh1)]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, smul_eq_mul]

def histF (mask w skip span : ℕ) : Array ℕ :=
  ((List.range (2^span)).map (fun middle =>
    ((List.range (2^(w-span))).filter (fun outside =>
      mask.testBit (oldF skip span outside middle))).length)).toArray

theorem hist_get (mask w skip span mid : ℕ) (hmid : mid < 2^span) :
    (histF mask w skip span).getD mid 0 =
      cnt (2^(w-span)) (fun o => mask.testBit (oldF skip span o mid)) := by
  simp [histF, List.getElem?_range hmid, len_cnt]

theorem per_raw (c : ℤ) (inj x : ℤ → Bool) (t v : ℕ) (ht : t < 2^v) (M : Bool) :
    (if (M && (blockF v (evo x inj) c == t)) = true then 1 else 0) =
      ∑ s ∈ Finset.range 16, (if (M && Cs v c x (Rec c inj t v (s <<< v))) = true then 1 else 0) := by
  cases M
  · simp
  · simp only [Bool.true_and]
    by_cases hb : (blockF v (evo x inj) c == t) = true
    · rw [if_pos hb]
      have hblk := (blk_iff v (evo x inj) c t ht).mp hb
      have hs0 := charC c inj x t v hblk
      have s0lt : blockF 4 x (c+(v:ℤ)-1) < 16 := by
        have := blockF_lt 4 x (c+(v:ℤ)-1); norm_num at this; exact this
      rw [Finset.sum_eq_single (blockF 4 x (c+(v:ℤ)-1))]
      · rw [if_pos hs0]
      · intro s hs hne
        rw [if_neg]
        intro hC
        exact hne (charB c inj x t v _ _ (Finset.mem_range.mp hs) s0lt hC hs0)
      · intro hn
        exact absurd (Finset.mem_range.mpr s0lt) hn
    · rw [if_neg hb]
      symm
      apply Finset.sum_eq_zero
      intro s _
      rw [if_neg]
      intro hC
      exact hb ((blk_iff v (evo x inj) c t ht).mpr (charA c inj x t v s hC))

theorem main (w v m : ℕ) (b c : ℤ) (ref inj : ℤ → Bool) (mask : ℕ)
    (h1 : b-3 ≤ c) (h2 : c ≤ b+(w : ℤ)+1) (h3 : w ≤ m) (h4 : c+(v : ℤ)+3 ≤ b+(m : ℤ))
    (t : ℕ) (ht : t < 2^v) :
    ((List.range (2^m)).filter (fun raw =>
      mask.testBit (raw % 2^w) && (blockF v (evo (trialF b ref raw) inj) c == t))).length =
    2^(m - max w (c+(v:ℤ)+3-b).toNat) * ((List.range 16).map (fun suffix =>
      if pOK v b c ref (Rec c inj t v (suffix <<< v)) = true then
        (histF mask w (c-b-1).toNat (min w (c+(v:ℤ)+3-b).toNat - (c-b-1).toNat)).getD
          ((Rec c inj t v (suffix <<< v) >>> (b+1+((c-b-1).toNat:ℤ)-c).toNat) %
            2^(min w (c+(v:ℤ)+3-b).toNat - (c-b-1).toNat)) 0
      else 0)).sum := by
  rw [len_cnt, lsum, Finset.mul_sum]
  have part : cnt (2^m) (fun raw =>
      mask.testBit (raw % 2^w) && (blockF v (evo (trialF b ref raw) inj) c == t)) =
      ∑ s ∈ Finset.range 16, cnt (2^m) (fun raw =>
        mask.testBit (raw % 2^w) && Cs v c (trialF b ref raw) (Rec c inj t v (s <<< v))) := by
    unfold cnt
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro raw _
    exact per_raw c inj (trialF b ref raw) t v ht _
  rw [part]
  apply Finset.sum_congr rfl
  intro s _
  have hC := fun raw => P6 v b c ref (Rec c inj t v (s <<< v)) raw h1
  simp only [hC]
  cases hp : pOK v b c ref (Rec c inj t v (s <<< v))
  · simp [cnt]
  · simp only [Bool.true_and]
    rw [if_pos trivial]
    have hsp : min w (c+(v:ℤ)+3-b).toNat - (c-b-1).toNat ≤
        (c+(v:ℤ)+3-b).toNat - (c-b-1).toNat := by omega
    rw [NL mask w (c+(v:ℤ)+3-b).toNat m (c-b-1).toNat _ (by omega) (by omega) h3 (by omega)
      (Nat.mod_lt _ (by positivity)), Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 hsp),
      hist_get _ _ _ _ _ (Nat.mod_lt _ (by positivity))]

end PEqualNP.Outside.L_meta_25597

open PEqualNP.Outside.L_meta_25597 in
theorem PEqualNP.Outside.L_meta_25597 :
    let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
    let evolve := fun (x inj : ℤ → Bool) (z : ℤ) =>
      xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
    let block := fun (v : ℕ) (x : ℤ → Bool) (c : ℤ) =>
      (List.range v).foldl (fun (acc pos : ℕ) => acc ||| ((x (c+1+(pos : ℤ))).toNat <<< pos)) 0
    ∀ (w v m : ℕ) (b c : ℤ) (ref inj : ℤ → Bool) (mask : ℕ),
      b-3 ≤ c → c ≤ b+(w : ℤ)+1 → w ≤ m → c+(v : ℤ)+3 ≤ b+(m : ℤ) →
      let skip := (c-b-1).toNat
      let readEnd := (c+(v : ℤ)+3-b).toNat
      let span := min w readEnd - skip
      let hist := ((List.range (2^span)).map (fun middle =>
        ((List.range (2^(w-span))).filter (fun outside =>
          let old := (outside % 2^skip) ||| (middle <<< skip) |||
            ((outside >>> skip) <<< (skip+span))
          mask.testBit old)).length)).toArray
      let trial := fun (tailBits : ℕ) (site : ℤ) =>
        if site ≤ b then ref site else tailBits.testBit (site-b-1).toNat
      ∀ target : Fin (2^v),
        let recover := fun (suffix : ℕ) =>
          ((List.range v).reverse).foldl (fun (partialWord j : ℕ) =>
            let jz := c+1+(j : ℤ)
            let bits := fun (z : ℤ) => partialWord.testBit (z-c).toNat
            let chosen := xor (target.val.testBit j) (evolve bits inj jz)
            partialWord ||| (chosen.toNat <<< j)) (suffix <<< v)
        let price := fun (suffix : ℕ) =>
          let predWord := recover suffix
          let prefixOK := (List.range (v+4)).all (fun coord =>
            let z := c+(coord : ℤ)
            decide (b < z) || (predWord.testBit coord == ref z))
          let offset := (b+1+(skip : ℤ)-c).toNat
          let middle := (predWord >>> offset) % 2^span
          if prefixOK then hist.getD middle 0 else 0
        ((List.range (2^m)).filter (fun raw =>
          mask.testBit (raw % 2^w) && (block v (evolve (trial raw) inj) c == target.val))).length =
          2^(m - max w readEnd) * ((List.range 16).map price).sum
 := by
  intro mix evolve block w v m b c ref inj mask h1 h2 h3 h4 skip readEnd span hist trial target
  exact main w v m b c ref inj mask h1 h2 h3 h4 target.val target.isLt
