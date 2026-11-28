import PEqualNP.Defs
import PEqualNP.Outside.L_lib_540
import PEqualNP.Outside.L_clb_087
import PEqualNP.Outside.L_lib_377

namespace PEqualNP.Outside.L_clb_125_aux

abbrev Row := Nat → Bool

def pat (n w word site : Nat) : Nat :=
  (List.range (w+1)).foldl (fun (acc bit : Nat) =>
    acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0

def parity (n w : Nat) (input : Nat → Row) : Bool :=
  ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
    input site (pat n w word site)))).length.testBit 0

def run (n p : Nat) {A : Type} (start : A)
    (step : Nat → Nat → A → Row → A) (input : Nat → Row) : A :=
  (List.range p).foldl (fun prev passId =>
    (List.range n).foldl (fun state site => step passId site state (input site)) prev) start

def Fits (n w p k : Nat) : Prop :=
  ∃ (start : Fin (2^k)) (step : Nat → Nat → Fin (2^k) → Row → Fin (2^k))
      (out : Fin (2^k) → Bool), ∀ input, out (run n p start step input) = parity n w input

lemma fold_encode {A B C : Type} (enc : A → B) (dec : B → A)
    (inverse : Function.LeftInverse dec enc) (f : A → C → A) (l : List C) (a : A) :
    l.foldl (fun b c => enc (f (dec b) c)) (enc a) = enc (l.foldl f a) := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => simpa only [List.foldl_cons, inverse a] using ih (f a c)

lemma run_encode {A B : Type} (enc : A → B) (dec : B → A)
    (inverse : Function.LeftInverse dec enc) (n p : Nat) (a : A)
    (step : Nat → Nat → A → Row → A) (input : Nat → Row) :
    run n p (enc a) (fun q i b row => enc (step q i (dec b) row)) input =
      enc (run n p a step input) := by
  unfold run
  generalize List.range p = passes
  induction passes generalizing a with
  | nil => rfl
  | cons q passes ih =>
    simp only [List.foldl_cons]
    rw [fold_encode enc dec inverse (fun st i => step q i st (input i))]
    exact ih _

lemma of_equiv {A : Type} {n w p k : Nat} (E : A ≃ Fin (2^k)) (a : A)
    (step : Nat → Nat → A → Row → A) (out : A → Bool)
    (h : ∀ input, out (run n p a step input) = parity n w input) : Fits n w p k := by
  refine ⟨E a, fun q i b row => E (step q i (E.symm b) row), out ∘ E.symm, ?_⟩
  intro input
  rw [run_encode E E.symm E.left_inv]
  exact (congrArg out (E.symm_apply_apply _)).trans (h input)

lemma one_fit (w p : Nat) (hp : 0 < p) : Fits 1 w p 1 := by
  apply of_equiv (Fintype.equivFinOfCardEq (α := Bool) (by decide)) false
    (fun _ _ _ row => parity 1 w (fun _ => row)) id
  intro input
  obtain ⟨q, rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
  simp only [run, List.range_one]
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, id_eq]
  unfold parity
  rfl

lemma trans_bound (f : Nat → Bool) (k : Nat) :
    (List.range k).foldl (fun acc bit => acc ||| ((f bit).toNat <<< bit)) 0 < 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    apply Nat.or_lt_two_pow
    · exact lt_trans ih (Nat.pow_lt_pow_right (by decide) (by omega))
    · cases f k <;> simp [Nat.shiftLeft_eq, pow_succ] <;> positivity

lemma raw_fit (n w p : Nat) (hn : 0 < n) (hp : 0 < p) :
    Fits n w p (2*n*2^w) := by
  let A := Fin n → Fin (2^(w+1)) → Bool
  have hcard : Fintype.card A = 2^(2*n*2^w) := by
    have he : 2 ^ (w+1) * n = 2*n*2^w := by rw [pow_succ]; ring
    simp [A, ← pow_mul, he]
  let blank : A := fun _ _ => false
  let assign (i : Nat) (old : A) (row : Row) : A :=
    fun j k => if j.val = i then row k.val else old j k
  let target (input : Nat → Row) : A := fun j k => input j.val k.val
  have hscan (input : Nat → Row) (a : A) (j : Fin n) (k : Fin (2^(w+1))) :
      ∀ m, ((List.range m).foldl (fun state i => assign i state (input i)) a) j k =
        if j.val < m then target input j k else a j k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, assign]
      by_cases h : j.val = m
      · simp [h, target]
      · rw [if_neg h, ih]
        have : j.val < m+1 ↔ j.val < m := by omega
        simp [this]
  let answer (a : A) : Bool := parity n w (fun site loc =>
    if h : site < n then if k : loc < 2^(w+1) then a ⟨site,h⟩ ⟨loc,k⟩ else false else false)
  apply of_equiv (Fintype.equivFinOfCardEq hcard) blank (fun _ => assign) answer
  intro input
  obtain ⟨q, rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
  unfold run
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  have scan_all (a : A) : (List.range n).foldl (fun state i => assign i state (input i)) a =
      target input := by
    funext j k
    rw [hscan, if_pos j.isLt]
  rw [scan_all]
  unfold answer parity
  congr 2
  apply List.filter_congr
  intro word hw
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  apply forall_congr'
  intro site
  apply imp_congr_right
  intro hs
  have hl : site < n := List.mem_range.mp hs
  have hk : pat n w word site < 2^(w+1) := trans_bound _ _
  simp [hl, hk, target]

lemma vector_fit (n w p : Nat) (hn : 0 < n) (hw : 0 < w) (hp : 0 < p) :
    Fits n w p (1+2^w*((2^w+p-1)/p)) := by
  rw [Nat.add_comm 1]
  exact PEqualNP.Outside.L_clb_087 n w p hn hw hp

open Finset in
lemma xor_testBit (a b : Nat) : (a.testBit 0 ^^ b.testBit 0) = (a+b).testBit 0 := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h <;>
    rcases Nat.mod_two_eq_zero_or_one b with h' | h' <;>
    simp [Nat.testBit_zero, Nat.add_mod, h, h']

open Finset in
lemma batch_fit (n w p : Nat) (hn : 0 < n) (hp : 0 < p) :
    Fits n w p (1+(2^n+p-1)/p) := by
  classical
  let N := 2^n
  let B := (N+p-1)/p
  have hN : 0 < N := by dsimp [N]; positivity
  have hNB : N ≤ p * B := by
    have h1 := Nat.div_add_mod (N+p-1) p
    have h2 := Nat.mod_lt (N+p-1) hp
    dsimp [B]
    omega
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h | h
    · rw [h, Nat.mul_zero] at hNB
      omega
    · exact h
  let A := Bool × (Fin B → Bool)
  have hc : Fintype.card A = 2^(1+B) := by simp [A, pow_add]
  let cnt (q : Nat) (m : Fin B → Bool) :=
    (univ.filter fun k : Fin B => m k = true ∧ q*B+k.val < N).card
  let test (q i : Nat) (row : Row) (k : Fin B) := row (pat n w (q*B+k.val) i)
  let step (q i : Nat) (st : A) (row : Row) : A :=
    if i = 0 then (st.1 ^^ (cnt (q-1) st.2).testBit 0, test q i row)
    else (st.1, fun k => st.2 k && test q i row k)
  let answer (st : A) := st.1 ^^ (cnt (p-1) st.2).testBit 0
  apply of_equiv (Fintype.equivFinOfCardEq hc) (false, fun _ => false) step answer
  intro input
  let good (word : Nat) := (List.range n).all (fun i => input i (pat n w word i))
  let mask (q : Nat) : Fin B → Bool := fun k => good (q*B+k.val)
  let scan (q : Nat) (st : A) := (List.range n).foldl (fun s i => step q i s (input i)) st
  have rest (q : Nat) (l : List Nat) (hl : ∀ i ∈ l, i ≠ 0) (acc : Bool) (m : Fin B → Bool) :
      l.foldl (fun s i => step q i s (input i)) (acc,m) =
        (acc, fun k => m k && l.all (fun i => test q i (input i) k)) := by
    induction l generalizing m with
    | nil => simp
    | cons i l ih =>
      rw [List.foldl_cons]
      simp only [step, if_neg (hl i List.mem_cons_self)]
      rw [ih (fun j hj => hl j (List.mem_cons_of_mem i hj))]
      simp only [List.all_cons, Bool.and_assoc]
  have scan_eq (q : Nat) (acc : Bool) (m : Fin B → Bool) :
      scan q (acc,m) = (acc ^^ (cnt (q-1) m).testBit 0, mask q) := by
    obtain ⟨n', h⟩ : ∃ n', n = n'+1 := ⟨n-1, by omega⟩
    have split : List.range n = 0 :: (List.range n').map Nat.succ := by
      rw [h, List.range_succ_eq_map]
    unfold scan
    rw [split, List.foldl_cons]
    simp only [step, if_pos rfl]
    rw [rest]
    · simp only [mask, good, split, List.all_cons, test]
    · intro i hi
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      omega
  have batch_prefix (q : Nat) :
      (List.range (q+1)).foldl (fun st i => scan i st) (false, fun _ => false) =
        ((∑ i ∈ range q, cnt i (mask i)).testBit 0, mask q) := by
    induction q with
    | zero => simp [scan_eq, cnt]
    | succ q ih =>
      rw [List.range_succ, List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, scan_eq, Nat.add_sub_cancel, xor_testBit,
        Finset.sum_range_succ]
  have hcount : ((List.range N).filter good).length = ∑ q ∈ range p, cnt q (mask q) := by
    have e1 : ((List.range N).filter good).length = ((range N).filter fun j => good j = true).card := by
      rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range), List.toFinset_filter]
      congr 1
      ext j
      simp [List.mem_range]
    rw [e1, Finset.card_eq_sum_card_fiberwise (f := fun j : Nat => j/B) (t := range p)]
    · apply Finset.sum_congr rfl
      intro q hq
      symm
      apply Finset.card_bij (fun k _ => q*B+k.val)
      · intro k hk
        simp only [cnt, mask, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hk ⊢
        refine ⟨⟨hk.2, hk.1⟩, ?_⟩
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt k.isLt, Nat.zero_add]
      · intro k _ k' _ h
        exact Fin.ext (by omega)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        have h := Nat.div_add_mod j B
        rw [Nat.mul_comm, hj.2] at h
        refine ⟨⟨j%B, Nat.mod_lt _ hB⟩, ?_, h⟩
        simp only [cnt, mask, Finset.mem_filter, Finset.mem_univ, true_and, h]
        exact ⟨hj.1.2, hj.1.1⟩
    · intro j hj
      have hjm : j ∈ (range N).filter (fun j => good j = true) := hj
      have hjlt := mem_range.mp (mem_filter.mp hjm).1
      simp only [Finset.mem_coe, Finset.mem_range]
      rw [Nat.div_lt_iff_lt_mul hB]
      exact lt_of_lt_of_le hjlt (by simpa [Nat.mul_comm] using hNB)
  have hpar : parity n w input = (∑ q ∈ range p, cnt q (mask q)).testBit 0 :=
    congrArg (fun a => a.testBit 0) hcount
  unfold run
  change answer ((List.range p).foldl (fun st q => scan q st) (false, fun _ => false)) = _
  rw [hpar]
  obtain ⟨q, rfl⟩ : ∃ q, p = q+1 := ⟨p-1, by omega⟩
  rw [batch_prefix]
  simp only [answer, Nat.add_sub_cancel, xor_testBit, Finset.sum_range_succ]

open Finset

private theorem foldl_bits_spec (f : Nat → Bool) :
    ∀ (k b : Nat),
      ((List.range k).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0).testBit b =
      if b < k then f b else false := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih b, Nat.testBit_shiftLeft]
    by_cases hbk : b < k
    · have hlt : b < k + 1 := by omega
      have hge : ¬ (k ≤ b) := by omega
      simp [hbk, hlt, hge]
    · by_cases hbe : b = k
      · subst hbe
        simp only [lt_self_iff_false, ↓reduceIte, Nat.lt_add_one, le_refl,
          decide_true, Nat.sub_self, Bool.true_and, Bool.false_or]
        cases f b <;> decide
      · have hgt : ¬ (b < k + 1) := by omega
        have hpos : b - k ≠ 0 := by omega
        have hzero : (f k).toNat.testBit (b - k) = false := by
          cases f k
          · simp
          · simp only [Bool.toNat_true, Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not]
            have hdiv0 : 1 / 2 ^ (b - k) = 0 := Nat.div_eq_of_lt (Nat.one_lt_two_pow hpos)
            simp [hdiv0]
        simp [hbk, hgt, hzero]

private theorem list_filter_length_eq_finset_card (N : Nat) (p : Nat → Bool) :
    ((List.range N).filter p).length =
      ((Finset.univ : Finset (Fin N)).filter (fun x => p x.val = true)).card := by
  have h1 : ((List.range N).filter p).length = ((Finset.range N).filter (fun x => p x = true)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_range).filter p)]
    congr 1
    ext x
    simp [List.mem_range, Finset.mem_filter, Finset.mem_range]
  rw [h1]
  refine Finset.card_bij (fun x hx => ⟨x, Finset.mem_range.mp (Finset.mem_filter.mp hx).1⟩) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hx).2
  · intro x1 _ x2 _ h
    exact congrArg Fin.val h
  · intro x hx
    refine ⟨x.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr x.isLt, (Finset.mem_filter.mp hx).2⟩, rfl⟩
def ipSign (n : ℕ) (x y : Fin n → Bool) : ℤ :=
  (-1) ^ (univ.filter (fun i : Fin n => x i = true ∧ y i = true)).card

theorem ipSign_eq_prod (n : ℕ) (x y : Fin n → Bool) :
    ipSign n x y = ∏ i : Fin n, (if x i = true ∧ y i = true then (-1 : ℤ) else 1) := by
  unfold ipSign
  rw [Finset.prod_ite]
  simp

theorem ipSign_sq (n : ℕ) (x y : Fin n → Bool) : ipSign n x y * ipSign n x y = 1 := by
  unfold ipSign
  rw [← pow_add, ← two_mul, pow_mul]
  simp

theorem ipSign_orth (n : ℕ) (y y' : Fin n → Bool) :
    ∑ x : Fin n → Bool, ipSign n x y * ipSign n x y' = if y = y' then (2 : ℤ) ^ n else 0 := by
  have h1 : ∀ x : Fin n → Bool, ipSign n x y * ipSign n x y' =
      ∏ i : Fin n, ((if x i = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if x i = true ∧ y' i = true then (-1 : ℤ) else 1)) := by
    intro x
    rw [ipSign_eq_prod, ipSign_eq_prod, ← Finset.prod_mul_distrib]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset Bool))
    (fun (i : Fin n) (b : Bool) => (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1))
  rw [Fintype.piFinset_univ] at h2
  rw [← h2]
  have h3 : ∀ i : Fin n, (∑ b : Bool, (if b = true ∧ y i = true then (-1 : ℤ) else 1) *
        (if b = true ∧ y' i = true then (-1 : ℤ) else 1)) = if y i = y' i then 2 else 0 := by
    intro i
    cases y i <;> cases y' i <;> simp
  simp_rw [h3]
  rw [Finset.prod_ite_zero]
  by_cases h : y = y'
  · subst h; simp
  · have : ¬ ∀ i ∈ (univ : Finset (Fin n)), y i = y' i :=
      fun hh => h (funext fun i => hh i (mem_univ i))
    rw [if_neg this, if_neg h]

theorem lindsey_w (M : ℕ) (A B : Finset (Fin M → Bool)) (ε : (Fin M → Bool) → ℤ)
    (hε : ∀ y, ε y * ε y = 1) :
    (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * 2 ^ M := by
  have h1 : (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤
      (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 := sq_sum_le_card_mul_sum_sq
  have h2 : ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 ≤
      ∑ x : Fin M → Bool, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (subset_univ A) (fun _ _ _ => sq_nonneg _)
  have h3 : ∑ x : Fin M → Bool, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 = (B.card : ℤ) * 2 ^ M := by
    simp_rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    have : ∀ y ∈ B, ∑ x : Fin M → Bool, ∑ y' ∈ B, ipSign M x y * ε y * (ipSign M x y' * ε y') = 2 ^ M := by
      intro y hy
      rw [Finset.sum_comm]
      have e : ∀ y', ∑ x : Fin M → Bool, ipSign M x y * ε y * (ipSign M x y' * ε y') =
          ε y * ε y' * ∑ x : Fin M → Bool, ipSign M x y * ipSign M x y' := by
        intro y'
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        ring
      simp_rw [e, ipSign_orth]
      simp [hy, hε]
    rw [Finset.sum_congr rfl this]
    simp
  calc (∑ x ∈ A, ∑ y ∈ B, ipSign M x y * ε y) ^ 2
      ≤ (A.card : ℤ) * ∑ x ∈ A, (∑ y ∈ B, ipSign M x y * ε y) ^ 2 := h1
    _ ≤ (A.card : ℤ) * ((B.card : ℤ) * 2 ^ M) := by
        apply mul_le_mul_of_nonneg_left (h2.trans h3.le) (by positivity)
    _ = (A.card : ℤ) * (B.card : ℤ) * 2 ^ M := by ring

def sgn (b : Bool) : ℤ := if b then -1 else 1

theorem sgn_sq (b : Bool) : sgn b * sgn b = 1 := by cases b <;> simp [sgn]

def P {X Y : Type} {S : ℕ} (s0 : Fin S) (α : ℕ → Fin S → X → Fin S) (β : ℕ → Fin S → Y → Fin S)
    (x : X) (y : Y) : ℕ → Fin S
  | 0 => s0
  | q + 1 => β q (α q (P s0 α β x y q) x) y

def prev {S p : ℕ} (s0 : Fin S) (t : (Fin p → Fin S) × (Fin (p - 1) → Fin S)) (q : ℕ) : Fin S :=
  if h : q = 0 then s0 else if h' : q - 1 < p - 1 then t.2 ⟨q - 1, h'⟩ else s0

theorem proto {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (S p : ℕ) (hp : 0 < p) (s0 : Fin S)
    (α : ℕ → Fin S → X → Fin S) (β : ℕ → Fin S → Y → Fin S) (g : Fin S → Bool) (wt : X → Y → ℤ) (K : ℤ)
    (Lin : ∀ (A : Finset X) (B : Finset Y) (ε : Y → ℤ), (∀ y, ε y * ε y = 1) →
      (∑ x ∈ A, ∑ y ∈ B, wt x y * ε y) ^ 2 ≤ (A.card : ℤ) * (B.card : ℤ) * K) :
    (∑ x, ∑ y, wt x y * sgn (g (P s0 α β x y p))) ^ 2 ≤
      (S : ℤ) ^ (2 * p - 1) * (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) * K := by
  classical
  let T := (Fin p → Fin S) × (Fin (p - 1) → Fin S)
  let tau : X × Y → T := fun xy =>
    (fun q => α q.val (P s0 α β xy.1 xy.2 q.val) xy.1,
     fun q => P s0 α β xy.1 xy.2 (q.val + 1))
  let Ac : T → X → Prop := fun t x => ∀ q : Fin p, t.1 q = α q.val (prev s0 t q.val) x
  let Bc : T → Y → Prop := fun t y => ∀ q : Fin (p - 1), t.2 q = β q.val (t.1 ⟨q.val, by omega⟩) y
  have hiff : ∀ x y t, tau (x, y) = t ↔ (Ac t x ∧ Bc t y) := by
    intro x y t
    constructor
    · rintro rfl
      refine ⟨?_, ?_⟩
      · intro q
        simp only [tau]
        congr 1
        unfold prev
        by_cases h0 : q.val = 0
        · simp [h0, P]
        · have h1 : q.val - 1 < p - 1 := by omega
          simp only [h0, h1, dite_false, dite_true]
          congr 1
          omega
      · intro q
        simp only [tau, P]
    · rintro ⟨ha, hb⟩
      have key : ∀ q : ℕ, (hq : q < p) → t.1 ⟨q, hq⟩ = α q (P s0 α β x y q) x ∧
          (∀ hq' : q < p - 1, t.2 ⟨q, hq'⟩ = P s0 α β x y (q + 1)) := by
        intro q
        induction q with
        | zero =>
          intro hq
          have e1 : t.1 ⟨0, hq⟩ = α 0 (P s0 α β x y 0) x := by
            rw [ha ⟨0, hq⟩]; simp [prev, P]
          refine ⟨e1, ?_⟩
          intro hq'
          rw [hb ⟨0, hq'⟩, e1]
          rfl
        | succ q ih =>
          intro hq
          have ih' := (ih (by omega)).2 (by omega)
          have e1 : t.1 ⟨q + 1, hq⟩ = α (q + 1) (P s0 α β x y (q + 1)) x := by
            rw [ha ⟨q + 1, hq⟩]
            have : prev s0 t (q + 1) = t.2 ⟨q, by omega⟩ := by
              simp [prev, show q < p - 1 by omega]
            simp only [this, ih']
          refine ⟨e1, ?_⟩
          intro hq'
          rw [hb ⟨q + 1, hq'⟩, e1]
          rfl
      apply Prod.ext
      · funext q
        exact ((key q.val q.isLt).1).symm
      · funext q
        exact ((key q.val (by omega)).2 q.isLt).symm
  have hPp : ∀ x y, P s0 α β x y p = β (p - 1) (α (p - 1) (P s0 α β x y (p - 1)) x) y := by
    intro x y
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    rfl
  let A : T → Finset X := fun t => univ.filter (Ac t)
  let B : T → Finset Y := fun t => univ.filter (Bc t)
  let ε : T → Y → ℤ := fun t y => sgn (g (β (p - 1) (t.1 ⟨p - 1, by omega⟩) y))
  have hfib : ∀ t, (univ : Finset (X × Y)).filter (fun xy => tau xy = t) = A t ×ˢ B t := by
    intro t
    ext ⟨x, y⟩
    simp [A, B, hiff]
  have hsum : ∑ x, ∑ y, wt x y * sgn (g (P s0 α β x y p)) =
      ∑ t : T, ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y := by
    rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise (univ : Finset (X × Y)) tau]
    apply Finset.sum_congr rfl
    intro t _
    rw [hfib, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    have ht : tau (x, y) = t := (hiff x y t).2 ⟨(Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2⟩
    simp only [ε, hPp, ← ht, tau]
  have hcardsum : ∑ t : T, ((A t).card : ℤ) * ((B t).card : ℤ) =
      (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := tau) (s := (univ : Finset (X × Y)))
      (t := (univ : Finset T)) (by intro _ _; simp)
    simp only [hfib, Finset.card_product, Finset.card_univ, Fintype.card_prod] at this
    rw [← Nat.cast_mul, this]
    push_cast
    rfl
  have hT : (Fintype.card T : ℤ) = (S : ℤ) ^ (2 * p - 1) := by
    simp only [T, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    rw [← pow_add]
    congr 1
    omega
  rw [hsum]
  calc (∑ t : T, ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y) ^ 2
      ≤ (Fintype.card T : ℤ) * ∑ t : T, (∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset T))
          (f := fun t => ∑ x ∈ A t, ∑ y ∈ B t, wt x y * ε t y)
        simpa using this
    _ ≤ (Fintype.card T : ℤ) * ∑ t : T, ((A t).card : ℤ) * ((B t).card : ℤ) * K := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro t _
        exact Lin (A t) (B t) (ε t) (fun y => sgn_sq _)
    _ = (S : ℤ) ^ (2 * p - 1) * (Fintype.card X : ℤ) * (Fintype.card Y : ℤ) * K := by
        rw [← Finset.sum_mul, hcardsum, hT]; ring

theorem list_corr {γ : Type} (l : List γ) (q : γ → Bool) :
    (l.map (fun c => if q c then (1 : ℤ) else -1)).sum = 2 * ((l.filter q).length : ℤ) - l.length := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.filter_cons, List.length_cons]
    cases q j <;> simp <;> ring

theorem sgn_mul (b o : Bool) : sgn b * sgn o = if (o == b) = true then 1 else -1 := by
  cases b <;> cases o <;> simp [sgn]

theorem ip_sgn (M : ℕ) (x y : Fin M → Bool) :
    ipSign M x y = sgn ((univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card.testBit 0) := by
  unfold ipSign sgn
  rw [Nat.testBit_zero]
  rcases Nat.even_or_odd (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card with h | h
  · rw [h.neg_one_pow]; simp [Nat.even_iff.mp h]
  · rw [h.neg_one_pow]; simp [Nat.odd_iff.mp h]


def IP (M : Nat) (x y : Fin M → Bool) : Bool :=
  (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card.testBit 0

def Gadget (n w a M : Nat) : Prop :=
  ∃ T : (Fin M → Bool) → (Fin M → Bool) → Nat → Row,
    (∀ i, i < a → ∀ x y y', T x y i = T x y' i) ∧
    (∀ i, a ≤ i → ∀ x x' y, T x y i = T x' y i) ∧
    ∀ x y, parity n w (T x y) = IP M x y

theorem foldl_congr' {σ γ : Type} (l : List γ) (f g : σ → γ → σ) (h : ∀ i ∈ l, ∀ s, f s i = g s i) (s : σ) :
    l.foldl f s = l.foldl g s := by
  induction l generalizing s with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    rw [h j (by simp) s]
    exact ih (fun i hi => h i (by simp [hi])) _

lemma lower_gadget (n w a M p S R u v : Nat) (ha : a ≤ n) (hp : 0 < p)
    (hR : 0 < R) (huv : u ≤ v) (hG : Gadget n w a M)
    (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
    (output : Fin R → Fin S → Bool)
    (hyp : ∀ input : Nat → Row, (v+u)*R ≤ 2*v*((List.finRange R).filter (fun coin =>
      output coin (run n p (init coin) (update coin) input) == parity n w input)).length) :
    u^2 * 2^M ≤ v^2 * S^(2*p-1) := by
  classical
  obtain ⟨T, hT1, hT2, hpar⟩ := hG
  let al (c : Fin R) (q : Nat) (s : Fin S) (x : Fin M → Bool) :=
    (List.range a).foldl (fun st i => update c q i st (T x (fun _ => false) i)) s
  let be (c : Fin R) (q : Nat) (s : Fin S) (y : Fin M → Bool) :=
    (List.range (n-a)).foldl
      (fun st i => update c q (a+i) st (T (fun _ => false) y (a+i))) s
  have hrun (c : Fin R) (x y : Fin M → Bool) :
      run n p (init c) (update c) (T x y) = P (init c) (al c) (be c) x y p := by
    have hsplit (q : Nat) (s : Fin S) :
        (List.range n).foldl (fun st i => update c q i st (T x y i)) s =
          be c q (al c q s x) y := by
      have hs : List.range n = List.range a ++ (List.range (n-a)).map (a+·) := by
        have := @List.range_add a (n-a)
        rwa [show a+(n-a) = n by omega] at this
      rw [hs, List.foldl_append, List.foldl_map]
      have h1 : (List.range a).foldl (fun st i => update c q i st (T x y i)) s = al c q s x := by
        apply foldl_congr'
        intro i hi st
        rw [hT1 i (List.mem_range.mp hi) x y]
      rw [h1]
      apply foldl_congr'
      intro i _ st
      rw [hT2 (a+i) (by omega) x]
    simp only [run, hsplit]
    suffices ∀ q, (List.range q).foldl (fun st i => be c i (al c i st x) y) (init c) =
        P (init c) (al c) (be c) x y q from this p
    intro q
    induction q with
    | zero => rfl
    | succ q ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, P, ih]
  have hcardX : (Fintype.card (Fin M → Bool) : ℤ) = 2 ^ M := by simp
  let C : Fin R → ℤ := fun c => ∑ x : Fin M → Bool, ∑ y : Fin M → Bool,
    ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p))
  have hC : ∀ c, C c ^ 2 ≤ (S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M := by
    intro c
    have := proto S p hp (init c) (al c) (be c) (output c) (ipSign M) (2 ^ M)
      (fun A B ε hε => lindsey_w M A B ε hε)
    rw [hcardX] at this
    exact this
  have hcor : ∀ x y, (u : ℤ) * R ≤
      v * ∑ c : Fin R, ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p)) := by
    intro x y
    have h := hyp (T x y)
    simp only [hrun, hpar] at h
    rw [ip_sgn]
    simp_rw [sgn_mul]
    rw [Fin.sum_univ_def, list_corr, List.length_finRange]
    have h' : (((v + u) * R : ℕ) : ℤ) ≤ ((2 * v * (List.filter (fun c => output c
        (P (init c) (al c) (be c) x y p) == (univ.filter (fun i : Fin M => x i = true ∧ y i = true)).card.testBit 0)
        (List.finRange R)).length : ℕ) : ℤ) := by exact_mod_cast h
    push_cast at h'
    linarith
  have hsumC : (u : ℤ) * R * (2 ^ M * 2 ^ M) ≤ v * ∑ c, C c := by
    have e : ∑ c, C c = ∑ x : Fin M → Bool, ∑ y : Fin M → Bool, ∑ c : Fin R,
        ipSign M x y * sgn (output c (P (init c) (al c) (be c) x y p)) := by
      simp only [C]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    rw [e, Finset.mul_sum]
    calc (u : ℤ) * R * (2 ^ M * 2 ^ M) = ∑ x : Fin M → Bool, ∑ y : Fin M → Bool, (u : ℤ) * R := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← hcardX]; push_cast; ring
      _ ≤ _ := by
          apply Finset.sum_le_sum
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro y _
          exact hcor x y
  have hCS : (∑ c, C c) ^ 2 ≤ (R : ℤ) * ∑ c, C c ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin R))) (f := C)
    simpa using this
  have hCS2 : ∑ c, C c ^ 2 ≤ (R : ℤ) * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M) := by
    calc ∑ c, C c ^ 2 ≤ ∑ _c : Fin R, ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M) :=
          Finset.sum_le_sum (fun c _ => hC c)
      _ = _ := by simp
  have hpos : 0 ≤ (u : ℤ) * R * (2 ^ M * 2 ^ M) := by positivity
  have big : ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 ≤
      (v : ℤ) ^ 2 * (R * (R * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M))) := by
    calc ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 ≤ (v * ∑ c, C c) ^ 2 := pow_le_pow_left₀ hpos hsumC 2
      _ = (v : ℤ) ^ 2 * (∑ c, C c) ^ 2 := by ring
      _ ≤ (v : ℤ) ^ 2 * (R * ∑ c, C c ^ 2) := mul_le_mul_of_nonneg_left hCS (by positivity)
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_left hCS2 (by positivity)
  have hZ : (0 : ℤ) < (R : ℤ) ^ 2 * (2 ^ M) ^ 3 := by
    have : (0 : ℤ) < R := by exact_mod_cast hR
    positivity
  have fin : ((u : ℤ) ^ 2 * 2 ^ M) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) ≤
      ((v : ℤ) ^ 2 * (S : ℤ) ^ (2 * p - 1)) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) := by
    have e1 : ((u : ℤ) ^ 2 * 2 ^ M) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) = ((u : ℤ) * R * (2 ^ M * 2 ^ M)) ^ 2 := by ring
    have e2 : ((v : ℤ) ^ 2 * (S : ℤ) ^ (2 * p - 1)) * ((R : ℤ) ^ 2 * (2 ^ M) ^ 3) =
        (v : ℤ) ^ 2 * (R * (R * ((S : ℤ) ^ (2 * p - 1) * 2 ^ M * 2 ^ M * 2 ^ M))) := by ring
    rw [e1, e2]; exact big
  have := le_of_mul_le_mul_right fin hZ
  exact_mod_cast this

def sols (n L : Nat) (hn : 0 < n) (tab : Fin n × (Fin L → Bool) → Bool) : Finset (Fin n → Bool) :=
  (Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
    ∀ i : Fin n, tab (i, fun j => x ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true)

def Emb (n L : Nat) (hn : 0 < n) (a M : Nat) : Prop :=
  ∃ (code : Fin M → (Fin n → Bool)) (base : Fin n × (Fin L → Bool) → Bool)
    (left right : Fin M → Fin n × (Fin L → Bool)),
    Function.Injective code ∧ (∀ i, (left i).1.val < a ∧ a ≤ (right i).1.val) ∧
    ∀ A B : Finset (Fin M), sols n L hn (fun slot => base slot || decide (slot ∈ A.image left) ||
      decide (slot ∈ B.image right)) = (A ∩ B).image code

theorem Emb_cast {n n' L a M : Nat} (e : n' = n) (hn : 0 < n) (hn' : 0 < n') :
    Emb n' L hn' a M → Emb n L hn a M := by
  subst e; exact id

theorem direct_gen (n L : Nat) (hn : 0 < n) (h2 : 2 ≤ n) (off m : Nat) (hom : off + m ≤ n)
    (c01 : ∀ i k, i < 2 → off ≤ k → k < off + m → ∃ j, j < L ∧ (i + j) % n = k)
    (cZ : ∀ k, k < n → ¬(off ≤ k ∧ k < off + m) →
      ∃ i j, 2 ≤ i ∧ i < n ∧ j < L ∧ (i + j) % n = k) :
    Emb n L hn 1 (2^m) := by
  let code : Fin (2^m) → Fin n → Bool := fun i k =>
    decide (off ≤ k.val ∧ k.val < off + m) && Nat.testBit i.val (k.val - off)
  let win : Nat → (Fin n → Bool) → Fin L → Bool := fun i x j => x ⟨(i + j.val) % n, Nat.mod_lt _ hn⟩
  let base : Fin n × (Fin L → Bool) → Bool := fun slot => decide (2 ≤ slot.1.val ∧
    ∀ j : Fin L, ¬(off ≤ (slot.1.val + j.val) % n ∧ (slot.1.val + j.val) % n < off + m) →
      slot.2 j = false)
  let left : Fin (2^m) → Fin n × (Fin L → Bool) := fun k => (⟨0, hn⟩, win 0 (code k))
  let right : Fin (2^m) → Fin n × (Fin L → Bool) := fun k => (⟨1, by omega⟩, win 1 (code k))
  have hcv : ∀ i (k : Fin n), ¬(off ≤ k.val ∧ k.val < off + m) → code i k = false := by
    intro i k hk
    simp [code, hk]
  have det : ∀ i, i < 2 → ∀ x y : Fin n → Bool,
      (∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → x k = false) →
      (∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → y k = false) →
      win i x = win i y → x = y := by
    intro i hi x y hx hy hw
    funext k
    by_cases hk : off ≤ k.val ∧ k.val < off + m
    · obtain ⟨j, hj, hjk⟩ := c01 i k.val hi hk.1 hk.2
      have := congrFun hw ⟨j, hj⟩
      simp only [win] at this
      have e : (⟨(i + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hjk
      rw [e] at this
      exact this
    · rw [hx k hk, hy k hk]
  have hinj : Function.Injective code := by
    intro i i' h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro b
    by_cases hb : b < m
    · have := congrFun h ⟨off + b, by omega⟩
      simpa [code, hb] using this
    · have hm : 2^m ≤ 2^b := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le i.isLt hm),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le i'.isLt hm)]
  refine ⟨code, base, left, right, hinj, fun i => ⟨Nat.zero_lt_one, le_refl 1⟩, ?_⟩
  intro A B
  have hnl : ∀ (i : Fin n) (pat : Fin L → Bool) (A' : Finset (Fin (2^m))), i.val ≠ 0 →
      decide ((i,pat) ∈ A'.image left) = false := by
    intro i pat A' hi
    simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
    intro k _ hk
    have := congrArg (fun s => s.1.val) hk
    simp [left] at this
    omega
  have hnr : ∀ (i : Fin n) (pat : Fin L → Bool) (B' : Finset (Fin (2^m))), i.val ≠ 1 →
      decide ((i,pat) ∈ B'.image right) = false := by
    intro i pat B' hi
    simp only [decide_eq_false_iff_not, Finset.mem_image, not_exists, not_and]
    intro k _ hk
    have := congrArg (fun s => s.1.val) hk
    simp [right] at this
    omega
  have hnb : ∀ (i : Fin n) (pat : Fin L → Bool), i.val < 2 → base (i,pat) = false := by
    intro i pat hi
    simp only [base, decide_eq_false_iff_not, not_and]
    intro h
    omega
  ext x
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.mem_image]
  simp only [Finset.mem_inter]
  constructor
  · intro hx
    have hvan : ∀ k : Fin n, ¬(off ≤ k.val ∧ k.val < off + m) → x k = false := by
      intro k hk
      obtain ⟨i, j, hi2, hin, hj, hijk⟩ := cZ k.val k.isLt hk
      have hxi := hx ⟨i, hin⟩
      rw [hnl _ _ _ (by simp; omega), hnr _ _ _ (by simp; omega)] at hxi
      simp only [Bool.or_false, base, decide_eq_true_eq] at hxi
      have := hxi.2 ⟨j, hj⟩ (by simp only; rw [hijk]; exact hk)
      have e : (⟨(i + j) % n, Nat.mod_lt _ hn⟩ : Fin n) = k := Fin.ext hijk
      simp only at this
      rw [e] at this
      exact this
    have h0 := hx ⟨0, hn⟩
    rw [hnb _ _ (by simp), hnr _ _ _ (by simp)] at h0
    simp only [Bool.false_or, Bool.or_false, decide_eq_true_eq, Finset.mem_image] at h0
    obtain ⟨k, hkA, hk⟩ := h0
    have h1 := hx ⟨1, by omega⟩
    rw [hnb _ _ (by simp), hnl _ _ _ (by simp)] at h1
    simp only [Bool.false_or, Bool.or_false, decide_eq_true_eq, Finset.mem_image] at h1
    obtain ⟨k', hkB, hk'⟩ := h1
    have ek : code k = x := det 0 (by norm_num) _ _ (hcv k) hvan (congrArg Prod.snd hk)
    have ek' : code k' = x := det 1 (by norm_num) _ _ (hcv k') hvan (congrArg Prod.snd hk')
    have : k = k' := hinj (ek.trans ek'.symm)
    subst this
    exact ⟨k, ⟨hkA, hkB⟩, ek⟩
  · rintro ⟨k, ⟨hkA, hkB⟩, rfl⟩ i
    by_cases i0 : i.val = 0
    · have : (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = left k := by
        have ei : i = ⟨0, hn⟩ := Fin.ext i0
        subst ei
        rfl
      rw [this]
      simp [Finset.mem_image_of_mem left hkA]
    by_cases i1 : i.val = 1
    · have : (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = right k := by
        obtain ⟨iv, hiv⟩ := i
        simp only at i1
        subst i1
        rfl
      rw [this]
      simp [Finset.mem_image_of_mem right hkB]
    · have hb : base (i, fun j : Fin L => code k ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩) = true := by
        simp only [base, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        intro j hj
        exact hcv k _ hj
      rw [hb]
      rfl



def wordNat (k : Nat) (word : Fin k → Bool) : Nat :=
  (List.range k).foldl (fun acc bit => acc |||
    ((if h : bit < k then word ⟨bit,h⟩ else false).toNat <<< bit)) 0

lemma wordNat_bits (k : Nat) (word : Fin k → Bool) (i : Fin k) :
    (wordNat k word).testBit i.val = word i := by
  rw [wordNat, foldl_bits_spec]
  simp [i.isLt]

set_option maxHeartbeats 1500000 in
def readWord (n : Nat) : Fin (2^n) ≃ (Fin n → Bool) where
  toFun x i := x.val.testBit i.val
  invFun x := ⟨wordNat n x, trans_bound _ _⟩
  left_inv x := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    let bits : Fin n → Bool := fun j => x.val.testBit j.val
    change (wordNat n bits).testBit i = x.val.testBit i
    by_cases hi : i < n
    · exact wordNat_bits n bits ⟨i, hi⟩
    · have hh : 2^n ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      have hb : wordNat n bits < 2^n := trans_bound _ _
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hh),
          Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt hh)]
  right_inv x := funext (wordNat_bits n x)

def putRows {n k : Nat} (tab : Fin n × (Fin k → Bool) → Bool) : Nat → Row :=
  fun i r => if h : i < n then tab (⟨i,h⟩, fun j => r.testBit j.val) else false

lemma parity_push {n w : Nat} (hn : 0 < n) (tab : Fin n × (Fin (w+1) → Bool) → Bool) :
    parity n w (putRows tab) = (sols n (w+1) hn tab).card.testBit 0 := by
  unfold parity
  rw [list_filter_length_eq_finset_card]
  congr 1
  apply Finset.card_equiv (readWord n)
  intro x
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and, List.all_eq_true, List.mem_range]
  have h (i : Fin n) : putRows tab i.val (pat n w x.val i.val) =
      tab (i, fun j : Fin (w+1) => readWord n x ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) := by
    simp only [putRows, dif_pos i.isLt, Fin.eta]
    congr 1
    refine Prod.ext ?_ ?_
    · rfl
    · funext j
      change (pat n w x.val i.val).testBit j.val = x.val.testBit ((i.val+j.val)%n)
      unfold pat
      exact (foldl_bits_spec (fun bit => x.val.testBit ((i.val+bit)%n)) (w+1) j.val).trans
        (if_pos j.isLt)
  constructor
  · intro hall i
    rw [← h i]
    exact hall i.val i.isLt
  · intro hall i hi
    exact (h ⟨i,hi⟩).trans (hall ⟨i,hi⟩)

lemma from_emb {n w a M : Nat} (hn : 0 < n) (he : Emb n (w+1) hn a M) : Gadget n w a M := by
  classical
  obtain ⟨code, base, left, right, hinj, hp, hsol⟩ := he
  let aset (x : Fin M → Bool) : Finset (Fin M) := univ.filter fun i => x i = true
  let tab (x y : Fin M → Bool) : Fin n × (Fin (w+1) → Bool) → Bool :=
    fun s => base s || decide (s ∈ (aset x).image left) || decide (s ∈ (aset y).image right)
  refine ⟨fun x y => putRows (tab x y), ?_, ?_, ?_⟩
  · intro i hi x y y'
    funext r
    by_cases hin : i < n
    · have forb (b : Fin M → Bool) :
          (⟨i,hin⟩, fun j : Fin (w+1) => r.testBit j.val) ∉ (aset b).image right := by
        intro h
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
        have hs := congrArg (fun s => s.1.val) hk
        change (right k).1.val = i at hs
        have hb := (hp k).2
        omega
      simp only [putRows, dif_pos hin, tab, decide_eq_false (forb _)]
    · simp [putRows, hin]
  · intro i hi x x' y
    funext r
    by_cases hin : i < n
    · have forb (b : Fin M → Bool) :
          (⟨i,hin⟩, fun j : Fin (w+1) => r.testBit j.val) ∉ (aset b).image left := by
        intro h
        obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
        have hs := congrArg (fun s => s.1.val) hk
        change (left k).1.val = i at hs
        have hb := (hp k).1
        omega
      simp only [putRows, dif_pos hin, tab, decide_eq_false (forb _)]
    · simp [putRows, hin]
  · intro x y
    rw [parity_push hn, show sols n (w+1) hn (tab x y) = ((aset x) ∩ (aset y)).image code from
      hsol (aset x) (aset y), Finset.card_image_of_injective _ hinj]
    unfold IP
    have he : aset x ∩ aset y = univ.filter (fun i => x i = true ∧ y i = true) := by
      ext k
      simp [aset]
    rw [he]

lemma direct_gadget (n w : Nat) (hn : 0 < n) (h2 : 2 ≤ n) (hw : 0 < w) :
    Gadget n w 1 (if n ≤ w+1 then 2^n else 2^w) := by
  apply from_emb hn
  by_cases hc : n ≤ w+1
  · rw [if_pos hc]
    refine direct_gen n (w+1) hn h2 0 n (by omega) ?_ ?_
    · intro i k hi _ hk
      interval_cases i
      · exact ⟨k, by omega, by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]⟩
      · rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · subst hk0
          exact ⟨n-1, by omega, by rw [show 1 + (n-1) = n by omega, Nat.mod_self]⟩
        · exact ⟨k-1, by omega, by rw [show 1 + (k-1) = k by omega, Nat.mod_eq_of_lt (by omega)]⟩
    · intro k hk hnot
      exact absurd ⟨Nat.zero_le _, by omega⟩ hnot
  · rw [if_neg hc]
    refine direct_gen n (w+1) hn h2 1 w (by omega) ?_ ?_
    · intro i k hi hk1 hk
      interval_cases i
      · exact ⟨k, by omega, by rw [Nat.zero_add, Nat.mod_eq_of_lt (by omega)]⟩
      · exact ⟨k-1, by omega, by rw [show 1 + (k-1) = k by omega, Nat.mod_eq_of_lt (by omega)]⟩
    · intro k hk hnot
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        exact ⟨n-1, 1, by omega, by omega, by omega, by
          rw [show n - 1 + 1 = n by omega, Nat.mod_self]⟩
      · exact ⟨k, 0, by omega, hk, by omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hk]⟩

def FTable (n w : Nat) := Fin n × (Fin (w+1) → Bool) → Bool

def FiniteGadget (n w a M : Nat) (hn : 0 < n) : Prop :=
  ∃ T : (Fin M → Bool) → (Fin M → Bool) → FTable n w,
    (∀ s, s.1.val < a → ∀ x y y', T x y s = T x y' s) ∧
    (∀ s, a ≤ s.1.val → ∀ x x' y, T x y s = T x' y s) ∧
    ∀ x y, (sols n (w+1) hn (T x y)).card.testBit 0 = IP M x y

lemma finite_to_gadget {n w a M : Nat} {hn : 0 < n}
    (hg : FiniteGadget n w a M hn) : Gadget n w a M := by
  obtain ⟨T, h1, h2, hc⟩ := hg
  refine ⟨fun x y => putRows (T x y), ?_, ?_, ?_⟩
  · intro i hi x y y'
    funext row
    by_cases h : i < n
    · simp only [putRows, dif_pos h]
      exact h1 _ hi _ _ _
    · simp [putRows, h]
  · intro i hi x x' y
    funext row
    by_cases h : i < n
    · simp only [putRows, dif_pos h]
      exact h2 _ hi _ _ _
    · simp [putRows, h]
  · intro x y
    exact (parity_push hn _).trans (hc x y)

def downWord {n e : Nat} (word : Fin (n+e) → Bool) : Fin n → Bool :=
  fun i => word ⟨i.val, by omega⟩

def upWord {n e : Nat} (word : Fin n → Bool) : Fin (n+e) → Bool :=
  fun i => if h : i.val < n then word ⟨i.val,h⟩ else false

def liftTable {n e k w : Nat} (hkw : k+e ≤ w) (T : FTable n k) : FTable (n+e) w :=
  fun s => if hi : s.1.val < n then
    T (⟨s.1.val,hi⟩, fun j =>
      s.2 ⟨if n ≤ s.1.val+j.val then j.val+e else j.val, by
        have := j.isLt
        split <;> omega⟩)
  else !(s.2 0)

lemma liftTable_window {n e k w : Nat} (hn : 0 < n) (hk : k ≤ n) (hkw : k+e ≤ w)
    {word : Fin (n+e) → Bool} (T : FTable n k) (i : Fin (n+e)) (hi : i.val < n) :
    liftTable hkw T (i, fun j : Fin (w+1) =>
        word ⟨(i.val+j.val)%(n+e), Nat.mod_lt _ (by omega)⟩) =
      T (⟨i.val,hi⟩, fun j : Fin (k+1) =>
        downWord (e := e) word ⟨(i.val+j.val)%n, Nat.mod_lt _ hn⟩) := by
  simp only [liftTable, dif_pos hi]
  congr 1
  refine Prod.ext (by rfl) ?_
  funext j
  simp only [downWord]
  congr 1
  apply Fin.ext
  change (i.val + (if n ≤ i.val+j.val then j.val+e else j.val))%(n+e) = (i.val + j.val)%n
  have hj := j.isLt
  by_cases h : n ≤ i.val+j.val
  · rw [if_pos h, Nat.mod_eq_sub_mod (show n+e ≤ i.val+(j.val+e) by omega),
      Nat.mod_eq_sub_mod h]
    have e1 : i.val+(j.val+e)-(n+e) = i.val+j.val-n := by omega
    rw [e1, Nat.mod_eq_of_lt (by omega : i.val+j.val-n < n+e),
      Nat.mod_eq_of_lt (by omega : i.val+j.val-n < n)]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega : i.val+j.val < n+e), Nat.mod_eq_of_lt (by omega)]

lemma liftTable_count {n e k w : Nat} (hn : 0 < n) (hk : k ≤ n) (hkw : k+e ≤ w)
    (T : FTable n k) :
    (sols (n+e) (w+1) (by omega) (liftTable hkw T)).card = (sols n (k+1) hn T).card := by
  classical
  apply Finset.card_bij (fun word _ => downWord (e := e) word)
  · intro word hw
    simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    intro i
    have h := hw ⟨i.val, by omega⟩
    rw [liftTable_window hn hk hkw T _ i.isLt] at h
    exact h
  · intro word hword word' hword' he
    funext i
    by_cases h : i.val < n
    · exact congrFun he ⟨i.val,h⟩
    · have z (x : Fin (n+e) → Bool) (hx : x ∈ sols (n+e) (w+1) (by omega) (liftTable hkw T)) :
          x i = false := by
        have ht := (Finset.mem_filter.mp hx).2 i
        simp only [liftTable, dif_neg h, Fin.val_zero, Nat.add_zero, Nat.mod_eq_of_lt i.isLt] at ht
        simpa using ht
      rw [z word hword, z word' hword']
  · intro word hw
    refine ⟨upWord (e := e) word, ?_, ?_⟩
    · simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      intro i
      by_cases h : i.val < n
      · rw [liftTable_window hn hk hkw T i h]
        have he : downWord (e := e) (upWord (e := e) word) = word := by
          funext j
          simp [downWord, upWord, j.isLt]
        rw [he]
        exact hw ⟨i.val,h⟩
      · simp [liftTable, h, upWord, Nat.mod_eq_of_lt i.isLt]
    · funext j
      simp [downWord, upWord, j.isLt]

lemma padded_gadget {n e k w a M : Nat} {hn : 0 < n} (ha : a ≤ n)
    (hk : k ≤ n) (hkw : k+e ≤ w) (hg : FiniteGadget n k a M hn) :
    FiniteGadget (n+e) w a M (by omega) := by
  obtain ⟨T, h1, h2, hc⟩ := hg
  refine ⟨fun x y => liftTable hkw (T x y), ?_, ?_, ?_⟩
  · intro i hi x y y'
    have h : i.1.val < n := by omega
    simp only [liftTable, dif_pos h]
    exact h1 _ hi _ _ _
  · intro i hi x x' y
    by_cases h : i.1.val < n
    · simp only [liftTable, dif_pos h]
      exact h2 _ hi _ _ _
    · simp [liftTable, h]
  · intro x y
    rw [liftTable_count hn hk hkw]
    exact hc x y

abbrev BlockTab (L k : Nat) := Fin L × (Fin (k+1) → Bool) → Bool

def pieceA {L k : Nat} (hk : k ≤ L) (x : Fin (L+L) → Bool) : Fin (L+k) → Bool :=
  fun i => x ⟨i.val, by omega⟩

def pieceB {L k : Nat} (hL : 0 < L) (x : Fin (L+L) → Bool) : Fin (L+k) → Bool :=
  fun i => x ⟨(L+i.val)%(L+L), Nat.mod_lt _ (by omega)⟩

def startOf {L k : Nat} (s : Fin (L+k) → Bool) : Fin k → Bool :=
  fun i => s ⟨i.val, by omega⟩

def endOf {L k : Nat} (s : Fin (L+k) → Bool) : Fin k → Bool :=
  fun i => s ⟨L+i.val, by omega⟩

def wordTests {L k : Nat} (T : BlockTab L k) (s : Fin (L+k) → Bool) : Prop :=
  ∀ i : Fin L, T (i,fun j : Fin (k+1) => s ⟨i.val+j.val, by omega⟩) = true

noncomputable def blockWords {L k : Nat} (T : BlockTab L k) (a b : Fin k → Bool) :
    Finset (Fin (L+k) → Bool) := by
  classical
  exact univ.filter fun s => (startOf s = a ∧ endOf s = b) ∧ wordTests T s

def glueTable {L k : Nat} (A B : BlockTab L k) : FTable (L+L) k :=
  fun s => if h : s.1.val < L then A (⟨s.1.val,h⟩,s.2) else B (⟨s.1.val-L, by omega⟩,s.2)

lemma blocks_ok {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (A B : BlockTab L k)
    (x : Fin (L+L) → Bool) :
    x ∈ sols (L+L) (k+1) (by omega) (glueTable A B) ↔
      wordTests A (pieceA hk x) ∧ wordTests B (pieceB (k := k) hL x) := by
  classical
  simp only [sols, Finset.mem_filter, Finset.mem_univ, true_and, wordTests]
  have hA (i : Fin L) : glueTable A B (⟨i.val,by omega⟩, fun j : Fin (k+1) =>
      x ⟨(i.val+j.val)%(L+L), Nat.mod_lt _ (by omega)⟩) =
      A (i, fun j : Fin (k+1) => pieceA hk x ⟨i.val+j.val,by omega⟩) := by
    simp only [glueTable, dif_pos i.isLt, Fin.eta]
    congr 1
    refine Prod.ext (by rfl) ?_
    funext j
    simp only [pieceA]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt (by omega : i.val+j.val<L+L))
  have hB (i : Fin L) : glueTable A B (⟨L+i.val,by omega⟩, fun j : Fin (k+1) =>
      x ⟨(L+i.val+j.val)%(L+L), Nat.mod_lt _ (by omega)⟩) =
      B (i, fun j : Fin (k+1) => pieceB (k := k) hL x ⟨i.val+j.val,by omega⟩) := by
    have hni : ¬ L+i.val < L := by omega
    simp [glueTable, hni, pieceB, Nat.add_assoc]
  constructor
  · intro hx
    refine ⟨fun i => ?_,fun i => ?_⟩
    · rw [← hA i]
      exact hx ⟨i.val,by omega⟩
    · rw [← hB i]
      exact hx ⟨L+i.val,by omega⟩
  · rintro ⟨ha,hb⟩ i
    by_cases hi : i.val < L
    · have he := hA ⟨i.val,hi⟩
      simpa only [Fin.eta, he] using ha ⟨i.val,hi⟩
    · let j : Fin L := ⟨i.val-L,by omega⟩
      have hj : L+j.val = i.val := by dsimp [j]; omega
      have e : (⟨L+j.val,by omega⟩ : Fin (L+L)) = i := Fin.ext hj
      have he := (hB j).trans (hb j)
      change glueTable A B (⟨L+j.val,by omega⟩, fun o : Fin (k+1) =>
        x ⟨(L+j.val+o.val)%(L+L), Nat.mod_lt _ (by omega)⟩) = true at he
      simp only [hj, e] at he
      exact he

def halves {L k : Nat} (a b : Fin (L+k) → Bool) : Fin (L+L) → Bool :=
  fun i => if h : i.val < L then a ⟨i.val,by omega⟩ else b ⟨i.val-L,by omega⟩

lemma end_pieceA {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (x : Fin (L+L) → Bool) :
    endOf (pieceA hk x) = startOf (pieceB (k := k) hL x) := by
  funext i
  simp [endOf, startOf, pieceA, pieceB, Nat.mod_eq_of_lt (by omega : L+i.val<L+L)]

lemma end_pieceB {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (x : Fin (L+L) → Bool) :
    endOf (pieceB (k := k) hL x) = startOf (pieceA hk x) := by
  funext i
  simp only [endOf, startOf, pieceA, pieceB]
  congr 1
  apply Fin.ext
  change (L+(L+i.val))%(L+L) = i.val
  rw [← Nat.add_assoc, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

lemma halves_pieces {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (x : Fin (L+L) → Bool) :
    halves (pieceA hk x) (pieceB (k := k) hL x) = x := by
  funext i
  by_cases h : i.val < L
  · simp [halves, pieceA, h]
  · have e : L+(i.val-L) = i.val := by omega
    simp [halves, pieceB, h, e, Nat.mod_eq_of_lt i.isLt]

lemma pieces_halves {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (a b : Fin (L+k) → Bool)
    (hab : endOf a = startOf b) (hba : endOf b = startOf a) :
    pieceA hk (halves a b) = a ∧ pieceB (k := k) hL (halves a b) = b := by
  constructor
  · funext i
    by_cases h : i.val < L
    · simp [pieceA, halves, h]
    · have e := congrFun hab ⟨i.val-L, by omega⟩
      simp only [endOf, startOf] at e
      simp only [pieceA, halves, dif_neg h]
      have hb : L+(i.val-L) < L+k := by omega
      have ei : (⟨L+(i.val-L),hb⟩ : Fin (L+k)) = i :=
        Fin.ext (show L+(i.val-L) = i.val by omega)
      rw [ei] at e
      exact e.symm
  · funext i
    by_cases h : i.val < L
    · have he : (L+i.val)%(L+L) = L+i.val := Nat.mod_eq_of_lt (by omega)
      simp [pieceB, halves, he, show ¬ L+i.val<L by omega]
    · let j : Fin k := ⟨i.val-L,by omega⟩
      have e := congrFun hba j
      have he : (L+i.val)%(L+L) = j.val := by
        have h0 : L+i.val = (L+L)+j.val := by dsimp [j]; omega
        rw [h0, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hj : j.val < L := by omega
      have ei : (⟨L+j.val,by omega⟩ : Fin (L+k)) = i := Fin.ext (by dsimp [j]; omega)
      simp only [endOf, startOf, ei] at e
      simpa only [pieceB, halves, he, dif_pos hj] using e.symm

lemma count_glue {L k : Nat} (hL : 0 < L) (hk : k ≤ L) (A B : BlockTab L k) :
    (sols (L+L) (k+1) (by omega) (glueTable A B)).card =
      ∑ ab : (Fin k → Bool) × (Fin k → Bool),
        (blockWords A ab.1 ab.2).card * (blockWords B ab.2 ab.1).card := by
  classical
  let ends (x : Fin (L+L) → Bool) : (Fin k → Bool) × (Fin k → Bool) :=
    (startOf (pieceA hk x), endOf (pieceA hk x))
  rw [Finset.card_eq_sum_card_fiberwise (f := ends) (t := univ) (by intro _ _; exact mem_univ _)]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ _
  rw [← Finset.card_product]
  apply Finset.card_bij (fun x _ => (pieceA hk x,pieceB (k := k) hL x))
  · intro x hx
    have hh := (mem_filter.mp hx).2
    change (startOf (pieceA hk x),endOf (pieceA hk x)) = (a,b) at hh
    have hxy := (blocks_ok hL hk A B x).mp (mem_filter.mp hx).1
    have ha := congrArg Prod.fst hh
    have hb := congrArg Prod.snd hh
    simp only [Finset.mem_product, blockWords, mem_filter, mem_univ, true_and]
    exact ⟨⟨⟨ha,hb⟩,hxy.1⟩,⟨⟨(end_pieceA hL hk x).symm.trans hb,
      (end_pieceB hL hk x).trans ha⟩,hxy.2⟩⟩
  · intro x _ y _ he
    have ha : pieceA hk x = pieceA hk y := congrArg Prod.fst he
    have hb : pieceB (k := k) hL x = pieceB (k := k) hL y := congrArg Prod.snd he
    rw [← halves_pieces hL hk x, ← halves_pieces hL hk y, ha, hb]
  · rintro ⟨x,y⟩ h
    simp only [Finset.mem_product, blockWords, mem_filter, mem_univ, true_and] at h
    have hxy := pieces_halves hL hk x y (h.1.1.2.trans h.2.1.1.symm)
      (h.2.1.2.trans h.1.1.1.symm)
    refine ⟨halves x y, mem_filter.mpr ⟨?_,?_⟩, Prod.ext hxy.1 hxy.2⟩
    · apply (blocks_ok hL hk A B _).mpr
      rw [hxy.1,hxy.2]
      exact ⟨h.1.2,h.2.2⟩
    · simp only [ends, hxy.1, h.1.1.1, h.1.1.2]

lemma blockWords_eq {L k : Nat} [NeZero (L+k)] (hL : 0 < L) (hk : k ≤ L) (T : BlockTab L k)
    (a b : Fin k → Bool) :
    blockWords T a b = univ.filter (fun s : Fin (L+k) → Bool =>
      (∀ pos : Fin k, s (Fin.ofNat (L+k) pos.val) = a pos ∧
        s (Fin.ofNat (L+k) (L+pos.val)) = b pos) ∧
      ∀ i : Fin L, T (i,fun off : Fin (k+1) =>
        s (Fin.ofNat (L+k) (i.val+off.val))) = true) := by
  classical
  ext s
  simp only [blockWords, mem_filter, mem_univ, true_and]
  have hstart (j : Fin k) : s (Fin.ofNat (L+k) j.val) = startOf s j := by
    apply congrArg s
    exact Fin.ext (Nat.mod_eq_of_lt (by omega))
  have hend (j : Fin k) : s (Fin.ofNat (L+k) (L+j.val)) = endOf s j := by
    apply congrArg s
    exact Fin.ext (Nat.mod_eq_of_lt (by omega))
  have e1 : (startOf s = a ∧ endOf s = b) ↔
      ∀ j : Fin k, s (Fin.ofNat (L+k) j.val) = a j ∧
        s (Fin.ofNat (L+k) (L+j.val)) = b j := by
    simp_rw [hstart, hend]
    exact ⟨fun h j => ⟨congrFun h.1 j, congrFun h.2 j⟩,
      fun h => ⟨funext fun j => (h j).1, funext fun j => (h j).2⟩⟩
  rw [e1]
  refine and_congr Iff.rfl ?_
  unfold wordTests
  apply forall_congr'
  intro i
  have e : (fun j : Fin (k+1) => s ⟨i.val+j.val,by omega⟩) =
      (fun j : Fin (k+1) => s (Fin.ofNat (L+k) (i.val+j.val))) := by
    funext j
    have h : i.val+j.val < L+k := by omega
    exact congrArg s (Fin.ext (Nat.mod_eq_of_lt h).symm)
  rw [e]

lemma even_gadget (L k : Nat) (hL : 0 < L) (hk : 0 < k) (hle : k ≤ L) :
    ∃ M, 2^k*min L (2^k) ≤ 20*M ∧ FiniteGadget (L+L) k L M (by omega) := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, k = d+1 := ⟨k-1, by omega⟩
  obtain ⟨M, edge, base, port, hM, hinj, hsep, hblock⟩ := PEqualNP.Outside.L_lib_540 d L hle
  let E (x : Fin M → Bool) : Finset (Fin M) := univ.filter (fun i => x i = true)
  let T (rev : Bool) (x : Fin M → Bool) : BlockTab L (d+1) :=
    fun s => base s || decide (s ∈ (E x).image (port rev))
  have hcounts (rev : Bool) (z : Fin M → Bool) (a b : Fin (d+1) → Bool) :
      (blockWords (T rev z) a b).card =
        (if a = b then 1 else 0) +
        (if ∃ i ∈ E z, edge i = (if rev then (b,a) else (a,b)) then 1 else 0) := by
    rw [blockWords_eq hL hle]
    have he : (univ.filter (fun s : Fin (L+(d+1)) → Bool =>
        (∀ pos : Fin (d+1), s (Fin.ofNat (L+(d+1)) pos.val) = a pos ∧
          s (Fin.ofNat (L+(d+1)) (L+pos.val)) = b pos) ∧
        ∀ i : Fin L, let t : Fin L × (Fin (d+2) → Bool) :=
          (i,fun off => s (Fin.ofNat (L+(d+1)) (i.val+off.val)))
        base t = true ∨ t ∈ (E z).image (port rev))) =
      (univ.filter (fun s : Fin (L+(d+1)) → Bool =>
        (∀ pos : Fin (d+1), s (Fin.ofNat (L+(d+1)) pos.val) = a pos ∧
          s (Fin.ofNat (L+(d+1)) (L+pos.val)) = b pos) ∧
        ∀ i : Fin L, T rev z (i,fun off => s (Fin.ofNat (L+(d+1)) (i.val+off.val))) = true)) := by
      ext s
      simp only [T, mem_filter, mem_univ, true_and, Bool.or_eq_true, decide_eq_true_eq]
    rw [← he]
    exact (hblock rev).2.2 (E z) a b
  refine ⟨M,hM,fun x y => glueTable (T false x) (T true y),?_,?_,?_⟩
  · intro s hs x y y'
    simp [glueTable, hs]
  · intro s hs x x' y
    simp [glueTable, show ¬ s.1.val < L by omega]
  · intro x y
    rw [count_glue hL hle]
    let joint := E x ∩ E y
    have hprod (z : (Fin (d+1) → Bool) × (Fin (d+1) → Bool)) :
        (blockWords (T false x) z.1 z.2).card * (blockWords (T true y) z.2 z.1).card =
          (if z.1 = z.2 then 1 else 0) + (if z ∈ joint.image edge then 1 else 0) := by
      rcases z with ⟨a,b⟩
      rw [hcounts, hcounts]
      simp only [Bool.false_eq_true, ↓reduceIte, eq_comm (a := b)]
      by_cases h : a = b
      · subst b
        have no : ∀ i, edge i ≠ (a,a) := by
          intro i e
          exact hsep i i (by rw [e])
        simp [no, Finset.mem_image]
      · simp only [h, ↓reduceIte, zero_add]
        have hb : ¬ b = a := Ne.symm h
        try simp only [hb, ↓reduceIte, zero_add]
        by_cases h1 : ∃ i ∈ E x, edge i = (a,b)
        · by_cases h2 : ∃ i ∈ E y, edge i = (a,b)
          · obtain ⟨i,hi,hei⟩ := h1
            obtain ⟨j,hj,hej⟩ := h2
            have e : i = j := hinj (hei.trans hej.symm)
            subst j
            have hm : (a,b) ∈ joint.image edge :=
              mem_image.mpr ⟨i,mem_inter.mpr ⟨hi,hj⟩,hei⟩
            simp [hm, show ∃ i ∈ E x, edge i = (a,b) from ⟨i,hi,hei⟩,
              show ∃ i ∈ E y, edge i = (a,b) from ⟨i,hj,hei⟩]
          · have hm : (a,b) ∉ joint.image edge := by
              intro hm
              obtain ⟨i,hi,hei⟩ := mem_image.mp hm
              exact h2 ⟨i,(mem_inter.mp hi).2,hei⟩
            simp [h2, hm]
        · have hm : (a,b) ∉ joint.image edge := by
            intro hm
            obtain ⟨i,hi,hei⟩ := mem_image.mp hm
            exact h1 ⟨i,(mem_inter.mp hi).1,hei⟩
          simp [h1, hm]
    simp_rw [hprod]
    rw [Finset.sum_add_distrib]
    have diag : (∑ z : (Fin (d+1) → Bool) × (Fin (d+1) → Bool),
        if z.1 = z.2 then (1 : Nat) else 0) = 2^(d+1) := by
      rw [Fintype.sum_prod_type (fun z : (Fin (d+1) → Bool) × (Fin (d+1) → Bool) =>
        if z.1 = z.2 then (1 : Nat) else 0)]
      simp
    have image_count : (∑ z : (Fin (d+1) → Bool) × (Fin (d+1) → Bool),
        if z ∈ joint.image edge then (1 : Nat) else 0) = joint.card := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      have hset : univ.filter (fun z => z ∈ joint.image edge) = joint.image edge := by ext z; simp
      rw [hset, Finset.card_image_of_injective _ hinj]
      rfl
    rw [diag, image_count]
    have e : (2^(d+1) : Nat).testBit 0 = false := by
      rw [pow_succ, Nat.testBit_zero]
      simp
    rw [← xor_testBit, e]
    simp only [Bool.false_xor]
    have eq : joint = univ.filter (fun i => x i = true ∧ y i = true) := by
      ext i
      simp [joint,E]
    rw [eq]
    rfl

lemma boundary_gadget (n w : Nat) (hn : 0 < n) (h2 : 2 ≤ n) (hw : 0 < w) :
    ∃ a M, a ≤ n ∧
      (2^(min w (n/2)) * min n (2^(min w (n/2))) + 119) / 120 ≤ M ∧ Gadget n w a M := by
  let L := n/2
  let e := n%2
  have he : e ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  have hL : 0 < L := by dsimp [L]; omega
  have hlen : L+L+e = n := by dsimp [L,e]; omega
  let k := min (w-e) L
  let F := 2^(min w L)
  by_cases hk : 0 < k
  · have hkL : k ≤ L := min_le_right _ _
    have hkw : k+e ≤ w := by have := min_le_left (w-e) L; omega
    obtain ⟨M, hM, hg⟩ := even_gadget L k hL hk hkL
    have hd : min w L ≤ k+1 := by
      dsimp [k]
      omega
    have hf : F ≤ 2 * 2^k := by
      calc F ≤ 2^(k+1) := Nat.pow_le_pow_right (by decide) hd
           _ = 2*2^k := by rw [pow_succ']
    have hmin : min n F ≤ 3 * min L (2^k) := by
      rcases min_choice L (2^k) with h | h
      · rw [h]
        exact (min_le_left _ _).trans (by omega)
      · rw [h]
        exact (min_le_right _ _).trans (by omega)
    have hence : F * min n F ≤ 120*M := by
      calc F*min n F ≤ (2*2^k) * (3*min L (2^k)) := Nat.mul_le_mul hf hmin
      _ = 6*(2^k*min L (2^k)) := by ring
      _ ≤ 120*M := by omega
    have hc : (F*min n F+119)/120 ≤ M := by omega
    have hpad : FiniteGadget (L+L+e) w L M (by omega) :=
      padded_gadget (by omega) (by omega) hkw hg
    have hgg := finite_to_gadget hpad
    rw [hlen] at hgg
    exact ⟨L,M,by omega,hc,hgg⟩
  · have hw1 : w = 1 := by
      have : k = 0 := by omega
      dsimp [k] at this
      omega
    have hF : F = 2 := by simp [F, hw1, min_eq_left (show 1 ≤ L from hL)]
    have hd : 2 ≤ (if n ≤ w+1 then 2^n else 2^w) := by
      by_cases h : n ≤ w+1
      · rw [if_pos h]
        calc
          2 = (2 : Nat)^1 := by norm_num
          _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
      · rw [if_neg h, hw1, pow_one]
    refine ⟨1, _, by omega, le_trans ?_ hd, direct_gadget n w hn h2 hw⟩
    change (F*min n F+119)/120 ≤ 2
    rw [hF]
    have := min_le_right n 2
    omega

end PEqualNP.Outside.L_clb_125_aux

theorem PEqualNP.Outside.L_clb_125 : ∀ (n w p : Nat), 0 < n → 0 < w → 0 < p →
  let D := 2^w
  let smallWidth := min w (n/2)
  let F := 2^smallWidth
  let direct := if n ≤ w+1 then 2^n else D
  let hard := max direct ((F*min n F+119)/120)
  let bits := if n = 1 then 1 else min (2*n*D) (min (1+(2^n+p-1)/p) (1+D*((D+p-1)/p)))
  let Row := Nat → Bool
  let parity := fun (rows : Nat → Row) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      rows site pat))).length.testBit 0
  let run := fun (S : Nat) (start : Fin S)
      (step : Nat → Nat → Fin S → Row → Fin S) (table : Nat → Row) =>
    (List.range p).foldl (fun prev passId =>
      (List.range n).foldl (fun state siteId => step passId siteId state (table siteId)) prev) start
  (∃ (startState : Fin (2^bits)) (advance : Nat → Nat → Fin (2^bits) → Row → Fin (2^bits))
      (answer : Fin (2^bits) → Bool), ∀ full : Nat → Row,
      answer (run (2^bits) startState advance full) = parity full) ∧
    (2 ≤ n → ∀ (S R u v : Nat), 0 < R → 0 < v → u ≤ v →
      ∀ (init : Fin R → Fin S) (update : Fin R → Nat → Nat → Fin S → Row → Fin S)
        (output : Fin R → Fin S → Bool),
        (∀ input : Nat → Row,
          (v+u)*R ≤ 2*v*((List.finRange R).filter (fun coin =>
            output coin (run S (init coin) (update coin) input) == parity input)).length) →
        u^2 * 2^hard ≤ v^2 * S^(2*p-1)) := by
  intro n w p hn hw hp D smallWidth F direct hard bits Row parity run
  open PEqualNP.Outside.L_clb_125_aux in
  have upper : Fits n w p bits := by
    by_cases e : n = 1
    · have h : bits = 1 := if_pos e
      rw [h, e]
      exact one_fit w p hp
    · have h : bits = min (2*n*D) (min (1+(2^n+p-1)/p) (1+D*((D+p-1)/p))) := if_neg e
      rw [h]
      rcases min_choice (2*n*D) (min (1+(2^n+p-1)/p) (1+D*((D+p-1)/p))) with h' | h'
      · rw [h']
        exact raw_fit n w p hn hp
      · rw [h']
        rcases min_choice (1+(2^n+p-1)/p) (1+D*((D+p-1)/p)) with h'' | h''
        · rw [h'']
          exact batch_fit n w p hn hp
        · rw [h'']
          exact vector_fit n w p hn hw hp
  refine ⟨upper, ?_⟩
  intro h2 S R u v hR hv huv init update output hyp
  have directBound := PEqualNP.Outside.L_clb_125_aux.lower_gadget n w 1 direct p S R u v
    (by omega) hp hR huv (PEqualNP.Outside.L_clb_125_aux.direct_gadget n w hn h2 hw)
    init update output hyp
  rcases max_choice direct ((F*min n F+119)/120) with h | h
  · rw [show hard = max direct ((F*min n F+119)/120) from rfl, h]
    exact directBound
  · obtain ⟨a, M, ha, hM, hG⟩ := PEqualNP.Outside.L_clb_125_aux.boundary_gadget n w hn h2 hw
    have bound := PEqualNP.Outside.L_clb_125_aux.lower_gadget n w a M p S R u v
      ha hp hR huv hG init update output hyp
    rw [show hard = max direct ((F*min n F+119)/120) from rfl, h]
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hM)).trans bound
