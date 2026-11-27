import PEqualNP.Defs

/-!
# Truth tables as numbers, monotone tables built from two halves, and a checker for relabelling

Helper of `L-meta-8613` (the five-input assembly). Everything here is general except the
checker `chk`, which is for five inputs.

* `idx x`: the position of `x` in a truth table, `∑ i, if x i then 2 ^ i else 0`.
* `tableNat n f`: the truth table of `f` as a number, built from the half with the last input
  `false` (low bits) and the half with it `true` (high bits). `testBit_table`: bit `idx x` of it
  is `f x`.
* `monoTables n`: the list of tables of monotone functions on `n` inputs, built as ordered pairs
  of monotone tables on `n - 1` inputs. `mono_mem`: the table of a monotone function is in it.
* `chk ts ws`: for each table `t` of `ts`, the matching entry `(c, d, T)` of `ws` names a
  permutation `σ` of five inputs (code `c`), its inverse (code `d`) and a table `T` of `reps`
  with `T` the table of `x ↦ f (x ∘ σ)`. `chk_sound` turns `chk ts ws = true` into `Good t`.
-/

namespace PEqualNP.Library.Mono5

/-- The position of the input `x` in a truth table. -/
def idx {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i : Fin n, if x i then 2 ^ (i : ℕ) else 0

theorem idx_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    idx x = 2 ^ n * (if x (Fin.last n) then 1 else 0) + idx (Fin.init x) := by
  unfold idx
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.init, Fin.val_last]
  split <;> simp [Nat.add_comm] <;> rfl

theorem idx_lt {n : ℕ} (x : Fin n → Bool) : idx x < 2 ^ n := by
  induction n with
  | zero => simp [idx]
  | succ n ih =>
    rw [idx_succ, Nat.pow_succ]
    have := ih (Fin.init x)
    split <;> omega

theorem testBit_idx {n : ℕ} (x : Fin n → Bool) (j : Fin n) : (idx x).testBit j = x j := by
  induction n with
  | zero => exact j.elim0
  | succ n ih =>
    rw [idx_succ, Nat.testBit_two_pow_mul_add _ (idx_lt _)]
    induction j using Fin.lastCases with
    | last => simp only [Fin.val_last, Nat.lt_irrefl, ite_false, Nat.sub_self]; split <;> simp_all
    | cast j =>
      simp only [Fin.val_castSucc, j.isLt, ite_true]
      rw [ih]
      rfl

/-- The truth table of `f` as a number: bit `idx x` is `f x`. -/
def tableNat : (n : ℕ) → ((Fin n → Bool) → Bool) → ℕ
  | 0, f => if f Fin.elim0 then 1 else 0
  | n + 1, f => 2 ^ (2 ^ n) * tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) +
      tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x false))

theorem tableNat_lt (n : ℕ) (f : (Fin n → Bool) → Bool) : tableNat n f < 2 ^ (2 ^ n) := by
  induction n with
  | zero => simp only [tableNat]; split <;> simp
  | succ n ih =>
    simp only [tableNat]
    have h1 := ih (fun x => f (Fin.snoc (α := fun _ => Bool) x true))
    have h2 := ih (fun x => f (Fin.snoc (α := fun _ => Bool) x false))
    have hK : 2 ^ (2 ^ (n + 1)) = 2 ^ (2 ^ n) * 2 ^ (2 ^ n) := by
      rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]
    rw [hK]
    calc 2 ^ 2 ^ n * tableNat n _ + tableNat n _
        < 2 ^ 2 ^ n * tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) + 2 ^ 2 ^ n :=
          by omega
      _ = 2 ^ 2 ^ n * (tableNat n (fun x => f (Fin.snoc (α := fun _ => Bool) x true)) + 1) := by
          ring
      _ ≤ 2 ^ 2 ^ n * 2 ^ 2 ^ n := Nat.mul_le_mul_left _ h1

theorem testBit_table (n : ℕ) (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (tableNat n f).testBit (idx x) = f x := by
  induction n with
  | zero =>
    have hx : x = Fin.elim0 := Subsingleton.elim _ _
    subst hx
    simp only [tableNat, idx, Finset.univ_eq_empty, Finset.sum_empty]
    split <;> simp_all
  | succ n ih =>
    simp only [tableNat]
    rw [Nat.testBit_two_pow_mul_add _ (tableNat_lt _ _), idx_succ]
    have hx : x = Fin.snoc (α := fun _ => Bool) (Fin.init x) (x (Fin.last n)) :=
      (Fin.snoc_init_self x).symm
    have hl := idx_lt (Fin.init x)
    cases hb : x (Fin.last n) with
    | false =>
      simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.zero_add, hl, ite_true]
      rw [ih]
      rw [hb] at hx
      exact congrArg f hx.symm
    | true =>
      simp only [ite_true, Nat.mul_one]
      split
      · omega
      · rw [Nat.add_sub_cancel_left, ih]
        rw [hb] at hx
        exact congrArg f hx.symm

theorem two_pow_mul_add_and (K a b c d : ℕ) (hb : b < 2 ^ K) (hd : d < 2 ^ K) :
    (2 ^ K * a + b) &&& (2 ^ K * c + d) = 2 ^ K * (a &&& c) + (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hd)]
  split <;> simp

theorem table_and (n : ℕ) (f g : (Fin n → Bool) → Bool) :
    tableNat n (fun x => f x && g x) = tableNat n f &&& tableNat n g := by
  induction n with
  | zero =>
    simp only [tableNat]
    rcases Bool.eq_false_or_eq_true (f Fin.elim0) with h | h <;>
      rcases Bool.eq_false_or_eq_true (g Fin.elim0) with h' | h' <;> simp [h, h']
  | succ n ih =>
    simp only [tableNat]
    rw [two_pow_mul_add_and _ _ _ _ _ (tableNat_lt _ _) (tableNat_lt _ _), ih, ih]

/-- Monotone on `n` inputs, in the row's words. -/
def Mono (n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y : Fin n → Bool, (∀ i, x i = true → y i = true) → f x = true → f y = true

/-- One level of the recursion: for each lower half `a` of `as`, each upper half `b` of `L`
with `a ≤ b` bitwise. -/
def step (K : ℕ) (L as : List ℕ) : List ℕ :=
  as.flatMap (fun a => (L.filter (fun b => a &&& b == a)).map (fun b => 2 ^ K * b + a))

theorem step_append (K : ℕ) (L as bs : List ℕ) :
    step K L (as ++ bs) = step K L as ++ step K L bs := List.flatMap_append

/-- The tables of the monotone functions on `n` inputs. -/
def monoTables : ℕ → List ℕ
  | 0 => [0, 1]
  | n + 1 => let L := monoTables n; step (2 ^ n) L L

theorem mono_mem (n : ℕ) (f : (Fin n → Bool) → Bool) (hf : Mono n f) :
    tableNat n f ∈ monoTables n := by
  induction n with
  | zero => simp only [tableNat, monoTables]; split <;> simp
  | succ n ih =>
    set f1 : (Fin n → Bool) → Bool := fun x => f (Fin.snoc (α := fun _ => Bool) x true)
    set f0 : (Fin n → Bool) → Bool := fun x => f (Fin.snoc (α := fun _ => Bool) x false)
    have hm : ∀ b : Bool, Mono n (fun x => f (Fin.snoc (α := fun _ => Bool) x b)) := by
      intro b x y hxy hx
      refine hf _ _ ?_ hx
      intro i
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa using hxy i
    have h0 := ih f0 (hm false)
    have h1 := ih f1 (hm true)
    have hle : (fun x => f0 x && f1 x) = f0 := by
      funext x
      cases h : f0 x with
      | false => simp
      | true =>
        have : f1 x = true := hf _ _ (by
          intro i
          induction i using Fin.lastCases with
          | last => simp
          | cast i => simp) h
        simp [this]
    have hand : tableNat n f0 &&& tableNat n f1 = tableNat n f0 := by
      rw [← table_and, hle]
    show 2 ^ (2 ^ n) * tableNat n f1 + tableNat n f0 ∈ step (2 ^ n) (monoTables n) (monoTables n)
    simp only [step, List.mem_flatMap, List.mem_map, List.mem_filter]
    exact ⟨tableNat n f0, h0, tableNat n f1, ⟨h1, by simp [hand]⟩, rfl⟩

/-! ## The checker, five inputs -/

/-- The map of five inputs with code `c`: input `i` goes to digit `i` of `c` in base five. -/
def dec (c : ℕ) (i : Fin 5) : Fin 5 := ⟨c / 5 ^ (i : ℕ) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- The position `idx (x ∘ dec c)` for the input `x` at position `m`. -/
def pidx (c m : ℕ) : ℕ :=
  (if m.testBit (dec c 0) then 1 else 0) + (if m.testBit (dec c 1) then 2 else 0) +
  (if m.testBit (dec c 2) then 4 else 0) + (if m.testBit (dec c 3) then 8 else 0) +
  (if m.testBit (dec c 4) then 16 else 0)

theorem pidx_eq (c m : ℕ) :
    pidx c m = ∑ i : Fin 5, if m.testBit (dec c i) then 2 ^ (i : ℕ) else 0 := by
  simp only [pidx, Fin.sum_univ_five]
  rfl

/-- The entry `(c, d, T)` is right for the table `t`, with `T` in the list `R`. -/
def Ent (R : List ℕ) (t c d T : ℕ) : Prop :=
  (∀ i : Fin 5, dec d (dec c i) = i) ∧ T ∈ R ∧ ∀ m < 32, t.testBit (pidx c m) = T.testBit m

instance (R : List ℕ) (t c d T : ℕ) : Decidable (Ent R t c d T) := by
  unfold Ent; infer_instance

/-- Every table of `ts` has its right entry, in order, in `ws`. -/
def chk (R : List ℕ) : List ℕ → List (ℕ × ℕ × ℕ) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | t :: ts, (c, d, T) :: ws => decide (Ent R t c d T) && chk R ts ws

/-- `t` is, after relabelling its inputs by a map with a left inverse, a table of `R`. -/
def Good (R : List ℕ) (t : ℕ) : Prop :=
  ∃ σ τ : Fin 5 → Fin 5, (∀ i, τ (σ i) = i) ∧ ∃ T ∈ R,
    ∀ m < 32, t.testBit (∑ i : Fin 5, if m.testBit (σ i) then 2 ^ (i : ℕ) else 0) = T.testBit m

theorem chk_sound (R : List ℕ) :
    ∀ (ts : List ℕ) (ws : List (ℕ × ℕ × ℕ)), chk R ts ws = true → ∀ t ∈ ts, Good R t
  | [], _, _ => by simp
  | _ :: _, [], h => by simp [chk] at h
  | t :: ts, (c, d, T) :: ws, h => by
    simp only [chk, Bool.and_eq_true, decide_eq_true_eq] at h
    intro t' ht'
    rcases List.mem_cons.1 ht' with rfl | ht'
    · obtain ⟨h1, h2, h3⟩ := h.1
      exact ⟨dec c, dec d, h1, T, h2, fun m hm => by rw [← pidx_eq]; exact h3 m hm⟩
    · exact chk_sound R ts ws h.2 t' ht'

end PEqualNP.Library.Mono5

/-! Data of `L-meta-8613`, written by notes/data/table2/statements/mono5/lean_cover.py. The 210 listed tables in the row's order, the 168 monotone tables of four inputs, and their split into pieces. -/

namespace PEqualNP.Library.Mono5

/-- The 210 listed tables, in the order of the row. -/
def reps : List ℕ :=
  [0xa8808000, 0xa8888880, 0xaaa8a880, 0xe8808080, 0xe8808880, 0xe880a880, 0xe880e880, 0xe8888880, 0xe888a080, 0xe888a880, 0xe888e080, 0xe888e880, 0xe8a8a800, 0xe8a8a880, 0xe8a8a888, 0xe8a8c880, 0xe8a8e800, 0xe8a8e880, 0xe8a8e888, 0xe8e8e880, 0xeaa8a880, 0xeaa8a888, 0xeaa8a8a8, 0xeaa8aaa8, 0xeaa8c000, 0xeaa8c080, 0xeaa8c880, 0xeaa8c888, 0xeaa8e880, 0xeaa8e888, 0xeaa8e8a8, 0xeaaaaaa8, 0xeaaac880, 0xeaaae880, 0xeaaaeaa8, 0xeac0e880, 0xeac8e000, 0xeac8e080, 0xeac8e880, 0xeac8e888, 0xeac8e8c0, 0xeae8e800, 0xeae8e888, 0xeae8e8a8, 0xeae8e8c0, 0xeae8e8c8, 0xeae8ea80, 0xeae8ea88, 0xeae8eaa8, 0xeaeaeaa8, 0xeee0e880, 0xeee0e8a0, 0xeee0eac0, 0xeee8e888, 0xeee8e8a0, 0xeee8e8a8, 0xeee8e8e0, 0xeee8eaa0, 0xeee8eaa8, 0xeee8eac0, 0xeee8eac8, 0xeee8eae0, 0xeee8eae8, 0xeeeaeaa0, 0xeeeaeaa8, 0xeeeaeac8, 0xeeeaeae0, 0xeeeaeae8, 0xfee8e880, 0xfee8e888, 0xfee8e8a8, 0xfee8e8e8, 0xfee8eaa8, 0xfee8eac0, 0xfee8eac8, 0xfee8eae8, 0xfee8eee0, 0xfee8eee8, 0xfee8fee8, 0xfeeaeaa8, 0xfeeaeaaa, 0xfeeaeac0, 0xfeeaeac8, 0xfeeaeae8, 0xfeeaece0, 0xfeeaece8, 0xfeeaeee0, 0xfeeaeee8, 0xfeeafcc8, 0xfeeafce8, 0xfeeafee8, 0xfeeeeee0, 0xfeeeeee8, 0xfeeeeeea, 0xfeeefaa8, 0xfeeefac0, 0xfeeefae8, 0xfeeefee8, 0xfefefee8, 0xfffefee8, 0xfffefeea, 0x0, 0xaaaaaaaa, 0x88888888, 0xeeeeeeee, 0xffffffff, 0x80808080, 0xa8a8a8a8, 0xeaeaeaea, 0xfefefefe, 0x80008000, 0x88808880, 0xa888a888, 0xaaa8aaa8, 0xeaaaeaaa, 0xeac0eac0, 0xeee0eee0, 0xeeeaeeea, 0xfeeefeee, 0xfffefffe, 0x80000000, 0x80808000, 0x88808080, 0x88888880, 0xa8888888, 0xa888a000, 0xa8a8a800, 0xa8a8a888, 0xaaa8a8a8, 0xaaaaaaa8, 0xe8e8e8e8, 0xeaaaaaaa, 0xeaaac000, 0xeac8eac8, 0xeaeaea00, 0xeaeaeaaa, 0xeaeaeac0, 0xeeeaeaea, 0xeeeeeee0, 0xeeeeeeea, 0xfeeeeeee, 0xfeeefaaa, 0xfefefeaa, 0xfefefeee, 0xfffefefe, 0xfffffffe, 0xa880a880, 0xa888a080, 0xe888e888, 0xe8a8e8a8, 0xeaaac080, 0xeaaac888, 0xeac8e0c0, 0xeac8eac0, 0xeae8eae8, 0xeaeaeac8, 0xeee0eae0, 0xeee8eee8, 0xeeeaece0, 0xeeeaeee0, 0xfeeafeea, 0xfeeefaea, 0x88808000, 0xa8808080, 0xa8808880, 0xa888a880, 0xa8a8a880, 0xaaa8a888, 0xe8888888, 0xe888a000, 0xe888a888, 0xe888e000, 0xe8a8a8a8, 0xe8a8c800, 0xe8a8c888, 0xe8e8e800, 0xe8e8e888, 0xe8e8e8a8, 0xeaa8eaa8, 0xeaaae888, 0xeaaae8a8, 0xeac0e8c0, 0xeac8e8c8, 0xeae8e8e8, 0xeae8ea00, 0xeae8eac0, 0xeae8eac8, 0xeaeaea80, 0xeaeaea88, 0xeaeaeae8, 0xeee0e8e0, 0xeee8e8e8, 0xeee8eee0, 0xeeeaeaaa, 0xeeeaeac0, 0xeeeaece8, 0xeeeaeee8, 0xeeeeeee8, 0xfeeaeaea, 0xfeeaeeea, 0xfeeafcc0, 0xfeeefac8, 0xfeeefee0, 0xfeeefeea, 0xfefefea8, 0xfefefeea, 0xfffefeee, 0xe8808000, 0xeae8e880, 0xeee8e880]

/-- The 168 monotone tables of four inputs, in the order of `monoTables 4`. -/
def E4 : List ℕ :=
  [0x0, 0x8000, 0xc000, 0xa000, 0xe000, 0xf000, 0x8800, 0xc800, 0xa800, 0xe800, 0xf800, 0xcc00, 0xec00, 0xfc00, 0xaa00, 0xea00, 0xfa00, 0xee00, 0xfe00, 0xff00, 0x8080, 0xc080, 0xa080, 0xe080, 0xf080, 0x8880, 0xc880, 0xa880, 0xe880, 0xf880, 0xcc80, 0xec80, 0xfc80, 0xaa80, 0xea80, 0xfa80, 0xee80, 0xfe80, 0xff80, 0xc0c0, 0xe0c0, 0xf0c0, 0xc8c0, 0xe8c0, 0xf8c0, 0xccc0, 0xecc0, 0xfcc0, 0xeac0, 0xfac0, 0xeec0, 0xfec0, 0xffc0, 0xa0a0, 0xe0a0, 0xf0a0, 0xa8a0, 0xe8a0, 0xf8a0, 0xeca0, 0xfca0, 0xaaa0, 0xeaa0, 0xfaa0, 0xeea0, 0xfea0, 0xffa0, 0xe0e0, 0xf0e0, 0xe8e0, 0xf8e0, 0xece0, 0xfce0, 0xeae0, 0xfae0, 0xeee0, 0xfee0, 0xffe0, 0xf0f0, 0xf8f0, 0xfcf0, 0xfaf0, 0xfef0, 0xfff0, 0x8888, 0xc888, 0xa888, 0xe888, 0xf888, 0xcc88, 0xec88, 0xfc88, 0xaa88, 0xea88, 0xfa88, 0xee88, 0xfe88, 0xff88, 0xc8c8, 0xe8c8, 0xf8c8, 0xccc8, 0xecc8, 0xfcc8, 0xeac8, 0xfac8, 0xeec8, 0xfec8, 0xffc8, 0xa8a8, 0xe8a8, 0xf8a8, 0xeca8, 0xfca8, 0xaaa8, 0xeaa8, 0xfaa8, 0xeea8, 0xfea8, 0xffa8, 0xe8e8, 0xf8e8, 0xece8, 0xfce8, 0xeae8, 0xfae8, 0xeee8, 0xfee8, 0xffe8, 0xf8f8, 0xfcf8, 0xfaf8, 0xfef8, 0xfff8, 0xcccc, 0xeccc, 0xfccc, 0xeecc, 0xfecc, 0xffcc, 0xecec, 0xfcec, 0xeeec, 0xfeec, 0xffec, 0xfcfc, 0xfefc, 0xfffc, 0xaaaa, 0xeaaa, 0xfaaa, 0xeeaa, 0xfeaa, 0xffaa, 0xeaea, 0xfaea, 0xeeea, 0xfeea, 0xffea, 0xfafa, 0xfefa, 0xfffa, 0xeeee, 0xfeee, 0xffee, 0xfefe, 0xfffe, 0xffff]

def c00 : List ℕ := [0x0, 0x8000, 0xc000, 0xa000, 0xe000, 0xf000, 0x8800, 0xc800, 0xa800, 0xe800, 0xf800, 0xcc00, 0xec00, 0xfc00]

def c01 : List ℕ := [0xaa00, 0xea00, 0xfa00, 0xee00, 0xfe00, 0xff00, 0x8080, 0xc080, 0xa080, 0xe080, 0xf080, 0x8880, 0xc880, 0xa880]

def c02 : List ℕ := [0xe880, 0xf880, 0xcc80, 0xec80, 0xfc80, 0xaa80, 0xea80, 0xfa80, 0xee80, 0xfe80, 0xff80, 0xc0c0, 0xe0c0, 0xf0c0]

def c03 : List ℕ := [0xc8c0, 0xe8c0, 0xf8c0, 0xccc0, 0xecc0, 0xfcc0, 0xeac0, 0xfac0, 0xeec0, 0xfec0, 0xffc0, 0xa0a0, 0xe0a0, 0xf0a0]

def c04 : List ℕ := [0xa8a0, 0xe8a0, 0xf8a0, 0xeca0, 0xfca0, 0xaaa0, 0xeaa0, 0xfaa0, 0xeea0, 0xfea0, 0xffa0, 0xe0e0, 0xf0e0, 0xe8e0]

def c05 : List ℕ := [0xf8e0, 0xece0, 0xfce0, 0xeae0, 0xfae0, 0xeee0, 0xfee0, 0xffe0, 0xf0f0, 0xf8f0, 0xfcf0, 0xfaf0, 0xfef0, 0xfff0]

def c06 : List ℕ := [0x8888, 0xc888, 0xa888, 0xe888, 0xf888, 0xcc88, 0xec88, 0xfc88, 0xaa88, 0xea88, 0xfa88, 0xee88, 0xfe88, 0xff88]

def c07 : List ℕ := [0xc8c8, 0xe8c8, 0xf8c8, 0xccc8, 0xecc8, 0xfcc8, 0xeac8, 0xfac8, 0xeec8, 0xfec8, 0xffc8, 0xa8a8, 0xe8a8, 0xf8a8]

def c08 : List ℕ := [0xeca8, 0xfca8, 0xaaa8, 0xeaa8, 0xfaa8, 0xeea8, 0xfea8, 0xffa8, 0xe8e8, 0xf8e8, 0xece8, 0xfce8, 0xeae8, 0xfae8]

def c09 : List ℕ := [0xeee8, 0xfee8, 0xffe8, 0xf8f8, 0xfcf8, 0xfaf8, 0xfef8, 0xfff8, 0xcccc, 0xeccc, 0xfccc, 0xeecc, 0xfecc, 0xffcc]

def c10 : List ℕ := [0xecec, 0xfcec, 0xeeec, 0xfeec, 0xffec, 0xfcfc, 0xfefc, 0xfffc, 0xaaaa, 0xeaaa, 0xfaaa, 0xeeaa, 0xfeaa, 0xffaa]

def c11 : List ℕ := [0xeaea, 0xfaea, 0xeeea, 0xfeea, 0xffea, 0xfafa, 0xfefa, 0xfffa, 0xeeee, 0xfeee, 0xffee, 0xfefe, 0xfffe, 0xffff]

theorem monoTables_four : monoTables 4 = E4 := by decide +kernel

theorem E4_split : E4 = c00 ++ (c01 ++ (c02 ++ (c03 ++ (c04 ++ (c05 ++ (c06 ++ (c07 ++ (c08 ++ (c09 ++ (c10 ++ (c11))))))))))) := by decide +kernel

/-- Every listed table is in the row's set. -/
theorem reps_sub : ∀ T ∈ reps, T ∈ ({0xa8808000, 0xa8888880, 0xaaa8a880, 0xe8808080, 0xe8808880, 0xe880a880, 0xe880e880, 0xe8888880, 0xe888a080, 0xe888a880, 0xe888e080, 0xe888e880, 0xe8a8a800, 0xe8a8a880, 0xe8a8a888, 0xe8a8c880, 0xe8a8e800, 0xe8a8e880, 0xe8a8e888, 0xe8e8e880, 0xeaa8a880, 0xeaa8a888, 0xeaa8a8a8, 0xeaa8aaa8, 0xeaa8c000, 0xeaa8c080, 0xeaa8c880, 0xeaa8c888, 0xeaa8e880, 0xeaa8e888, 0xeaa8e8a8, 0xeaaaaaa8, 0xeaaac880, 0xeaaae880, 0xeaaaeaa8, 0xeac0e880, 0xeac8e000, 0xeac8e080, 0xeac8e880, 0xeac8e888, 0xeac8e8c0, 0xeae8e800, 0xeae8e888, 0xeae8e8a8, 0xeae8e8c0, 0xeae8e8c8, 0xeae8ea80, 0xeae8ea88, 0xeae8eaa8, 0xeaeaeaa8, 0xeee0e880, 0xeee0e8a0, 0xeee0eac0, 0xeee8e888, 0xeee8e8a0, 0xeee8e8a8, 0xeee8e8e0, 0xeee8eaa0, 0xeee8eaa8, 0xeee8eac0, 0xeee8eac8, 0xeee8eae0, 0xeee8eae8, 0xeeeaeaa0, 0xeeeaeaa8, 0xeeeaeac8, 0xeeeaeae0, 0xeeeaeae8, 0xfee8e880, 0xfee8e888, 0xfee8e8a8, 0xfee8e8e8, 0xfee8eaa8, 0xfee8eac0, 0xfee8eac8, 0xfee8eae8, 0xfee8eee0, 0xfee8eee8, 0xfee8fee8, 0xfeeaeaa8, 0xfeeaeaaa, 0xfeeaeac0, 0xfeeaeac8, 0xfeeaeae8, 0xfeeaece0, 0xfeeaece8, 0xfeeaeee0, 0xfeeaeee8, 0xfeeafcc8, 0xfeeafce8, 0xfeeafee8, 0xfeeeeee0, 0xfeeeeee8, 0xfeeeeeea, 0xfeeefaa8, 0xfeeefac0, 0xfeeefae8, 0xfeeefee8, 0xfefefee8, 0xfffefee8, 0xfffefeea, 0x00000000, 0xaaaaaaaa, 0x88888888, 0xeeeeeeee, 0xffffffff, 0x80808080, 0xa8a8a8a8, 0xeaeaeaea, 0xfefefefe, 0x80008000, 0x88808880, 0xa888a888, 0xaaa8aaa8, 0xeaaaeaaa, 0xeac0eac0, 0xeee0eee0, 0xeeeaeeea, 0xfeeefeee, 0xfffefffe, 0x80000000, 0x80808000, 0x88808080, 0x88888880, 0xa8888888, 0xa888a000, 0xa8a8a800, 0xa8a8a888, 0xaaa8a8a8, 0xaaaaaaa8, 0xe8e8e8e8, 0xeaaaaaaa, 0xeaaac000, 0xeac8eac8, 0xeaeaea00, 0xeaeaeaaa, 0xeaeaeac0, 0xeeeaeaea, 0xeeeeeee0, 0xeeeeeeea, 0xfeeeeeee, 0xfeeefaaa, 0xfefefeaa, 0xfefefeee, 0xfffefefe, 0xfffffffe, 0xa880a880, 0xa888a080, 0xe888e888, 0xe8a8e8a8, 0xeaaac080, 0xeaaac888, 0xeac8e0c0, 0xeac8eac0, 0xeae8eae8, 0xeaeaeac8, 0xeee0eae0, 0xeee8eee8, 0xeeeaece0, 0xeeeaeee0, 0xfeeafeea, 0xfeeefaea, 0x88808000, 0xa8808080, 0xa8808880, 0xa888a880, 0xa8a8a880, 0xaaa8a888, 0xe8888888, 0xe888a000, 0xe888a888, 0xe888e000, 0xe8a8a8a8, 0xe8a8c800, 0xe8a8c888, 0xe8e8e800, 0xe8e8e888, 0xe8e8e8a8, 0xeaa8eaa8, 0xeaaae888, 0xeaaae8a8, 0xeac0e8c0, 0xeac8e8c8, 0xeae8e8e8, 0xeae8ea00, 0xeae8eac0, 0xeae8eac8, 0xeaeaea80, 0xeaeaea88, 0xeaeaeae8, 0xeee0e8e0, 0xeee8e8e8, 0xeee8eee0, 0xeeeaeaaa, 0xeeeaeac0, 0xeeeaece8, 0xeeeaeee8, 0xeeeeeee8, 0xfeeaeaea, 0xfeeaeeea, 0xfeeafcc0, 0xfeeefac8, 0xfeeefee0, 0xfeeefeea, 0xfefefea8, 0xfefefeea, 0xfffefeee, 0xe8808000, 0xeae8e880, 0xeee8e880} : Finset ℕ) := by
  decide +kernel

end PEqualNP.Library.Mono5
