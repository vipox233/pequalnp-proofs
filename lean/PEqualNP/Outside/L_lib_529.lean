import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_529

abbrev Rows := Nat → Nat → Bool

def pack (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range n).foldl (fun (acc bit : Nat) => acc ||| ((f bit).toNat <<< bit)) 0

theorem pack_bit (n : Nat) (f : Nat → Bool) (k : Nat) :
    (pack n f).testBit k = (decide (k < n) && f k) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack,List.range_succ,List.foldl_append]
    change ((pack n f) ||| ((f n).toNat <<< n)).testBit k = _
    rw [Nat.testBit_or,ih,Nat.testBit_shiftLeft,Nat.testBit_bool_toNat]
    rcases Nat.lt_trichotomy k n with h|h|h
    · have h₁ : ¬k ≥ n := by omega
      have h₂ : k < n+1 := by omega
      simp [h,h₁,h₂]
    · subst n; simp
    · have h₁ : ¬k < n := by omega
      have h₂ : ¬k < n+1 := by omega
      have h₃ : k-n≠0 := by omega
      simp [h₁,h₂,h₃]

def window (w n word site : Nat) := pack (w+1) (fun bit => word.testBit ((site+bit)%n))

theorem left_window {w L site : Nat} (h : site < L) (b : Nat) :
    window w (L+w) b site = (b >>> site) % (2*2^w) := by
  apply Nat.eq_of_testBit_eq
  intro k
  have e : 2*2^w = 2^(w+1) := by rw [Nat.pow_succ,Nat.mul_comm]
  rw [window, pack_bit, e, Nat.testBit_mod_two_pow,Nat.testBit_shiftRight]
  by_cases hp : k < w+1
  · simp [hp,Nat.mod_eq_of_lt (show site+k < L+w by omega)]
  · simp [hp]

def run (w L : Nat) (x : Rows) (word : Nat) : Bool :=
  (List.range L).all (fun i => x i ((word >>> i) % (2*2^w)))

def mass (w L : Nat) (x : Rows) (s z : Nat) := ((List.range (2^(w+L))).filter
  (fun bits => bits % 2^w == s && (bits >>> L) % 2^w == z && run w L x bits)).length

def cycOK (w L : Nat) (x y : Rows) (word : Nat) := (List.range (L+w)).all
  (fun i => if i < L then x i (window w (L+w) word i) else y (i-L) (window w (L+w) word i))

def count (w m L : Nat) (x y : Rows) := ((List.range (2^(L+w))).filter
  (cycOK w L x y)).length % m

def tester (w s z : Nat) : Rows := fun i pat =>
  (pat.testBit 0 == z.testBit i) && (pat.testBit w == s.testBit i)

theorem test_window {w L r : Nat} (hr : r < w) (word s z : Nat) :
    tester w s z r (window w (L+w) word (L+r)) =
      ((word.testBit (L+r) == z.testBit r) && (word.testBit r == s.testBit r)) := by
  have e : (L+r+w)%(L+w) = r := by
    rw [show L+r+w = r+(L+w) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  simp only [tester,window,pack_bit,Nat.zero_lt_succ,Nat.lt_succ_self,decide_true,
    Bool.true_and,Nat.add_zero,Nat.mod_eq_of_lt (show L+r < L+w by omega),e]

theorem low_eq_iff {w x a : Nat} (ha : a < 2^w) :
    x % 2^w = a ↔ ∀ i < w, x.testBit i = a.testBit i := by
  constructor
  · intro e i hi; have hh := congrArg (fun t : Nat => t.testBit i) e
    simpa [hi] using hh
  · intro h; apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_mod_two_pow]
    by_cases hi : i < w
    · simp [hi,h i hi]
    · have hei : 2^w ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      simp [hi,Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha hei)]

theorem split_cyc (w L : Nat) (x y : Rows) (word : Nat) :
    cycOK w L x y word = true ↔ run w L x word = true ∧
    ∀ r < w, y r (window w (L+w) word (L+r)) = true := by
  simp only [cycOK,run,List.all_eq_true,List.mem_range]
  constructor
  · intro h
    constructor
    · intro i hi
      have hx := h i (show i < L+w by omega)
      simpa [hi,left_window hi] using hx
    · intro r hr
      have hx := h (L+r) (show L+r < L+w by omega)
      simpa [show ¬ L+r < L by omega] using hx
  · rintro ⟨hx,hy⟩ i hi
    by_cases h : i < L
    · simpa [h,left_window h] using hx i h
    · have hh := hy (i-L) (by omega)
      have eq : L+(i-L) = i := by omega
      simpa [h,eq] using hh

theorem singleton_separates (w m L : Nat) (x : Rows) (s z : Fin (2^w)) :
    count w m L x (tester w s z) = mass w L x s z % m := by
  unfold count mass
  rw [Nat.add_comm w L]
  congr 2
  apply List.filter_congr; intro word _
  apply Bool.eq_iff_iff.mpr
  rw [split_cyc]
  have aux (i : Nat) (hi : i < w) : tester w s z i (window w (L+w) word (L+i)) = true ↔
      word.testBit (L+i) = z.val.testBit i ∧ word.testBit i = s.val.testBit i := by
    rw [test_window hi]; simp
  simp only [Bool.and_eq_true, beq_iff_eq,low_eq_iff s.isLt,low_eq_iff z.isLt,Nat.testBit_shiftRight]
  constructor
  · rintro ⟨h,all⟩
    exact ⟨⟨fun i hi => ((aux i hi).mp (all i hi)).2,
      fun i hi => ((aux i hi).mp (all i hi)).1⟩,h⟩
  · rintro ⟨⟨hs,hz⟩,h⟩
    exact ⟨h,fun i hi => (aux i hi).mpr ⟨hz i hi,hs i hi⟩⟩

def closeWord (w s z r : Nat) := pack (w+1) (fun bit =>
  if r+bit < w then z.testBit (r+bit) else s.testBit (r+bit-w))

theorem right_window {w L r : Nat} (hr : r < w) (word : Nat) :
    window w (L+w) word (L+r) = closeWord w (word % 2^w) ((word >>> L) % 2^w) r := by
  apply Nat.eq_of_testBit_eq; intro b
  simp only [window,closeWord,pack_bit]
  by_cases hb : b < w+1
  · simp only [hb,decide_true,Bool.true_and]
    by_cases hrb : r+b < w
    · have e : L+(r+b) < L+w := by omega
      simp [hrb,Nat.mod_eq_of_lt e,Nat.add_assoc]
    · have hd : r+b-w < w := by omega
      have hd' : r+b-w < L+w := by omega
      have eq : L+r+b = (r+b-w)+(L+w) := by omega
      simp [hrb,hd,eq,Nat.mod_eq_of_lt hd']
  · simp [hb]

def closes (w : Nat) (y : Rows) (s z : Nat) :=
  (List.range w).all (fun i => y i (closeWord w s z i))

theorem full_cyc (w L : Nat) (x y : Rows) (word : Nat) :
    cycOK w L x y word =
      (run w L x word && closes w y (word % 2^w) ((word >>> L) % 2^w)) := by
  apply Bool.eq_iff_iff.mpr
  rw [split_cyc]
  simp only [Bool.and_eq_true,closes,List.all_eq_true,List.mem_range]
  constructor <;> rintro ⟨h,t⟩ <;> refine ⟨h,fun i hi => ?_⟩
  · rw [← right_window hi]; exact t i hi
  · rw [right_window hi]; exact t i hi

def sumN (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n+1 => sumN n f + f n

theorem sumN_congr (n : Nat) {f g : Nat → Nat} (h : ∀ i < n, f i=g i) : sumN n f = sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumN,ih (fun i hi => h i (by omega)),h n (by omega)]

theorem sumN_add (n : Nat) (f g : Nat → Nat) :
    sumN n (fun i => f i + g i) = sumN n f + sumN n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumN,ih]; omega

theorem sumN_zero (n : Nat) : sumN n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumN,ih]

theorem sumN_single (n i a : Nat) :
    sumN n (fun j => if j=i then a else 0) = if i < n then a else 0 := by
  induction n with
  | zero => simp [sumN]
  | succ n ih =>
    simp only [sumN,ih]
    by_cases e : n=i
    · subst i; simp
    · by_cases h : i < n
      · simp [h,e,show i < n+1 by omega]
      · simp [h,e,show ¬i < n+1 by omega]

theorem sumN_mod_congr (n m : Nat) {f g : Nat → Nat} (h : ∀ i < n, f i%m=g i%m) :
    sumN n f % m = sumN n g % m := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumN]
    rw [Nat.add_mod,ih (fun i hi => h i (by omega)),h n (by omega),← Nat.add_mod]

theorem histogram (xs : List α) (n : Nat) (tag : α → Nat) (p : α → Bool)
    (h : ∀ x ∈ xs, tag x < n) :
    (xs.filter p).length = sumN n (fun i => (xs.filter (fun x => (tag x == i) && p x)).length) := by
  induction xs with
  | nil => simp [sumN_zero]
  | cons a xs ih =>
    have hh := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    have eqsum : sumN n (fun i => ((a::xs).filter (fun x => (tag x == i) && p x)).length) =
        sumN n (fun i => (xs.filter (fun x => (tag x == i) && p x)).length +
          (if i=tag a then (p a).toNat else 0)) := by
      apply sumN_congr; intro i _
      by_cases e : i=tag a
      · subst i; cases hp : p a <;> simp [hp,List.filter_cons]
      · cases hp : p a <;> simp [hp,e,Ne.symm e,List.filter_cons]
    rw [eqsum,sumN_add,sumN_single,if_pos ha,← hh]
    cases hpa : p a <;> simp [hpa,List.filter_cons]

theorem total_count (w m L : Nat) (x y : Rows) :
    count w m L x y = (sumN (2^w) (fun s => sumN (2^w)
      (fun z => if closes w y s z then mass w L x s z else 0))) % m := by
  unfold count
  congr 1
  let words := List.range (2^(L+w))
  let seed := fun word : Nat => word % 2^w
  let tail := fun word : Nat => (word >>> L) % 2^w
  change (words.filter (cycOK w L x y)).length = _
  rw [histogram words (2^w) seed _ (fun a _ => Nat.mod_lt _ (Nat.two_pow_pos _))]
  apply sumN_congr; intro s _
  rw [histogram words (2^w) tail _ (fun a _ => Nat.mod_lt _ (Nat.two_pow_pos _))]
  apply sumN_congr; intro z _
  have eq : words.filter (fun word => (tail word == z) && ((seed word == s) && cycOK w L x y word)) =
      words.filter (fun word => (seed word == s) && (tail word == z) && run w L x word && closes w y s z) := by
    apply List.filter_congr; intro word _
    rw [full_cyc]
    change ((tail word == z) && ((seed word == s) && (run w L x word && closes w y (seed word) (tail word)))) = _
    by_cases hs : seed word=s <;> by_cases hz : tail word=z <;> simp_all [Bool.and_assoc,show ∀ a b : Nat, (a == b) = decide (a=b) from fun _ _ => rfl]
  rw [eq]
  by_cases hg : closes w y s z
  · simp [hg,mass,seed,tail,words,Nat.add_comm w L]
  · simp [hg]

theorem signature_complete (w m L : Nat) (x x' : Rows) :
    (∀ y, count w m L x y = count w m L x' y) ↔
      ∀ s z : Fin (2^w), mass w L x s z % m = mass w L x' s z % m := by
  constructor
  · intro h s z
    simpa only [singleton_separates] using h (tester w s z)
  · intro h y
    rw [total_count,total_count]; apply sumN_mod_congr; intro s hs
    apply sumN_mod_congr; intro z hz
    by_cases hy : closes w y s z
    · simpa [hy] using h ⟨s,hs⟩ ⟨z,hz⟩
    · simp [hy]

def gate (w k u v : Nat) : Rows := fun i pat =>
  (pat.testBit 0 == pat.testBit w) || ((i == k) && (pat == closeWord w v u k))

theorem close_bit {w r b : Nat} (hb : b ≤ w) (z s : Nat) :
    (closeWord w z s r).testBit b = if r+b < w then s.testBit (r+b) else z.testBit (r+b-w) := by
  rw [closeWord,pack_bit]; simp [show b < w+1 by omega]

theorem close_lohi {w r : Nat} (hr : r < w) (z s : Nat) :
    (closeWord w z s r).testBit 0 = s.testBit r ∧ (closeWord w z s r).testBit w = z.testBit r := by
  constructor
  · rw [close_bit (Nat.zero_le _)]; simp [hr]
  · rw [close_bit (Nat.le_refl _)]; simp [show ¬r+w < w by omega]

theorem eq_of_low_bits {w : Nat} {s z : Fin (2^w)} (h : ∀ i < w, s.val.testBit i=z.val.testBit i) :
    s=z := Fin.ext (by simpa [Nat.mod_eq_of_lt s.isLt] using (low_eq_iff z.isLt).mpr h)

theorem gate_iff {w k : Nat} (hk : k < w) (u v s z : Fin (2^w))
    (uv : ∀ i < w, i≠k → u.val.testBit i=v.val.testBit i) :
    (∀ i < w, gate w k u v i (closeWord w z s i) = true) ↔ s=z ∨ (s=u ∧ z=v) := by
  have gat (i : Nat) (hi : i < w) :
      gate w k u v i (closeWord w z s i) = true ↔
      s.val.testBit i=z.val.testBit i ∨ (i=k ∧ closeWord w z s i=closeWord w v u k) := by
    rw [gate]; simp only [(close_lohi hi _ _).1,(close_lohi hi _ _).2,
      Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
  constructor
  · intro h
    by_cases eq : s=z
    · exact Or.inl eq
    · right
      have same (i : Nat) (hi : i < w) (ne : i≠k) : s.val.testBit i=z.val.testBit i := by
        rcases (gat i hi).mp (h i hi) with hx | ⟨hx,_⟩
        · exact hx
        · contradiction
      have pivot : closeWord w z s k=closeWord w v u k := by
        rcases (gat k hk).mp (h k hk) with hx|⟨_,hx⟩
        · exfalso
          apply eq
          apply eq_of_low_bits
          intro i hi
          by_cases e : i=k
          · simpa [e] using hx
          · exact same _ hi e
        · exact hx
      have tail (i : Nat) (hi : i < w) (hki : k ≤ i) : s.val.testBit i = u.val.testBit i := by
        have hb : i-k ≤ w := by omega
        have hp := congrArg (fun p : Nat => p.testBit (i-k)) pivot
        have hidx : k+(i-k) = i := by omega
        simpa [close_bit hb,hidx,hi] using hp
      have head (i : Nat) (hi : i ≤ k) : z.val.testBit i = v.val.testBit i := by
        have hb : w+i-k ≤ w := by omega
        have hp := congrArg (fun p : Nat => p.testBit (w+i-k)) pivot
        have hidx : k+(w+i-k) = w+i := by omega
        simpa [close_bit hb,hidx,show ¬w+i < w by omega] using hp
      constructor <;> apply eq_of_low_bits <;> intro i hi
      · by_cases hki : k ≤ i
        · exact tail i hi hki
        · have ne : i≠k := by omega
          exact (same i hi ne).trans ((head i (by omega)).trans (uv i hi ne).symm)
      · by_cases hik : i ≤ k
        · exact head i hik
        · have ne : i≠k := by omega
          exact (same i hi ne).symm.trans ((tail i hi (by omega)).trans (uv i hi ne))
  · rintro (rfl|⟨rfl,rfl⟩) i hi
    · exact (gat i hi).mpr (Or.inl rfl)
    · apply (gat i hi).mpr
      by_cases e : i=k
      · subst i; exact Or.inr ⟨rfl,rfl⟩
      · exact Or.inl (uv i hi e)

def prepend (w : Nat) (a x : Rows) : Rows := fun i p => if i < w then a i p else x (i-w) p

theorem inside_prefix {w i : Nat} (hi : i < w) (s : Fin (2^w)) (q : Nat) :
    (((2^w*q+s.val) >>> i) % (2*2^w)) = closeWord w (q%2^w) s i := by
  apply Nat.eq_of_testBit_eq; intro k
  rw [show 2*2^w=2^(w+1) by rw [Nat.pow_succ,Nat.mul_comm],
    Nat.testBit_mod_two_pow,Nat.testBit_shiftRight,Nat.testBit_two_pow_mul_add q s.isLt,closeWord,pack_bit]
  by_cases hk : k < w+1
  · by_cases hh : i+k < w
    · simp [hk,hh]
    · simp [hk,hh,show i+k-w < w by omega]
  · simp [hk]

theorem shift_join {w : Nat} (s : Fin (2^w)) (q i : Nat) :
    (2^w*q+s.val) >>> (w+i) = q >>> i := by
  apply Nat.eq_of_testBit_eq; intro k
  simp only [Nat.testBit_shiftRight,Nat.testBit_two_pow_mul_add q s.isLt]
  simp [show ¬w+i+k < w by omega,show w+i+k-w=i+k by omega]

theorem run_prepend (w h : Nat) (a x : Rows) (s : Fin (2^w)) (q : Nat) :
    run w (w+h) (prepend w a x) (2^w*q+s.val) =
      (closes w a (q%2^w) s && run w h x q) := by
  apply Bool.eq_iff_iff.mpr
  simp only [run,closes,List.all_eq_true,List.mem_range,Bool.and_eq_true]
  constructor
  · intro all
    exact ⟨fun i hi => by simpa [prepend,hi,inside_prefix hi] using all i (show i < w+h by omega),
      fun i hi => by simpa [prepend,show ¬w+i < w by omega,shift_join] using all (w+i) (show w+i < w+h by omega)⟩
  · rintro ⟨aok,xok⟩ i hi
    by_cases hp : i < w
    · simpa [prepend,hp,inside_prefix hp] using aok i hp
    · obtain ⟨j,rfl⟩ : ∃ j, i=w+j := ⟨i-w,by omega⟩
      simpa [prepend,show ¬w+j < w by omega,shift_join] using xok j (by omega)

theorem sumN_span (a b : Nat) (f : Nat → Nat) :
    sumN (a+b) f = sumN a f + sumN b (fun j => f (a+j)) := by
  induction b with
  | zero => simp [sumN]
  | succ b ih =>
    rw [Nat.add_succ]; simp only [sumN,ih]; omega

theorem sumN_blocks (q d : Nat) (f : Nat → Nat) :
    sumN (q*d) f = sumN q (fun i => sumN d (fun j => f (d*i+j))) := by
  induction q with
  | zero => simp [sumN]
  | succ q ih => rw [Nat.succ_mul,sumN_span,ih,Nat.mul_comm q d]; rfl

theorem length_range_filter (n : Nat) (p : Nat → Bool) :
    ((List.range n).filter p).length = sumN n (fun i => (p i).toNat) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ,List.filter_append,List.length_append,ih];
                 cases e : p n <;> simp [e,sumN]

theorem select_residue {d s : Nat} (hs : s < d) (q : Nat) (p : Nat → Bool) :
    ((List.range (q*d)).filter (fun b => (b%d==s) && p b)).length =
    ((List.range q).filter (fun i => p (d*i+s))).length := by
  rw [length_range_filter,length_range_filter,sumN_blocks]
  apply sumN_congr; intro i _
  have eq : sumN d (fun j => (((d*i+j)%d==s) && p (d*i+j)).toNat) =
      sumN d (fun j => if j=s then (p (d*i+s)).toNat else 0) := by
    apply sumN_congr; intro j hj
    rw [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hj]
    by_cases e : j=s
    · subst j; simp
    · simp [show (j==s)=false by exact beq_eq_false_iff_ne.mpr e,e]
  rw [eq,sumN_single,if_pos hs]

theorem transfer (w h : Nat) (a x : Rows) (s z : Fin (2^w)) :
    mass w (w+h) (prepend w a x) s z =
      sumN (2^w) (fun t => if closes w a t s then mass w h x t z else 0) := by
  unfold mass
  rw [show 2^(w+(w+h))=2^(w+h)*2^w by rw [← Nat.pow_add]; congr 1; omega]
  simp only [Bool.and_assoc]
  rw [select_residue s.isLt]
  simp only [shift_join,run_prepend]
  let words := List.range (2^(w+h))
  let tag := fun q : Nat => q%2^w
  rw [histogram words (2^w) tag _ (fun i _ => Nat.mod_lt _ (Nat.two_pow_pos _))]
  apply sumN_congr; intro t _
  have e : words.filter (fun q => (tag q==t) && ((((q >>> h)%2^w)==z.val) &&
        (closes w a (q%2^w) s && run w h x q))) =
      words.filter (fun q => closes w a t s && ((tag q==t) && ((((q >>> h)%2^w)==z.val) && run w h x q))) := by
    apply List.filter_congr; intro q _
    change ((tag q==t) && (_ && (closes w a (tag q) s && _))) = _
    by_cases he : tag q=t
    · simp [he,Bool.and_left_comm]
    · simp [show (tag q==t)=false from beq_eq_false_iff_ne.mpr he]
  rw [e]; by_cases ht : closes w a t s <;> simp [ht,tag,words]



def weight (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | d+1 => weight f d + f d

theorem weight_mono {f g : Nat → Nat} {d : Nat} (h : ∀ i < d, f i ≤ g i) :
    weight f d ≤ weight g d := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.add_le_add (ih (fun i hi => h i (by omega))) (h d (by omega))

theorem weight_lt {f g : Nat → Nat} {d : Nat} (h : ∀ i < d, f i ≤ g i)
    (i : Nat) (hi : i < d) (hs : f i < g i) : weight f d < weight g d := by
  induction d with
  | zero => omega
  | succ d ih =>
    simp only [weight]
    by_cases e : i = d
    · subst i
      exact Nat.add_lt_add_of_le_of_lt (weight_mono (fun i hi => h i (by omega))) hs
    · exact Nat.add_lt_add_of_lt_of_le (ih (fun i hi => h i (by omega)) (by omega))
        (h d (by omega))

theorem weight_le {f : Nat → Nat} {m d : Nat} (h : ∀ i < d, f i ≤ m) :
    weight f d ≤ d*m := by
  induction d with
  | zero => simp [weight]
  | succ d ih =>
    simpa [weight, Nat.succ_mul] using Nat.add_le_add
      (ih (fun i hi => h i (by omega))) (h d (by omega))

theorem first_le_weight (f : Nat → Nat) {d : Nat} (hd : 0 < d) : f 0 ≤ weight f d := by
  induction d with
  | zero => omega
  | succ d ih =>
    simp only [weight]
    cases d with
    | zero => simp [weight]
    | succ d => have := ih (by omega); omega

def Edge (w u v : Nat) : Prop :=
  ∃ k < w, ∃ j < 2^k, (u=j ∧ v=j+2^k) ∨ (v=j ∧ u=j+2^k)

theorem edge_symm {w u v : Nat} (h : Edge w u v) : Edge w v u := by
  obtain ⟨k,hk,j,hj,h⟩ := h
  exact ⟨k,hk,j,hj,h.symm⟩

theorem uniform {w : Nat} (f : Nat → Nat)
    (h : ∀ k < w, ∀ j < 2^k, f j = f (j+2^k)) : ∀ i < 2^w, f i = f 0 := by
  induction w with
  | zero => intro i hi; simp at hi; rw [hi]
  | succ w ih =>
    intro i hi
    have hi' := ih (fun k hk => h k (by omega))
    by_cases ha : i < 2^w
    · exact hi' i ha
    · have bound : i < 2^w + 2^w := by simpa [Nat.pow_succ, Nat.mul_two] using hi
      have hdiff : i - 2^w < 2^w := by omega
      have ht := h w (by omega) (i-2^w) hdiff
      have eq : i-2^w + 2^w = i := by omega
      rw [eq] at ht
      exact ht.symm.trans (hi' _ hdiff)

def addAt (u v : Nat) (f : Nat → Nat) (i : Nat) := if i=u then f i + f v else f i

def assemble (c : Nat) : List (Nat × Nat) → Nat → Nat
  | [] => fun _ => c
  | (u,v)::ops => addAt u v (assemble c ops)

theorem synthesize (w : Nat) (f : Nat → Nat) (hp : ∀ i < 2^w, 0 < f i) :
    ∃ c ops, 0 < c ∧ c + ops.length ≤ weight f (2^w) ∧
      (∀ uv ∈ ops, Edge w uv.1 uv.2) ∧ ∀ i < 2^w, assemble c ops i = f i := by
  classical
  by_cases hu : ∀ k < w, ∀ j < 2^k, f j = f (j+2^k)
  · have hD : 0 < 2^w := Nat.two_pow_pos _
    exact ⟨f 0, [], hp 0 hD, by simpa using first_le_weight f hD, by simp,
      fun i hi => (uniform f hu i hi).symm⟩
  · obtain ⟨k,hk⟩ := Classical.not_forall.mp hu
    obtain ⟨hk, hj⟩ := Classical.not_imp.mp hk
    obtain ⟨j,hj⟩ := Classical.not_forall.mp hj
    obtain ⟨hj, hne⟩ := Classical.not_imp.mp hj
    let l := j+2^k
    have hpow : 2^(k+1) ≤ 2^w := Nat.pow_le_pow_right (by decide) (by omega)
    have hl : l < 2^w := by dsimp [l]; rw [Nat.pow_succ,Nat.mul_two] at hpow; omega
    have hj' : j < 2^w := by dsimp [l] at hl; omega
    have ed : Edge w j l := ⟨k,hk,j,hj,Or.inl ⟨rfl,rfl⟩⟩
    have pick : ∃ u v, u < 2^w ∧ v < 2^w ∧ Edge w u v ∧ f v < f u := by
      by_cases h : f j < f l
      · exact ⟨l,j,hl,hj',edge_symm ed,h⟩
      · exact ⟨j,l,hj',hl,ed,by dsimp [l] at *; omega⟩
    obtain ⟨u,v,hu,hv,he,hlt⟩ := pick
    have huv : u ≠ v := by rintro rfl; omega
    let g := fun i => if i=u then f u - f v else f i
    have gp : ∀ i < 2^w, 0 < g i := by
      intro i hi; by_cases e : i=u
      · simp only [g,ite_eq_left e]; omega
      · simpa [g,e] using hp i hi
    have dec : weight g (2^w) < weight f (2^w) := weight_lt
      (fun i _ => by by_cases e : i=u <;> simp [g,e]) u hu (by
        have h := hp v hv; simp only [g,ite_eq_left rfl]; omega)
    obtain ⟨c,ops,hc,hlen,hed,heq⟩ := synthesize w g gp
    refine ⟨c,(u,v)::ops,hc,by simp; omega,?_,?_⟩
    · intro p h; rcases List.mem_cons.mp h with rfl|h
      · exact he
      · exact hed _ h
    · intro i hi
      simp only [assemble,addAt]
      rw [heq i hi, heq v hv]
      by_cases e : i=u
      · subst i; simp [g,Ne.symm huv]; omega
      · simp [g,e]
termination_by weight f (2^w)



theorem finInj_le {a b : Nat} (f : Fin a → Fin b) (hf : ∀ i j, f i=f j → i=j) : a ≤ b := by
  have hd : ((List.finRange a).map f).Nodup :=
    List.Pairwise.map f (fun i j hij hp => hij (hf i j hp)) (List.nodup_finRange a)
  simpa using hd.length_le_of_subset (fun x _ => List.mem_finRange x : (List.finRange a).map f ⊆ List.finRange b)

theorem message_count {X Y Z : Type} (good : X → Prop) (f : X → Y → Z)
    (K : Nat) (hk : 0 < K) (rep : Fin K → X) (hr : ∀ k, good (rep k))
    (distinct : ∀ i j, f (rep i)=f (rep j) → i=j)
    (covers : ∀ x, good x → ∃ i, f (rep i)=f x) (S : Nat) :
    (∃ (send : X → Fin S) (read : Fin S → Y → Z),
      ∀ x y, good x → read (send x) y = f x y) ↔ K ≤ S := by
  classical
  constructor
  · rintro ⟨send,read,h⟩
    apply finInj_le (fun i => send (rep i)); intro i j e
    apply distinct; funext y
    rw [← h _ y (hr i), ← h _ y (hr j), e]
  · intro hS
    let enc : X → Fin K := fun x => if h : good x then (covers x h).choose else ⟨0,hk⟩
    let dec : Fin S → Fin K := fun k => if h : k.val < K then ⟨k.val,h⟩ else ⟨0,hk⟩
    refine ⟨fun x => (enc x).castLE hS, fun i => f (rep (dec i)), ?_⟩
    intro x y hx
    have e : dec ((enc x).castLE hS) = enc x := by
      apply Fin.ext; simp [dec,(enc x).isLt]
    change f (rep (dec ((enc x).castLE hS))) y = f x y
    rw [e]
    exact congrFun (by simpa [enc,hx] using (covers x hx).choose_spec : f (rep (enc x)) = f x) y


theorem edge_bits {w u v : Nat} (e : Edge w u v) :
    u < 2^w ∧ v < 2^w ∧ u≠v ∧
      ∃ k < w, ∀ i < w, i≠k → u.testBit i = v.testBit i := by
  obtain ⟨k,hk,j,hj,h⟩ := e
  have hpow : 2^k+2^k ≤ 2^w := by simpa [Nat.pow_succ,Nat.mul_two] using
    (Nat.pow_le_pow_right (by decide : 0 < 2) (show k+1 ≤ w by omega))
  have hh (i : Nat) (hne : i≠k) : j.testBit i = (j+2^k).testBit i := by
    by_cases hi : i < k
    · rw [Nat.add_comm j,Nat.testBit_two_pow_add_gt hi]
    · have hpow' : 2^k+2^k ≤ 2^i := by simpa [Nat.pow_succ,Nat.mul_two] using
        (Nat.pow_le_pow_right (by decide : 0 < 2) (show k+1 ≤ i by omega))
      rw [Nat.testBit_lt_two_pow (show j < 2^i by omega),
        Nat.testBit_lt_two_pow (show j+2^k < 2^i by omega)]
  have hpos := Nat.two_pow_pos k
  rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨by omega,by omega,by omega,k,hk,fun i _ h => hh i h⟩
  · exact ⟨by omega,by omega,by omega,k,hk,fun i _ h => (hh i h).symm⟩

theorem sumN_mask_pair (n u v s : Nat) (hs : s < n) (hv : v < n) (hne : u≠v) (f : Nat → Nat) :
    sumN n (fun t => if s=t ∨ (s=u ∧ t=v) then f t else 0) =
      addAt u v f s := by
  have e : sumN n (fun t => if s=t ∨ (s=u ∧ t=v) then f t else 0) =
      sumN n (fun t => (if t=s then f s else 0) + (if t=v then if s=u then f v else 0 else 0)) := by
    apply sumN_congr; intro t _
    by_cases h : t=s
    · subst t; by_cases h' : s=u <;> by_cases h2 : s=v <;> simp_all [Ne.symm hne]
    · by_cases h' : t=v <;> by_cases h'' : s=u <;> simp_all [Ne.symm h,Ne.symm hne,eq_comm]
  rw [e,sumN_add,sumN_single,sumN_single]; simp [hs,hv,addAt]; split <;> simp_all

theorem prefix_add {w u v : Nat} (e : Edge w u v) :
    ∃ block : Rows, ∀ h (x : Rows) (s z : Fin (2^w)),
    mass w (w+h) (prepend w block x) s z = addAt u v (fun i => mass w h x i z) s := by
  obtain ⟨hu,hv,hne,k,hk,h⟩ := edge_bits e
  let U : Fin (2^w) := ⟨u,hu⟩; let V : Fin (2^w) := ⟨v,hv⟩
  refine ⟨gate w k u v, ?_⟩
  intro hlen x s z
  rw [transfer,← sumN_mask_pair (2^w) u v s s.isLt hv hne]
  apply sumN_congr; intro t ht
  have iff : closes w (gate w k u v) t s = true ↔ s.val=t ∨ (s.val=u ∧ t=v) := by
    simp only [closes,List.all_eq_true,List.mem_range]
    simpa [Fin.ext_iff,U,V] using (gate_iff hk U V s ⟨t,ht⟩ h)
  by_cases he : s.val=t ∨ (s.val=u ∧ t=v)
  · simp [he,iff.mpr he]
  · have hfalse := Bool.eq_false_iff.mpr (fun hp => he (iff.mp hp))
    simp [he,hfalse]

theorem apply_left {w : Nat} (ops : List (Nat × Nat)) (he : ∀ uv∈ops, Edge w uv.1 uv.2)
    (c h : Nat) (x : Rows) (f : Nat → Nat) (hx : ∀ s z : Fin (2^w), mass w h x s z = c*f z) :
    ∃ y : Rows, ∀ s z : Fin (2^w), mass w (ops.length*w+h) y s z = (assemble c ops s)*f z := by
  induction ops with
  | nil => simpa [assemble] using (show ∃ x' : Rows, ∀ s z : Fin (2^w), mass w h x' s z = c * f z from ⟨x,hx⟩)
  | cons uv ops ih =>
    obtain ⟨u,v⟩ := uv
    obtain ⟨r,hr⟩ := ih (fun uv hu => he uv (List.mem_cons_of_mem _ hu))
    have e := he (u,v) (List.mem_cons_self ..)
    obtain ⟨blk,hb⟩ := prefix_add e
    obtain ⟨_,hv,_,_⟩ := edge_bits e
    refine ⟨prepend w blk r,?_⟩
    intro s z
    rw [show ((u,v)::ops).length * w+h = w+(ops.length*w+h) by simp [Nat.succ_mul]; omega,hb]
    simp only [assemble,addAt]
    rw [hr s z,hr (⟨v,hv⟩ : Fin _) z]
    split <;> simp [Nat.add_mul]
def weighted (w h : Nat) (x : Rows) (f : Nat → Nat) (z : Nat) :=
  sumN (2^w) (fun i => f i * mass w h x i z)

theorem contraction {n u v : Nat} (hu : u < n) (hv : v < n) (f g : Nat → Nat) :
    sumN n (fun i => f i * addAt u v g i) = sumN n (fun i => addAt v u f i * g i) := by
  have lhs : sumN n (fun i => f i * addAt u v g i) = sumN n (fun i => f i*g i) + f u*g v := by
    have e : sumN n (fun i => f i * addAt u v g i) =
        sumN n (fun i => f i * g i + (if i=u then f u*g v else 0)) := by
      apply sumN_congr; intro i _; by_cases hi : i=u <;> simp [addAt,hi,Nat.mul_add]
    rw [e,sumN_add,sumN_single]; simp [hu]
  rw [lhs]
  have e : sumN n (fun i => addAt v u f i *g i) =
      sumN n (fun i => f i*g i + (if i=v then f u*g v else 0)) := by
    apply sumN_congr; intro i _; by_cases hi : i=v <;> simp [addAt,hi,Nat.add_mul]
  rw [e,sumN_add,sumN_single]; simp [hv]

theorem apply_right {w : Nat} (ops : List (Nat × Nat)) (he : ∀ uv∈ops, Edge w uv.1 uv.2)
    (c h : Nat) (x : Rows) :
    ∃ y : Rows, ∀ z : Fin (2^w),
    weighted w (ops.length*w+h) y (fun _ => c) z = weighted w h x (assemble c ops) z := by
  induction ops generalizing h x with
  | nil => exact ⟨x,by intro z; simp [assemble]⟩
  | cons e ops ih =>
    obtain ⟨u,v⟩ := e
    have edge := edge_symm (he (u,v) (List.mem_cons_self ..))
    obtain ⟨hv,hu,_⟩ := edge_bits edge
    obtain ⟨blk,hb⟩ := prefix_add edge
    obtain ⟨y,hy⟩ := ih (fun uv h => he uv (List.mem_cons_of_mem _ h)) (w+h) (prepend w blk x)
    refine ⟨y,?_⟩; intro z
    rw [show ((u,v)::ops).length*w+h = ops.length*w+(w+h) by simp [Nat.succ_mul,Nat.add_assoc],hy]
    unfold weighted; simp only [assemble]
    rw [← contraction hv hu]
    apply sumN_congr; intro i hi
    rw [hb _ x (⟨i,hi⟩ : Fin _) z]

theorem mass_empty (w : Nat) (x : Rows) (s z : Fin (2^w)) :
    mass w 0 x s z = if s=z then 1 else 0 := by
  simp only [mass,run,List.range_zero,List.all_nil,Bool.and_true,Nat.add_zero,Nat.shiftRight_zero]
  rw [length_range_filter]
  have e : sumN (2^w) (fun i => ((i%2^w==s.val) && (i%2^w==z.val)).toNat) =
    sumN (2^w) (fun i => if i=s.val then if s=z then 1 else 0 else 0) := by
    apply sumN_congr; intro i hi
    rw [Nat.mod_eq_of_lt hi]; by_cases eq : i=s.val
    · subst i; by_cases g : s=z
      · simp [g]
      · have ne : s.val≠z.val := fun h => g (Fin.ext h)
        simp [g,beq_eq_false_iff_ne.mpr ne]
    · simp [eq,beq_eq_false_iff_ne.mpr eq]
  rw [e,sumN_single]; simp [s.isLt]

theorem weighted_empty (w : Nat) (x : Rows) (f : Nat → Nat) (z : Fin (2^w)) :
    weighted w 0 x f z = f z := by
  unfold weighted
  have e : sumN (2^w) (fun i => f i * mass w 0 x i z) =
      sumN (2^w) (fun i => if i=z.val then f i else 0) := by
    apply sumN_congr; intro i hi
    rw [mass_empty _ _ (⟨i,hi⟩ : Fin _) z]; by_cases h : i=z.val <;> simp [Fin.ext_iff,h]
  rw [e]; have e' : sumN (2^w) (fun i => if i=z.val then f i else 0) =
      sumN (2^w) (fun i => if i=z.val then f z else 0) := by
    apply sumN_congr; intro i _; by_cases h : i=z.val <;> simp [h]
  rw [e',sumN_single]; simp [z.isLt]

theorem right_vector (w : Nat) (b : Nat → Nat) (hb : ∀ i < 2^w, 0 < b i) :
    ∃ (d k : Nat) (y : Rows), 0 < d ∧ d+k ≤ weight b (2^w) ∧
      ∀ z : Fin (2^w), weighted w (k*w) y (fun _ => d) z = b z := by
  obtain ⟨d,ops,hd,hk,he,hv⟩ := synthesize w b hb
  obtain ⟨y,hy⟩ := apply_right ops he d 0 (fun _ _ => false)
  exact ⟨d,ops.length,y,hd,hk,fun z => by simpa [weighted_empty,hv z z.isLt] using hy z⟩

def zeroStep (x : Rows) : Rows := fun i p => if i=0 then p==0 else x (i-1) p
theorem run_hold (w h : Nat) (x : Rows) (b : Nat) :
    run w (1+h) (zeroStep x) b = ((b%(2*2^w)==0) && run w h x (b >>> 1)) := by
  apply Bool.eq_iff_iff.mpr; simp only [run,List.all_eq_true,List.mem_range,Bool.and_eq_true]
  constructor
  · intro all
    constructor
    · simpa [zeroStep] using all 0 (by omega)
    · intro i hi
      simpa [zeroStep,show 1+i≠0 by omega,Nat.shiftRight_add] using all (1+i) (by omega)
  · rintro ⟨a,f⟩ i hi
    cases i with
    | zero => simpa [zeroStep] using a
    | succ i => simpa [zeroStep,show i+1=1+i by omega,Nat.shiftRight_add] using f i (by omega)

theorem pad_one (w h : Nat) (x : Rows) (z : Nat) :
    mass w (1+h) (zeroStep x) 0 z = mass w h x 0 z := by
  unfold mass
  rw [show 2^(w+(1+h))=2^(w+h)*2 by rw [← Nat.pow_succ]; congr 1; omega]
  simp only [run_hold,Nat.shiftRight_add]
  let n := 2^(w+h)
  let pred := fun b : Nat => (b%(2*2^w)==0) && ((((b>>>1>>>h)%2^w)==z) && run w h x (b>>>1))
  have eq : (List.range (n*2)).filter (fun b => (b%2^w==0) && (((b>>>1>>>h)%2^w)==z) &&
      ((b%(2*2^w)==0) && run w h x (b>>>1))) =
      (List.range (n*2)).filter (fun b => (b%2==0) && pred b) := by
    apply List.filter_congr; intro b _
    apply Bool.eq_iff_iff.mpr
    simp only [pred,Bool.and_eq_true,beq_iff_eq]
    constructor
    · rintro ⟨⟨_,hz⟩,hp,hr⟩
      exact ⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_right ..) (Nat.dvd_of_mod_eq_zero hp)),hp,hz,hr⟩
    · rintro ⟨_,hp,hz,hr⟩
      exact ⟨⟨Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_left ..) (Nat.dvd_of_mod_eq_zero hp)),hz⟩,hp,hr⟩
  rw [eq,select_residue (s:=0) (d:=2) (by decide)]
  congr 1; apply List.filter_congr; intro q _
  have shq : (2*q) >>> 1 = q := by simp [Nat.shiftRight_eq_div_pow]
  apply Bool.eq_iff_iff.mpr; simp [pred,shq,Nat.mul_mod_mul_left,Bool.and_assoc] <;> omega

theorem pad (w h r : Nat) (x : Rows) :
    ∃ y : Rows, ∀ z, mass w (r+h) y 0 z = mass w h x 0 z := by
  induction r with
  | zero => exact ⟨x,by simp⟩
  | succ r ih => obtain ⟨y,hy⟩ := ih; exact ⟨zeroStep y, fun z => by
                   rw [show r+1+h=1+(r+h) by omega,pad_one,hy]⟩

def checkOpt (a : Option Nat) (i : Nat) (sample : Bool) :=
  match a with
  | none => true
  | some v => sample == v.testBit i

def matchOpt (a : Option (Fin n)) (s : Nat) : Bool :=
  match a with
  | none => true
  | some v => s==v.val

def sel (w : Nat) (a b : Option (Fin (2^w))) : Rows := fun i p =>
  checkOpt (a.map Fin.val) i (p.testBit 0) && checkOpt (b.map Fin.val) i (p.testBit w)

theorem opt_all (v : Option (Fin (2^w))) (s : Fin (2^w)) :
    (∀ i < w, checkOpt (v.map Fin.val) i (s.val.testBit i) = true) ↔ matchOpt v s = true := by
  cases v with
  | none => simp [checkOpt,matchOpt]
  | some v =>
    simp only [Option.map_some,checkOpt,matchOpt,beq_iff_eq]
    constructor
    · intro h; exact congrArg Fin.val (eq_of_low_bits h)
    · intro h i _; rw [h]

theorem sel_close (w : Nat) (a b : Option (Fin (2^w))) (s t : Fin (2^w)) :
    closes w (sel w a b) t s = (matchOpt a s && matchOpt b t) := by
  apply Bool.eq_iff_iff.mpr
  simp only [closes,List.all_eq_true,List.mem_range,Bool.and_eq_true]
  rw [← opt_all a s,← opt_all b t]
  constructor
  · intro h
    constructor <;> intro i hi <;> have hp := h i hi <;>
      simp only [sel,(close_lohi hi _ _).1,(close_lohi hi _ _).2,Bool.and_eq_true] at hp
    · exact hp.1
    · exact hp.2
  · rintro ⟨ha,hb⟩ i hi
    simp [sel,(close_lohi hi _ _).1,(close_lohi hi _ _).2,ha i hi,hb i hi]

theorem sel_point (w h : Nat) (a : Option (Fin (2^w))) (t : Fin (2^w)) (x : Rows) (s z : Fin (2^w)) :
    mass w (w+h) (prepend w (sel w a (some t)) x) s z =
      if matchOpt a s then mass w h x t z else 0 := by
  rw [transfer]
  have e : sumN (2^w) (fun q => if closes w (sel w a (some t)) q s then mass w h x q z else 0)
      = sumN (2^w) (fun q => if q=t.val then if matchOpt a s then mass w h x t z else 0 else 0) := by
    apply sumN_congr; intro q hq
    rw [sel_close w a (some t) s (⟨q,hq⟩ : Fin _)]
    by_cases h : q=t.val
    · subst q; cases a <;> simp [matchOpt]
    · simp [matchOpt,show (q==t.val)=false from beq_eq_false_iff_ne.mpr h,h]
  rw [e,sumN_single]; simp [t.isLt]

theorem sel_fan (w h : Nat) (a : Fin (2^w)) (x : Rows) (s z : Fin (2^w)) :
    mass w (w+h) (prepend w (sel w (some a) none) x) s z =
    if s=a then sumN (2^w) (fun i => mass w h x i z) else 0 := by
  rw [transfer]; by_cases hsa : s=a
  · simp only [hsa,ite_true]; apply sumN_congr; intro i hi
    rw [sel_close w (some a) none a (⟨i,hi⟩ : Fin _)]
    simp [matchOpt]
  · simp only [ite_eq_right hsa]
    apply Eq.trans (b := sumN (2^w) (fun _ => 0))
    · apply sumN_congr; intro i hi
      rw [sel_close w (some a) none s (⟨i,hi⟩ : Fin _)]
      simp [matchOpt,show (s.val==a.val)=false from beq_eq_false_iff_ne.mpr (fun hh => hsa (Fin.ext hh))]
    · exact sumN_zero _

theorem accumulate {w : Nat} (hw : 0 < w) (k h : Nat) (x : Rows) (F : Nat → Nat)
    (hx0 : ∀ z : Fin (2^w), mass w h x 0 z = 0)
    (hx1 : ∀ z : Fin (2^w), mass w h x 1 z = F z) :
    ∃ y : Rows, ∀ z : Fin (2^w), mass w (k*w+h) y 0 z = k*F z ∧
      mass w (k*w+h) y 1 z = F z := by
  have e : Edge w 0 1 := ⟨0,hw,0,by decide,Or.inl ⟨rfl,rfl⟩⟩
  obtain ⟨h0,h1,_⟩ := edge_bits e
  have A : Fin (2^w) := ⟨0,h0⟩
  obtain ⟨block,hb⟩ := prefix_add e
  induction k with
  | zero => exact ⟨x,fun z => by simp [hx0,hx1]⟩
  | succ k ih =>
    obtain ⟨y,hy⟩ := ih
    refine ⟨prepend w block y,fun z => ?_⟩
    rw [Nat.succ_mul,show k*w+w+h=w+(k*w+h) by omega]
    rw [hb _ y (⟨0,h0⟩ : Fin _) z,hb _ y (⟨1,h1⟩ : Fin _) z]
    simp [addAt,(hy z).1,(hy z).2,Nat.succ_mul]

theorem mul_sumN (n k : Nat) (F : Nat → Nat) :
    k*sumN n F = sumN n (fun i => k*F i) := by
  induction n with
  | zero => simp [sumN]
  | succ n ih => simp [sumN,Nat.mul_add,ih]

theorem realize_nat (w m L : Nat) (hw : 0 < w) (budget : 18*w*2^w*m+3*w ≤ L)
    (a b : Nat → Nat)
    (ha : ∀ i < 2^w, 0 < a i) (hma : ∀ i < 2^w, a i ≤ m)
    (hb : ∀ i < 2^w, 0 < b i) (hmb : ∀ i < 2^w, b i ≤ m) :
    ∃ x : Rows, ∀ s z : Fin (2^w), mass w L x s z = a s * b z := by
  obtain ⟨c,ops,_,hops,edges,rep⟩ := synthesize w a ha
  obtain ⟨d,k,y,_,hk,hy⟩ := right_vector w b hb
  have wpos : 1 < 2^w := by have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ w by omega); exact this
  let O : Fin (2^w) := ⟨0,by omega⟩
  let I : Fin (2^w) := ⟨1,wpos⟩
  let h₀ := k*w
  let F := fun z : Nat => sumN (2^w) (fun i => mass w h₀ y i z)
  have db (z : Fin (2^w)) : d*F z = b z := by
    simpa only [F,h₀,mul_sumN,weighted] using hy z
  let y₁ := prepend w (sel w (some I) none) y
  let h₁ := w+h₀
  have y₁O (z : Fin (2^w)) : mass w h₁ y₁ 0 z = 0 := by
    have hh := sel_fan w h₀ I y O z
    simpa [h₁,y₁,O,I,Fin.ext_iff] using hh
  have y₁I (z : Fin (2^w)) : mass w h₁ y₁ 1 z = F z := by
    simpa [h₁,y₁,I,F] using sel_fan w h₀ I y I z
  obtain ⟨y₂,hy₂⟩ := accumulate hw d h₁ y₁ F y₁O y₁I
  let h₂ := d*w+h₁
  let h₃ := w+h₂
  let y₃ := prepend w (sel w (some I) (some O)) y₂
  have y₃O (z : Fin (2^w)) : mass w h₃ y₃ 0 z = 0 := by
    simpa [h₃,y₃,O,I,matchOpt] using sel_point w h₂ (some I) O y₂ O z
  have y₃I (z : Fin (2^w)) : mass w h₃ y₃ 1 z = b z := by
    have hh : mass w h₂ y₂ O z = b z := ((hy₂ z).1).trans (db z)
    simpa [h₃,y₃,O,I,matchOpt] using (sel_point w h₂ (some I) O y₂ I z).trans
      (by simpa [I,matchOpt] using hh : _ = b z)
  obtain ⟨y₄,hy₄⟩ := accumulate hw c h₃ y₃ b y₃O y₃I
  let h₄ := c*w+h₃
  let total := ops.length*w+(w+h₄)
  have hnum : (ops.length+c)+(d+k) ≤ (2^w*m)+(2^w*m) := by
    have aa := weight_le hma; have bb := weight_le hmb; omega
  have hl : total ≤ L := by
    have e : total = ((ops.length+c)+(d+k))*w + 3*w := by
      simp only [total,h₄,h₃,h₂,h₁,h₀,Nat.add_mul]; omega
    rw [e]
    have z := Nat.mul_le_mul_right w hnum
    have eq : (2^w*m+2^w*m)*w = (w*2^w*m)+(w*2^w*m) := by rw [Nat.add_mul]; ac_rfl
    rw [eq] at z; rw [show 18*w*2^w*m=18*(w*2^w*m) by ac_rfl] at budget; omega
  let r := L-total
  obtain ⟨yp,hp⟩ := pad w h₄ r y₄
  let y₅ := prepend w (sel w none (some O)) yp
  have h₅ (s z : Fin (2^w)) : mass w (w+(r+h₄)) y₅ s z = c*b z := by
    rw [show y₅=prepend w (sel w none (some O)) yp by rfl,sel_point]
    simp only [matchOpt,ite_true]
    exact (hp z).trans (hy₄ z).1
  obtain ⟨final,hfinal⟩ := apply_left ops edges c _ y₅ b h₅
  refine ⟨final,?_⟩; intro s z
  have e : ops.length*w+(w+(r+h₄)) = L := by dsimp only [r,total] at *; omega
  simpa only [e,rep s s.isLt] using hfinal s z

theorem realize (w m L : Nat) (hw : 0 < w) (hl : 18*w*2^w*m+3*w ≤ L)
    (a b : Fin (2^w) → Nat)
    (ha : ∀ i, 0 < a i) (hma : ∀ i, a i ≤ m) (hb : ∀ i, 0 < b i) (hmb : ∀ i, b i ≤ m) :
    ∃ x : Rows, ∀ s z : Fin (2^w), mass w L x s z = a s * b z := by
  let A := fun i : Nat => if h : i < 2^w then a ⟨i,h⟩ else 1
  let B := fun i : Nat => if h : i < 2^w then b ⟨i,h⟩ else 1
  obtain ⟨x,hx⟩ := realize_nat w m L hw hl A B
    (fun i hi => by simpa [A,hi] using ha ⟨i,hi⟩) (fun i hi => by simpa [A,hi] using hma ⟨i,hi⟩)
    (fun i hi => by simpa [B,hi] using hb ⟨i,hi⟩) (fun i hi => by simpa [B,hi] using hmb ⟨i,hi⟩)
  exact ⟨x,fun s z => by simpa [A,B,s.isLt,z.isLt] using hx s z⟩



abbrev Matrix (d : Nat) := Fin d → Fin d → Nat
def sig (w m L : Nat) (x : Rows) : Matrix (2^w) := fun s z => mass w L x s z % m
def good (w L : Nat) (x : Rows) := ∃ a b : Fin (2^w) → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
    ∀ s z : Fin (2^w), mass w L x s.val z.val = a s * b z
def out (d m : Nat) (a b : Fin d → Fin m) : Matrix d :=
  fun s z => (a s).val*(b z).val % m
def isOuter (d m : Nat) (M : Matrix d) := ∃ a b : Fin d → Fin m, out d m a b = M

def liftPos (m : Nat) (r : Fin m) := if r.val=0 then m else r.val
theorem liftfacts (m : Nat) (r : Fin m) : 0 < liftPos m r ∧ liftPos m r ≤ m ∧ liftPos m r % m = r.val := by
  have := r.isLt; by_cases h : r.val=0
  · simp [liftPos,h]; omega
  · simp [liftPos,h,Nat.mod_eq_of_lt r.isLt]; omega

theorem image_exact (w m L : Nat) (hw : 0 < w) (hm : 2 ≤ m) (hl : 18*w*2^w*m+3*w ≤ L)
    (M : Matrix (2^w)) :
    (∃ x : Rows, good w L x ∧ sig w m L x = M) ↔ isOuter (2^w) m M := by
  constructor
  · rintro ⟨x,⟨a,b,_,_,h⟩,rfl⟩
    refine ⟨fun s => ⟨a s % m, Nat.mod_lt _ (by omega)⟩,
      fun z => ⟨b z % m, Nat.mod_lt _ (by omega)⟩, ?_⟩
    funext s z
    simp only [out,sig,h]; rw [← Nat.mul_mod]
  · rintro ⟨a,b,rfl⟩
    let A := fun s => liftPos m (a s); let B := fun z => liftPos m (b z)
    obtain ⟨x,h⟩ := realize w m L hw hl A B (fun s => (liftfacts m (a s)).1)
      (fun s => (liftfacts m (a s)).2.1) (fun z => (liftfacts m (b z)).1)
      (fun z => (liftfacts m (b z)).2.1)
    refine ⟨x,⟨A,B,fun s => (liftfacts m (a s)).1, fun z => (liftfacts m (b z)).1,h⟩,?_⟩
    funext s z
    simp only [sig,h,out]; rw [Nat.mul_mod,(liftfacts m (a s)).2.2,(liftfacts m (b z)).2.2]

def OuterCard (d m K : Nat) := ∃ R : Fin K → Matrix d,
  (∀ i j, R i=R j → i=j) ∧ (∀ M, (∃ i, R i=M) ↔ isOuter d m M)

theorem msg_of_outerCard (w m L : Nat) (hw : 0 < w) (hm : 2 ≤ m) (hl : 18*w*2^w*m+3*w ≤ L)
    (K : Nat) (hK : OuterCard (2^w) m K) (S : Nat) :
    (∃ (send : Rows → Fin S) (read : Fin S → Rows → Nat),
      ∀ x y : Rows, good w L x → read (send x) y = count w m L x y) ↔ K ≤ S := by
  classical
  obtain ⟨R,hinj,hcov⟩ := hK
  have hx (i : Fin K) : ∃ x : Rows, good w L x ∧ sig w m L x = R i :=
    (image_exact w m L hw hm hl _).mpr ((hcov _).mp ⟨i,rfl⟩)
  let X := fun i => (hx i).choose
  have hpos : 0 < K := by
    let z : Fin (2^w) → Fin m := fun _ => ⟨0,by omega⟩
    obtain ⟨i,_⟩ := (hcov _).mpr (show isOuter (2^w) m (out (2^w) m z z) from ⟨z,z,rfl⟩)
    have := i.isLt; omega
  apply message_count (good w L) (count w m L) K hpos X (fun i => (hx i).choose_spec.1)
  · intro i j h; apply hinj
    rw [← (hx i).choose_spec.2,← (hx j).choose_spec.2]
    funext s z; exact (signature_complete _ _ _ _ _).mp (fun y => congrFun h y) s z
  · intro x h
    obtain ⟨i,hi⟩ := (hcov (sig w m L x)).mpr ((image_exact _ _ _ hw hm hl _).mp ⟨x,h,rfl⟩)
    refine ⟨i,?_⟩; funext y; apply (signature_complete _ _ _ _ _).mpr _ y
    intro s z
    exact congrFun (congrFun ((hx i).choose_spec.2.trans hi) s) z


def primitive {d n : Nat} [NeZero n] (v : Fin d → Fin n) :=
  ∃ i c, c * v i = 1

def scalarRel {d n : Nat} [NeZero n] (a b a' b' : Fin d → Fin n) (u : Fin n) :=
  ∃ v : Fin n, u*v=1 ∧ (∀ i, a' i = u*a i) ∧ (∀ j, b' j = v*b j)

theorem fin_leftcomm {n : Nat} (i j k : Fin n) : i*(j*k)=j*(i*k) := by
  rw [← Fin.mul_assoc,Fin.mul_comm i j,Fin.mul_assoc]

theorem primitive_fiber {d n : Nat} [NeZero n] (a b a' b' : Fin d → Fin n)
    (ha : primitive a) (hb : primitive b) (h : ∀ i j, a i*b j = a' i*b' j) :
    ∃ u : Fin n, scalarRel a b a' b' u ∧ ∀ w, scalarRel a b a' b' w → w=u := by
  obtain ⟨i,A,hA⟩ := ha
  obtain ⟨j,B,hB⟩ := hb
  let u := A * a' i; let v := B * b' j
  have ub (t : Fin d) : u * b' t = b t := by
    dsimp [u]; rw [Fin.mul_assoc,← h i t,← Fin.mul_assoc,hA,Fin.one_mul]
  have va (s : Fin d) : v * a' s = a s := by
    dsimp [v]
    rw [Fin.mul_assoc,Fin.mul_comm (b' j),← h s j,Fin.mul_comm (a s),← Fin.mul_assoc,hB,Fin.one_mul]
  have huv : u*v=1 := by dsimp [v]; rw [fin_leftcomm,ub,hB]
  refine ⟨u,⟨v,huv,?_,?_⟩,?_⟩
  · intro s; rw [← va s,← Fin.mul_assoc,huv,Fin.one_mul]
  · intro t; rw [← ub t,← Fin.mul_assoc,Fin.mul_comm v,huv,Fin.one_mul]
  · rintro w ⟨_,_,hw,_⟩
    calc w = w*(A*a i) := by rw [hA,Fin.mul_one]
         _ = A*(w*a i) := fin_leftcomm ..
         _ = u := by rw [← hw i]

theorem scalarRel_outer {d n : Nat} [NeZero n] {a b a' b' : Fin d → Fin n}
    {u : Fin n} (h : scalarRel a b a' b' u) : ∀ i j, a i*b j = a' i*b' j := by
  obtain ⟨v,e,ha,hb⟩ := h
  intro i j; rw [ha,hb,Fin.mul_assoc u,fin_leftcomm (a i) v,← Fin.mul_assoc u v,e,Fin.one_mul]

theorem rescale_primitive {d n : Nat} [NeZero n] {a : Fin d → Fin n} {u v : Fin n}
    (ha : primitive a) (e : u*v=1) : primitive (fun i => u*a i) := by
  obtain ⟨i,A,hA⟩ := ha; refine ⟨i,A*v,?_⟩
  rw [Fin.mul_assoc,← Fin.mul_assoc v u,Fin.mul_comm v u,e,Fin.one_mul,hA]
abbrev UnitRes (n : Nat) [NeZero n] := {u : Fin n // ∃ v : Fin n, u*v=1}
abbrev Vec (d n : Nat) := Fin d → Fin n
abbrev Pair (d n : Nat) := Vec d n × Vec d n
def entryMap {d n : Nat} (x : Pair d n) := fun i j => x.1 i * x.2 j
def goodPair {d n : Nat} [NeZero n] (x : Pair d n) := primitive x.1 ∧ primitive x.2
abbrev PrimPair (d n : Nat) [NeZero n] := {x : Pair d n // goodPair x}
abbrev PrimImage (d n : Nat) [NeZero n] := {M : Fin d → Fin d → Fin n //
  ∃ x : PrimPair d n, entryMap x.val = M}

theorem inv_unique {n : Nat} [NeZero n] {u v v' : Fin n} (h : u*v=1) (h' : u*v'=1) : v=v' := by
  calc v = v*(u*v') := by rw [h',Fin.mul_one]
       _ = (u*v)*v' := by rw [← Fin.mul_assoc,Fin.mul_comm v u]
       _ = v' := by rw [h,Fin.one_mul]

noncomputable def act {d n : Nat} [NeZero n] (u : UnitRes n) (x : PrimPair d n) : PrimPair d n :=
  ⟨⟨fun i => u.val*x.val.1 i,fun j => u.property.choose*x.val.2 j⟩,
   rescale_primitive x.property.1 u.property.choose_spec,
   rescale_primitive x.property.2 ((Fin.mul_comm ..).trans u.property.choose_spec)⟩

theorem act_rel {d n : Nat} [NeZero n] (u : UnitRes n) (x : PrimPair d n) :
    scalarRel x.val.1 x.val.2 (act u x).val.1 (act u x).val.2 u :=
  ⟨_,u.property.choose_spec,fun _ => rfl,fun _ => rfl⟩

theorem act_preserves {d n : Nat} [NeZero n] (u : UnitRes n) (x : PrimPair d n) :
    entryMap (act u x).val = entryMap x.val := by
  funext i j; exact (scalarRel_outer (act_rel u x) i j).symm

theorem act_unique {d n : Nat} [NeZero n] (x x' : PrimPair d n)
    (h : entryMap x.val = entryMap x'.val) :
    ∃ u : UnitRes n, act u x=x' ∧ ∀ v, act v x=x' → v=u := by
  obtain ⟨u,⟨v,hv,ha,hb⟩,unique⟩ := primitive_fiber x.val.1 x.val.2 x'.val.1 x'.val.2
    x.property.1 x.property.2 (fun i j => congrFun (congrFun h i) j)
  let U : UnitRes n := ⟨u,v,hv⟩
  refine ⟨U,?_,?_⟩
  · apply Subtype.ext
    apply Prod.ext
    · funext i; exact (ha i).symm
    · funext j
      change U.property.choose * x.val.2 j = _
      rw [inv_unique U.property.choose_spec hv,← hb j]
  · intro V e
    apply Subtype.ext; apply unique
    rw [← e]
    exact act_rel V x

theorem primitive_atlas (d n : Nat) [NeZero n] :
    ∃ decode : PrimImage d n × UnitRes n → PrimPair d n,
      Function.Injective decode ∧ Function.Surjective decode := by
  classical
  let base := fun M : PrimImage d n => M.property.choose
  have hbase (M : PrimImage d n) : entryMap (base M).val = M.val := M.property.choose_spec
  let dec := fun p : PrimImage d n × UnitRes n => act p.2 (base p.1)
  have key (M : PrimImage d n) (u : UnitRes n) : entryMap (dec (M,u)).val = M.val :=
    (act_preserves u (base M)).trans (hbase M)
  refine ⟨dec,?_,?_⟩
  · rintro ⟨M,u⟩ ⟨N,v⟩ he
    have hMN : M=N := Subtype.ext ((key M u).symm.trans ((congrArg (fun t : PrimPair d n => entryMap t.val) he).trans (key N v)))
    subst N
    obtain ⟨t,_,uniq⟩ := act_unique (base M) (dec (M,v)) ((hbase M).trans (key M v).symm)
    have huv : u=v := (uniq u he).trans (uniq v rfl).symm
    rw [huv]
  · intro x
    let M : PrimImage d n := ⟨entryMap x.val,x,rfl⟩
    obtain ⟨u,hu,_⟩ := act_unique (base M) x (hbase M)
    exact ⟨(M,u),hu⟩


abbrev Img (d n : Nat) := {M : Matrix d // isOuter d n M}

theorem crt_images (d n n₁ n₂ : Nat) (f : Fin n → Fin n₁ × Fin n₂)
    (hf : Function.Injective f) (sur : Function.Surjective f)
    (mul : ∀ a b, f (a*b) = ((f a).1*(f b).1,(f a).2*(f b).2)) :
    ∃ split : Img d n → Img d n₁ × Img d n₂, Function.Injective split ∧ Function.Surjective split := by
  classical
  have has (X : Img d n) (i j : Fin d) : X.val i j < n := by
    obtain ⟨a,b,e⟩ := X.property
    rw [← e]; exact (a i * b j).isLt
  let cell := fun (X : Img d n) (i j : Fin d) => (⟨X.val i j,has X i j⟩ : Fin n)
  have fc (X : Img d n) (a b : Fin d → Fin n) (e : out d n a b = X.val) (i j : Fin d) :
      f (cell X i j) = ((f (a i)).1*(f (b j)).1,(f (a i)).2*(f (b j)).2) := by
    have eq : cell X i j = a i*b j := Fin.ext (congrFun (congrFun e.symm i) j)
    rw [eq,mul]
  let M1 := fun (X : Img d n) i j => (f (cell X i j)).1.val
  let M2 := fun (X : Img d n) i j => (f (cell X i j)).2.val
  have h1 (X : Img d n) : isOuter d n₁ (M1 X) := by
    obtain ⟨a,b,e⟩ := X.property
    refine ⟨fun i => (f (a i)).1,fun j => (f (b j)).1,?_⟩
    funext i j
    exact congrArg (fun x : Fin n₁ × Fin n₂ => x.1.val) (fc X a b e i j).symm
  have h2 (X : Img d n) : isOuter d n₂ (M2 X) := by
    obtain ⟨a,b,e⟩ := X.property
    refine ⟨fun i => (f (a i)).2,fun j => (f (b j)).2,?_⟩
    funext i j
    exact congrArg (fun x : Fin n₁ × Fin n₂ => x.2.val) (fc X a b e i j).symm
  let split := fun X : Img d n => ((⟨M1 X,h1 X⟩ : Img d n₁), (⟨M2 X,h2 X⟩ : Img d n₂))
  refine ⟨split,?_,?_⟩
  · intro X Y h
    apply Subtype.ext; funext i j
    apply congrArg Fin.val (hf (a₁ := cell X i j) (a₂ := cell Y i j) _)
    apply Prod.ext
    · apply Fin.ext; exact congrArg (fun p : Img d n₁ × Img d n₂ => p.1.val i j) h
    · apply Fin.ext; exact congrArg (fun p : Img d n₁ × Img d n₂ => p.2.val i j) h
  · rintro ⟨M,N⟩
    obtain ⟨a,b,hab⟩ := M.property
    obtain ⟨c,e,hce⟩ := N.property
    let A := fun i => (sur (a i,c i)).choose
    let B := fun j => (sur (b j,e j)).choose
    let X : Img d n := ⟨out d n A B,A,B,rfl⟩
    have ff (i j : Fin d) : f (cell X i j) = (a i*b j,c i*e j) := by
      rw [fc X A B rfl i j,(sur (a i,c i)).choose_spec,(sur (b j,e j)).choose_spec]
    refine ⟨X,Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
    · funext i j; exact (congrArg (fun p : Fin n₁ × Fin n₂ => p.1.val) (ff i j)).trans
        (congrFun (congrFun hab i) j)
    · funext i j; exact (congrArg (fun p : Fin n₁ × Fin n₂ => p.2.val) (ff i j)).trans
        (congrFun (congrFun hce i) j)


theorem stripVector (p : Nat) (hp : 1 < p) (k : Nat) (x : ι → Nat)
    (bound : ∀ i, x i < p^k) (nonzero : ∃ i, x i≠0) :
    ∃ r < k, ∃ y : ι → Nat, (∀ i, x i = p^r * y i) ∧
      (∀ i, y i < p^(k-r)) ∧ ∃ i, ¬p ∣ y i := by
  classical
  induction k generalizing x with
  | zero =>
    obtain ⟨i,hi⟩ := nonzero
    have h := bound i; simp at h; contradiction
  | succ k ih =>
    by_cases hd : ∀ i, p ∣ x i
    · let y := fun i => x i / p
      have eq (i : _) : p*y i=x i := Nat.mul_div_cancel' (hd i)
      have by' (i : _) : y i < p^k := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mpr
        simpa [Nat.pow_succ] using bound i
      obtain ⟨i,hn⟩ := nonzero
      have hn' : y i≠0 := fun h => hn (by rw [←eq i,h,Nat.mul_zero])
      obtain ⟨r,hr,z,hz,bz,one⟩ := ih y by' ⟨i,hn'⟩
      refine ⟨r+1,by omega,z,?_,?_,one⟩
      · intro j; rw [←eq j,hz j,Nat.pow_succ]; ac_rfl
      · simpa using bz
    · refine ⟨0,by omega,x,by simp,by simpa using bound,Classical.not_forall.mp hd⟩

theorem strata_mul_mod (p r s j a b : Nat) :
    ((p^r*a)*(p^s*b)) % p^(r+s+j) = p^(r+s) * ((a*b)%p^j) := by
  have e : (p^r*a)*(p^s*b) = p^(r+s)*(a*b) := by rw [Nat.pow_add]; ac_rfl
  rw [e,Nat.pow_add p (r+s) j,Nat.mul_mod_mul_left]

theorem invisible_product (p r s k a b : Nat) (h : k ≤ r+s) :
    ((p^r*a)*(p^s*b)) % p^k = 0 := by
  apply Nat.mod_eq_zero_of_dvd
  apply Nat.dvd_trans (Nat.pow_dvd_pow p h)
  refine ⟨a*b,?_⟩; rw [Nat.pow_add]; ac_rfl

theorem strip_mod_unit (p j a : Nat) (hj : 0 < j) : p ∣ a % p^j ↔ p ∣ a :=
  Nat.dvd_mod_iff (by simpa using Nat.pow_dvd_pow p (show 1 ≤ j by omega))

theorem scale_eq_iff {p r : Nat} (hp : 0 < p) (a b : Nat) : p^r*a = p^r*b ↔ a=b := by
  constructor
  · exact Nat.mul_left_cancel (Nat.pow_pos hp)
  · rintro rfl; rfl

theorem distinct_layers {p r s : Nat} (hp : 1 < p) (hrs : r < s) (a b : Nat) (ha : ¬p ∣ a) :
    p^r*a ≠ p^s*b := by
  intro he
  obtain ⟨j,hj⟩ : ∃ j, s = r+(1+j) := ⟨s-r-1,by omega⟩
  rw [hj,Nat.pow_add,Nat.mul_assoc] at he
  have ea := Nat.mul_left_cancel (Nat.pow_pos (show 0 < p by omega)) he
  apply ha; refine ⟨p^j*b,?_⟩; rw [ea,Nat.pow_add,Nat.pow_one,Nat.mul_assoc]
theorem nonzero_layer (p : Nat) (hp : 1 < p) (k : Nat) (a b : ι → Nat)
    (ha : ∀ i, a i < p^k) (hb : ∀ i, b i < p^k)
    (nz : ∃ i j, a i*b j % p^k≠0) :
    ∃ j, 0 < j ∧ j ≤ k ∧ ∃ x y : ι → Nat,
      (∀ i, x i < p^j) ∧ (∀ i, y i < p^j) ∧ (∃ i, ¬p ∣ x i) ∧ (∃ i, ¬p ∣ y i) ∧
      ∀ i t, a i*b t % p^k = p^(k-j) * (x i*y t % p^j) := by
  obtain ⟨i,t,nz⟩ := nz
  have an : a i≠0 := by intro h; simp [h] at nz
  have bn : b t≠0 := by intro h; simp [h] at nz
  obtain ⟨r,_,x,hx,_,i',hi'⟩ := stripVector p hp k a ha ⟨i,an⟩
  obtain ⟨s,_,y,hy,_,t',ht'⟩ := stripVector p hp k b hb ⟨t,bn⟩
  have hrs : r+s < k := by
    apply Nat.lt_of_not_ge; intro ge; apply nz
    rw [hx,hy,invisible_product _ _ _ _ _ _ ge]
  let j := k-(r+s)
  have hj : 0 < j := by dsimp [j]; omega
  have q := Nat.pow_pos (show 0 < p by omega) (n:=j)
  refine ⟨j,hj,by dsimp [j]; omega,fun i => x i % p^j,fun i => y i % p^j,
    fun i => Nat.mod_lt _ q,fun i => Nat.mod_lt _ q,⟨i',fun h => hi' ((strip_mod_unit _ _ _ hj).mp h)⟩,
    ⟨t',fun h => ht' ((strip_mod_unit _ _ _ hj).mp h)⟩,?_⟩
  intro i t
  have he : k = r+s+j := by dsimp [j]; omega
  rw [hx,hy,←Nat.mul_mod,show k-j=r+s by omega,he,strata_mul_mod]

theorem realize_layer (p k j : Nat) (hp : 0 < p) (hj : j ≤ k) (x y : ι → Nat)
    (hx : ∀ i, x i < p^j) (hy : ∀ i, y i < p^j) :
    ∃ a b : ι → Nat, (∀ i, a i < p^k) ∧ (∀ i, b i < p^k) ∧
      ∀ i t, a i*b t % p^k = p^(k-j)*(x i*y t % p^j) := by
  have he : p^k=p^(k-j)*p^j := by rw [←Nat.pow_add,show k-j+j=k by omega]
  refine ⟨fun i => p^(k-j)*x i,y,?_,fun i => Nat.lt_of_lt_of_le (hy i) (Nat.pow_le_pow_right hp hj),?_⟩
  · intro i; rw [he]; exact Nat.mul_lt_mul_of_pos_left (hx i) (Nat.pow_pos hp)
  · intro i t; rw [Nat.mul_assoc,he,Nat.mul_mod_mul_left]


def isPP (d p q : Nat) (M : Matrix d) :=
  ∃ a b : Fin d → Fin q, (∃ i, ¬p∣(a i).val) ∧ (∃ i, ¬p∣(b i).val) ∧ out d q a b = M

abbrev PP (d p q : Nat) := {M : Matrix d // isPP d p q M}

abbrev layerImage (d p k : Nat) := Option (Σ r : Fin k, PP d p (p^(k-r.val)))

def zeroOuter (d n : Nat) (hn : 0 < n) : Img d n :=
  ⟨fun _ _ => 0,fun _ => ⟨0,hn⟩,fun _ => ⟨0,hn⟩,by funext a b; simp [out]⟩

theorem mk_scale_outer (d p k : Nat) (hp : 0 < p) (r : Fin k) (M : PP d p (p^(k-r.val))) :
    isOuter d (p^k) (fun i j => p^r.val * M.val i j) := by
  obtain ⟨a,b,_,_,e⟩ := M.property
  obtain ⟨A,B,hA,hB,h⟩ := realize_layer p k (k-r.val) hp (Nat.sub_le ..)
    (fun i => (a i).val) (fun i => (b i).val) (fun i => (a i).isLt) (fun i => (b i).isLt)
  refine ⟨fun i => ⟨A i,hA i⟩,fun i => ⟨B i,hB i⟩,?_⟩
  funext i j
  have er : k-(k-r.val)=r.val := by have := r.isLt; omega
  rw [← e]
  simpa only [out,er] using h i j

def scaleAll (d p k : Nat) (hp : 0 < p) : layerImage d p k → Img d (p^k) :=
  fun X => match X with
  | none => zeroOuter d (p^k) (Nat.pow_pos hp)
  | some ⟨r,M⟩ => ⟨fun i j => p^r.val*M.val i j,mk_scale_outer d p k hp r M⟩

theorem scaleAll_surj (d p k : Nat) (hp : 1 < p) :
    Function.Surjective (scaleAll d p k (show 0 < p by omega)) := by
  classical
  let X := scaleAll d p k (show 0 < p by omega)
  intro M
  by_cases hz : ∃ i j, M.val i j ≠ 0
  · obtain ⟨a,b,he⟩ := M.property
    obtain ⟨j,hj,hjk,V,W,hV,hW,nV,nW,h⟩ := nonzero_layer p hp k
      (fun i => (a i).val) (fun i => (b i).val)
      (fun i => (a i).isLt) (fun i => (b i).isLt)
      (by simpa only [← he,out] using hz)
    let r : Fin k := ⟨k-j,by omega⟩
    have hidx : k-r.val=j := by dsimp [r]; omega
    let A : Fin d → Fin (p^(k-r.val)) := fun i => ⟨V i, by simpa [hidx] using hV i⟩
    let B : Fin d → Fin (p^(k-r.val)) := fun i => ⟨W i, by simpa [hidx] using hW i⟩
    let N : PP d p (p^(k-r.val)) := ⟨out d (p^(k-r.val)) A B, A,B,nV,nW,rfl⟩
    refine ⟨some ⟨r,N⟩,?_⟩
    apply Subtype.ext; funext i t
    exact (by simpa only [X,scaleAll,out,A,B,N,r,hidx] using (h i t).symm :
      (X (some ⟨r,N⟩)).val i t = out d (p^k) a b i t).trans (congrFun (congrFun he i) t)
  · refine ⟨none,?_⟩; apply Subtype.ext; funext i j
    exact (Classical.not_not.mp (fun h => hz ⟨i,j,h⟩) : M.val i j = 0).symm

theorem primitive_pivot (d p k : Nat) (r : Fin k)
    (piv : ∀ a b : Nat, ¬p∣a → ¬p∣b → ¬p∣a*b) (M : PP d p (p^(k-r.val))) :
    ∃ i j, ¬p ∣ M.val i j := by
  obtain ⟨a,b,⟨i,hi⟩,⟨j,hj⟩,h⟩ := M.property
  refine ⟨i,j,?_⟩; rw [← h]
  exact fun q => piv _ _ hi hj ((strip_mod_unit p (k-r.val) _ (by have := r.isLt; omega)).mp q)

theorem scaleAll_inj (d p k : Nat) (hp : 1 < p)
    (piv : ∀ a b : Nat, ¬p∣a → ¬p∣b → ¬p∣a*b) :
    Function.Injective (scaleAll d p k (show 0 < p by omega)) := by
  intro X Y h
  let F := scaleAll d p k (show 0 < p by omega)
  have nes (r : Fin k) (M : PP d p (p^(k-r.val))) : F (some ⟨r,M⟩) ≠ F none := by
    intro eq
    obtain ⟨i,j,hij⟩ := primitive_pivot d p k r piv M
    apply hij
    have e : p^r.val * M.val i j = 0 := congrArg (fun M : Img d (p^k) => M.val i j) eq
    have hz := (scale_eq_iff (show 0 < p by omega) (M.val i j) 0).mp (e.trans (Nat.mul_zero _).symm)
    simp [hz]
  cases X with
  | none => cases Y with
    | none => rfl
    | some Y => obtain ⟨r,M⟩ := Y; exact False.elim (nes r M h.symm)
  | some X =>
    obtain ⟨r,M⟩ := X
    cases Y with
    | none => exact False.elim (nes r M h)
    | some Y =>
      obtain ⟨s,N⟩ := Y
      have cell (i j : Fin d) : p^r.val*M.val i j = p^s.val*N.val i j :=
        congrArg (fun M : Img d (p^k) => M.val i j) h
      have hrs : r=s := by
        rcases Nat.lt_trichotomy r.val s.val with hlt|he|hgt
        · obtain ⟨i,j,hij⟩ := primitive_pivot d p k r piv M
          exact False.elim (distinct_layers hp hlt _ _ hij (cell i j))
        · exact Fin.ext he
        · obtain ⟨i,j,hij⟩ := primitive_pivot d p k s piv N
          exact False.elim (distinct_layers hp hgt _ _ hij (cell i j).symm)
      subst s
      have eq : M=N := Subtype.ext (by
        funext i j; exact (scale_eq_iff (show 0 < p by omega) _ _).mp (cell i j))
      subst N; rfl



open scoped BigOperators Classical
noncomputable section ArithmeticNoInst

def toZ (n : Nat) (h : 0 < n) : Fin n ≃ ZMod n := by
  cases n with
  | zero => omega
  | succ n => exact Equiv.refl (Fin (n+1))

theorem toZ_mul (n : Nat) (h : 0 < n) (a b : Fin n) :
    toZ n h (a*b) = toZ n h a * toZ n h b := by cases n <;> first | omega | rfl

theorem toZ_one (n : Nat) [NeZero n] (h : 0 < n) : toZ n h (1 : Fin n) = 1 := by
  cases n <;> first | omega | rfl

theorem toZ_nat (n : Nat) (h : 0 < n) (a : Fin n) : toZ n h a = (a.val : ZMod n) := by
  cases n with
  | zero => omega
  | succ n =>
    letI : NeZero (n+1) := ⟨by omega⟩
    change toZ (n+1) h a = ((toZ (n+1) h a).val : ZMod (n+1))
    rw [ZMod.natCast_val,ZMod.cast_id]

theorem finUnit_pow (p j : Nat) (hp : p.Prime) (hj : 0 < j)
    [NeZero (p^j)] (a : Fin (p^j)) : (∃ inv, a*inv=1) ↔ ¬p∣a.val := by
  let hpos := pow_pos hp.pos j
  let e := toZ (p^j) hpos
  have hc : IsUnit (e a) ↔ ¬p∣a.val := by
    rw [show e a=(a.val : ZMod (p^j)) from toZ_nat _ _ _,ZMod.isUnit_natCast_iff_not_dvd_pow hp hj]
  refine Iff.trans ?_ hc
  rw [isUnit_iff_exists_inv]
  constructor
  · rintro ⟨b,h⟩
    exact ⟨e b, by rw [← toZ_mul, h,toZ_one]⟩
  · rintro ⟨b,h⟩
    refine ⟨e.symm b,e.injective ?_⟩
    calc e (a * e.symm b) = e a * e (e.symm b) := toZ_mul .. 
         _ = 1 := by simpa using h
         _ = e 1 := (toZ_one _ _).symm

theorem finPrim_pow (p j d : Nat) (hp : p.Prime) (hj : 0 < j)
    [NeZero (p^j)] (a : Vec d (p^j)) :
    primitive a ↔ ∃ i, ¬p∣(a i).val := by
  constructor
  · rintro ⟨i,b,h⟩
    exact ⟨i,(finUnit_pow p j hp hj (a i)).mp ⟨b,(Fin.mul_comm ..).trans h⟩⟩
  · rintro ⟨i,hi⟩
    obtain ⟨b,h⟩ := (finUnit_pow p j hp hj (a i)).mpr hi
    exact ⟨i,b,(Fin.mul_comm ..).trans h⟩

def cellBound {d n : Nat} (M : Img d n) (i j : Fin d) : Fin n :=
  ⟨M.val i j, by obtain ⟨a,b,e⟩ := M.property; rw [← e]; exact (a i * b j).isLt⟩

theorem cells_inj (d n : Nat) : Function.Injective (cellBound (d:=d) (n:=n)) := by
  intro a b h; apply Subtype.ext; funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

def finiteImg (d n : Nat) : Finite (Img d n) := Finite.of_injective _ (cells_inj d n)

def imgFintype (d n : Nat) : Fintype (Img d n) :=
  @Fintype.ofFinite _ (finiteImg d n)

def finitePP (d p n : Nat) : Finite (PP d p n) := by
  letI : Finite (Img d n) := finiteImg d n
  let incl : PP d p n → Img d n := fun u => ⟨u.val,by obtain ⟨a,b,_,_,h⟩ := u.property; exact ⟨a,b,h⟩⟩
  exact Finite.of_injective incl (fun a b h => Subtype.ext (congrArg (fun x : Img d n => x.val) h))

def ppFintype (d p n : Nat) : Fintype (PP d p n) :=
  @Fintype.ofFinite _ (finitePP d p n)

def imgNum (d n : Nat) : Nat := @Fintype.card _ (imgFintype d n)
def ppNum (d p n : Nat) : Nat := @Fintype.card _ (ppFintype d p n)

theorem card_divisibles (p j : Nat) (hp : 0 < p) (hj : 0 < j) :
    Fintype.card {r : Fin (p^j) // p∣r.val} = p^(j-1) := by
  classical
  have he : p^j=p*p^(j-1) := by
    calc p^j = p^(1+(j-1)) := congrArg (fun x => p^x) (by omega)
         _ = _ := by rw [pow_add,pow_one]
  let mk : Fin (p^(j-1)) → {r : Fin (p^j) // p ∣ r.val} := fun a =>
    ⟨⟨p*a.val, by rw [he]; exact Nat.mul_lt_mul_of_pos_left a.isLt hp⟩, a.val,rfl⟩
  have inj : Function.Injective mk := by
    intro a b h; apply Fin.ext
    apply Nat.mul_left_cancel hp
    exact congrArg (fun r : {r : Fin (p^j) // p∣r.val} => r.val.val) h
  have sur : Function.Surjective mk := by
    intro r; obtain ⟨a,ha⟩ := r.property
    have hlt : a < p^(j-1) := by
      have hh := r.val.isLt; rw [ha,he] at hh
      exact Nat.lt_of_mul_lt_mul_left hh
    exact ⟨⟨a,hlt⟩,Subtype.ext (Fin.ext ha.symm)⟩
  simpa using (Fintype.card_congr (Equiv.ofBijective mk ⟨inj,sur⟩)).symm

theorem card_unitRes (p j : Nat) (hp : p.Prime) (hj : 0 < j) [NeZero (p^j)] :
    Fintype.card (UnitRes (p^j)) = p^j-p^(j-1) := by
  classical
  have e : UnitRes (p^j) ≃ {a : Fin (p^j) // ¬p∣a.val} :=
    Equiv.subtypeEquivRight (fun a => finUnit_pow p j hp hj a)
  rw [Fintype.card_congr e,Fintype.card_subtype_compl,Fintype.card_fin,card_divisibles p j hp.pos hj]

theorem card_vectors (d p j : Nat) (hp : p.Prime) (hj : 0 < j) [NeZero (p^j)] :
    Fintype.card {a : Vec d (p^j) // primitive a} = p^(j*d)-p^((j-1)*d) := by
  classical
  let Div := {i : Fin (p^j) // p∣i.val}
  let All := fun v : Vec d (p^j) => ∀ i, p∣(v i).val
  let ea : {v // All v} ≃ (Fin d → Div) :=
    ⟨fun v i => ⟨v.val i,v.property i⟩,fun f => ⟨fun i => (f i).val,fun i => (f i).property⟩,
      fun _ => rfl,fun _ => rfl⟩
  let ep : {v : Vec d (p^j) // primitive v} ≃ {v // ¬All v} :=
    Equiv.subtypeEquivRight (fun v => by rw [finPrim_pow p j d hp hj]; simp [All])
  rw [Fintype.card_congr ep,Fintype.card_subtype_compl,Fintype.card_congr ea]
  change Fintype.card (Fin d → Fin (p^j)) - Fintype.card (Fin d → Div) = _
  rw [Fintype.card_pi_const,Fintype.card_pi_const,Fintype.card_fin]
  rw [show Fintype.card Div=p^(j-1) from card_divisibles p j hp.pos hj,← pow_mul,← pow_mul]

theorem card_primPairs (d p j : Nat) (hp : p.Prime) (hj : 0 < j) [NeZero (p^j)] :
    Fintype.card (PrimPair d (p^j)) = (p^(j*d)-p^((j-1)*d))^2 := by
  classical
  let e : PrimPair d (p^j) ≃ {a : Vec d (p^j) // primitive a} × {a : Vec d (p^j) // primitive a} :=
    ⟨fun x => (⟨x.val.1,x.property.1⟩,⟨x.val.2,x.property.2⟩),
      fun x => ⟨(x.1.val,x.2.val),x.1.property,x.2.property⟩,fun _ => rfl,fun _ => rfl⟩
  rw [Fintype.card_congr e,Fintype.card_prod,card_vectors d p j hp hj,pow_two]

def pp_equiv_primImage (d p j : Nat) (hp : p.Prime) (hj : 0 < j) [NeZero (p^j)] :
    PP d p (p^j) ≃ PrimImage d (p^j) := by
  classical
  let incl : PP d p (p^j) → Img d (p^j) := fun M =>
    ⟨M.val,by obtain ⟨a,b,_,_,he⟩ := M.property; exact ⟨a,b,he⟩⟩
  let naturals (M : Fin d → Fin d → Fin (p^j)) : Matrix d := fun i j => (M i j).val
  let f (M : PP d p (p^j)) : PrimImage d (p^j) :=
    ⟨cellBound (incl M),by
      obtain ⟨a,b,ha,hb,he⟩ := M.property
      refine ⟨⟨(a,b),(finPrim_pow p j d hp hj a).mpr ha,(finPrim_pow p j d hp hj b).mpr hb⟩,?_⟩
      funext i t; exact Fin.ext (congrFun (congrFun he i) t)⟩
  let g (M : PrimImage d (p^j)) : PP d p (p^j) :=
    ⟨naturals M.val,by
      obtain ⟨⟨⟨a,b⟩,ha,hb⟩,he⟩ := M.property
      refine ⟨a,b,(finPrim_pow p j d hp hj a).mp ha,(finPrim_pow p j d hp hj b).mp hb,?_⟩
      funext i t
      exact congrArg Fin.val (congrFun (congrFun he i) t)⟩
  exact ⟨f,g,fun x => Subtype.ext rfl,fun x => Subtype.ext (by funext i t; exact Fin.ext rfl)⟩

theorem card_pp (d p j : Nat) (hp : p.Prime) (hj : 0 < j) :
    ppNum d p (p^j) = (p^(j*d)-p^((j-1)*d))^2 / (p^j-p^(j-1)) := by
  classical
  letI : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : Fintype (PP d p (p^j)) := ppFintype d p (p^j)
  change Fintype.card (PP d p (p^j)) = _
  obtain ⟨f,hfi,hfs⟩ := primitive_atlas d (p^j)
  have hmul := Fintype.card_congr (Equiv.ofBijective f ⟨hfi,hfs⟩)
  rw [Fintype.card_prod,card_unitRes p j hp hj,card_primPairs d p j hp hj] at hmul
  rw [Fintype.card_congr (pp_equiv_primImage d p j hp hj),← hmul,
    Nat.mul_div_cancel _ (Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hp.one_lt (by omega)))]

end ArithmeticNoInst

open scoped BigOperators
noncomputable section FinalCountNoInst

def localTerm (d p r : Nat) : Nat :=
  let j := r+1
  (p^(j*d)-p^(r*d))^2 / (p^j-p^r)

def localSize (d p k : Nat) :=
  1 + ((List.range k).map (localTerm d p)).sum

theorem list_sum_range (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.map_append,List.sum_append,Finset.sum_range_succ,ih]
    simp

theorem layer_count (d p k : Nat) (hp : p.Prime) :
    imgNum d (p^k) = localSize d p k := by
  let piv (a b : Nat) (ha : ¬p∣a) (hb : ¬p∣b) : ¬p∣a*b :=
    fun e => (hp.dvd_mul.mp e).elim ha hb
  let E : layerImage d p k ≃ Img d (p^k) :=
    Equiv.ofBijective _ ⟨scaleAll_inj d p k hp.one_lt piv,scaleAll_surj d p k hp.one_lt⟩
  letI : Fintype (Img d (p^k)) := imgFintype d (p^k)
  letI : ∀ r : Fin k, Fintype (PP d p (p^(k-r.val))) := fun r => ppFintype d p (p^(k-r.val))
  change Fintype.card (Img d (p^k)) = _
  rw [← Fintype.card_congr E]
  change Fintype.card (Option (Σ r : Fin k, PP d p (p^(k-r.val)))) = _
  rw [Fintype.card_option,Fintype.card_sigma,localSize,list_sum_range,Nat.add_comm 1]
  congr 1
  have H (r : Fin k) : ppNum d p (p^(k-r.val)) = localTerm d p (k-1-r.val) := by
    have hi := r.isLt
    have e : (k-1-r.val)+1 = k-r.val := by omega
    unfold localTerm
    rw [e,card_pp d p _ hp (by omega),show k-r.val-1 = k-1-r.val by omega]
  calc
    _ = ∑ i : Fin k, localTerm d p (k-1-i.val) := Finset.sum_congr rfl (fun i _ => H i)
    _ = ∑ i ∈ Finset.range k, localTerm d p (k-1-i) := Fin.sum_univ_eq_sum_range (fun i : Nat => localTerm d p (k-1-i)) k
    _ = _ := Finset.sum_range_reflect _ _

theorem card_img_crt (d a b : Nat) (ha : 0 < a) (hb : 0 < b) (h : a.Coprime b) :
    imgNum d (a*b) = imgNum d a * imgNum d b := by
  let hab := Nat.mul_pos ha hb
  let Z := ZMod.chineseRemainder h
  let e := (toZ (a*b) hab).trans (Z.toEquiv.trans (Equiv.prodCongr (toZ a ha).symm (toZ b hb).symm))
  have mul (x y : Fin (a*b)) : e (x*y) = ((e x).1*(e y).1,(e x).2*(e y).2) := by
    have aeq : (toZ a ha) ((e (x*y)).1) = (toZ a ha) ((e x).1) * (toZ a ha) ((e y).1) := by
      change (toZ a ha) ((toZ a ha).symm ((Z (toZ (a*b) hab (x*y))).1)) =
        (toZ a ha) ((toZ a ha).symm ((Z (toZ (a*b) hab x)).1)) *
        (toZ a ha) ((toZ a ha).symm ((Z (toZ (a*b) hab y)).1))
      simp only [Equiv.apply_symm_apply,toZ_mul,map_mul,Prod.fst_mul]
    have beq : (toZ b hb) ((e (x*y)).2) = (toZ b hb) ((e x).2) * (toZ b hb) ((e y).2) := by
      change (toZ b hb) ((toZ b hb).symm ((Z (toZ (a*b) hab (x*y))).2)) =
        (toZ b hb) ((toZ b hb).symm ((Z (toZ (a*b) hab x)).2)) *
        (toZ b hb) ((toZ b hb).symm ((Z (toZ (a*b) hab y)).2))
      simp only [Equiv.apply_symm_apply,toZ_mul,map_mul,Prod.snd_mul]
    apply Prod.ext
    · exact (toZ a ha).injective (aeq.trans (toZ_mul a ha _ _).symm)
    · exact (toZ b hb).injective (beq.trans (toZ_mul b hb _ _).symm)
  obtain ⟨f,hf,hs⟩ := crt_images d (a*b) a b e e.injective e.surjective mul
  letI : Fintype (Img d (a*b)) := imgFintype d (a*b)
  letI : Fintype (Img d a) := imgFintype d a
  letI : Fintype (Img d b) := imgFintype d b
  exact (Fintype.card_congr (Equiv.ofBijective f ⟨hf,hs⟩)).trans (Fintype.card_prod _ _)

theorem card_img_one (d : Nat) : imgNum d 1 = 1 := by
  let z := zeroOuter d 1 (by decide)
  letI : Unique (Img d 1) :=
    ⟨⟨z⟩, fun x => by
      apply Subtype.ext; funext i j
      obtain ⟨a,b,e⟩ := x.property
      rw [← e]; simp [out,z,zeroOuter]⟩
  letI : Fintype (Img d 1) := imgFintype d 1
  exact Fintype.card_unique

theorem card_img_product (d : Nat) {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → Nat)
    (hpos : ∀ i ∈ s, 0 < f i)
    (hpc : ∀ i ∈ s, ∀ j ∈ s, i≠j → (f i).Coprime (f j)) :
    imgNum d (s.prod f) = s.prod (fun i => imgNum d (f i)) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using card_img_one d
  | @insert i s hi ih =>
    have hep (j : ι) (hj : j∈s) : j ∈ insert i s := Finset.mem_insert_of_mem hj
    have hpp : 0 < s.prod f := Finset.prod_pos (fun j hj => hpos j (hep j hj))
    have hcp : (f i).Coprime (s.prod f) := Nat.Coprime.prod_right fun j hj =>
      hpc i (Finset.mem_insert_self ..) j (hep j hj) (fun ee => hi (ee ▸ hj))
    rw [Finset.prod_insert hi,Finset.prod_insert hi,
      card_img_crt d _ _ (hpos i (Finset.mem_insert_self ..)) hpp hcp,
      ih (fun j hj => hpos j (hep j hj)) (fun a ha b hb => hpc a (hep a ha) b (hep b hb))]

theorem image_card (d m : Nat) (hm : 0 < m) :
    imgNum d m = m.primeFactors.prod (fun p => localSize d p (m.factorization p)) := by
  let f := fun p => p ^ m.factorization p
  have hF : m = m.primeFactors.prod f := Nat.prod_primeFactors_pow_factorization (by omega)
  calc
    imgNum d m = imgNum d (m.primeFactors.prod f) := by rw [← hF]
    _ = m.primeFactors.prod (fun p => imgNum d (f p)) :=
      card_img_product d m.primeFactors f
        (fun p hp => pow_pos (Nat.prime_of_mem_primeFactors hp).pos _)
        (fun p hp q hq neq => Nat.pairwise_coprime_pow_primeFactors_factorization (n:=m)
          (i := ⟨p,hp⟩) (j := ⟨q,hq⟩) (fun eq => neq (congrArg (fun x : ↥m.primeFactors => x.val) eq)))
    _ = _ := Finset.prod_congr rfl (fun p hp => layer_count d p _ (Nat.prime_of_mem_primeFactors hp))

theorem outer_enum (d m : Nat) (hm : 0 < m) :
    OuterCard d m (m.primeFactors.prod (fun p => localSize d p (m.factorization p))) := by
  letI : Fintype (Img d m) := imgFintype d m
  have h : Fintype.card (Img d m) = _ := image_card d m hm
  let e := (Fintype.equivFinOfCardEq h).symm
  refine ⟨fun i => (e i).val,fun i j he => e.injective (Subtype.ext he),?_⟩
  intro M
  constructor
  · rintro ⟨i,rfl⟩; exact (e i).property
  · intro H
    exact ⟨e.symm ⟨M,H⟩,congrArg Subtype.val (e.apply_symm_apply ⟨M,H⟩)⟩

end FinalCountNoInst

end PEqualNP.Outside.L_lib_529

theorem PEqualNP.Outside.L_lib_529 :
∀ (w m L : Nat), 0 < w → 2 ≤ m →
  let D := 2^w
  let Rows := Nat → Nat → Bool
  let mass := fun (rows : Rows) (h seed tail : Nat) =>
    ((List.range (2^(w+h))).filter (fun bits =>
      bits % D == seed && (bits >>> h) % D == tail &&
      (List.range h).all (fun i => rows i ((bits >>> i) % (2*D))))).length
  18*w*D*m+3*w ≤ L →
  let n := L+w
  let good := fun (tables : Rows) =>
    ∃ a b : Fin D → Nat, (∀ i, 0 < a i) ∧ (∀ j, 0 < b j) ∧
      ∀ s z : Fin D, mass tables L s.val z.val = a s * b z
  let count := fun (left right : Rows) =>
    ((List.range (2^n)).filter (fun word => (List.range n).all (fun site =>
      let pat := (List.range (w+1)).foldl (fun (acc bit : Nat) =>
        acc ||| ((word.testBit ((site+bit)%n)).toNat <<< bit)) 0
      if site < L then left site pat else right (site-L) pat))).length % m
  let localSize := fun (p k : Nat) =>
    1 + ((List.range k).map (fun level =>
      let j := level+1
      (p^(j*D)-p^(level*D))^2 / (p^j-p^level))).sum
  let alphabet := m.primeFactors.prod (fun prime => localSize prime (m.factorization prime))
  ∀ S : Nat,
    (∃ (send : Rows → Fin S) (read : Fin S → Rows → Nat),
      ∀ x y : Rows, good x → read (send x) y = count x y) ↔ alphabet ≤ S
 := by
  intro w m L hw hm
  dsimp only
  intro hL S
  exact PEqualNP.Outside.L_lib_529.msg_of_outerCard w m L hw hm hL _ (PEqualNP.Outside.L_lib_529.outer_enum _ _ (by omega)) S
