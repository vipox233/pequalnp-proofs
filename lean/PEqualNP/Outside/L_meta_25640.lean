import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25640_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def rot (k s x : Nat) : Nat :=
  ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k

def mix (k d z : Nat) : Nat :=
  z ^^^ rot k d z ^^^ rot k (k - d % k) z

def chi (k x : Nat) : Nat :=
  (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k))).toNat <<< i)) 0

def run (k d s t key name c : Nat) : Nat :=
  let z := rot k s key ^^^ name
  chi k (z ^^^ rot k d z ^^^ rot k (k - d % k) z) ^^^ rot k t key ^^^ c

def pack {k : Nat} (w : Fin (2 ^ k)) : List Bool :=
  (List.range k).map (fun pos => w.val.testBit pos)

def keyVal {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (mask : Fin (2 ^ m)) : Nat :=
  (List.ofFn (fun genIndex : Fin m =>
    if mask.val.testBit genIndex.val then (gen genIndex).val else 0)).foldl Nat.xor base.val

def rotIdx (k s i : Nat) : Nat :=
  (i + k - s % k) % k

lemma testBit_ge_of_lt_two_pow {x k i : Nat} (hx : x < 2 ^ k) (hi : k ≤ i) :
    x.testBit i = false := by
  have h1 : x < 2 ^ i := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) hi)
  exact Nat.testBit_lt_two_pow h1

lemma lt_two_pow_of_testBit {x k : Nat} (h : ∀ i, k ≤ i → x.testBit i = false) :
    x < 2 ^ k := by
  by_contra hge
  have hle : 2 ^ k ≤ x := Nat.le_of_not_lt hge
  have hne : x >>> k ≠ 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.ne_of_gt (Nat.div_pos hle (Nat.two_pow_pos k))
  have hex : ∃ j, (x >>> k).testBit j = true := by
    by_contra hall
    apply hne
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.zero_testBit]
    cases hb : (x >>> k).testBit j with
    | false => rfl
    | true => exact absurd ⟨j, hb⟩ hall
  rcases hex with ⟨j, hj⟩
  rw [Nat.testBit_shiftRight] at hj
  have hf := h (k + j) (Nat.le_add_right k j)
  rw [hj] at hf
  cases hf

lemma eq_of_testBit_lt {x y k : Nat} (hx : x < 2 ^ k) (hy : y < 2 ^ k)
    (h : ∀ i, i < k → x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < k
  · exact h i hi
  · rw [testBit_ge_of_lt_two_pow hx (Nat.le_of_not_lt hi),
        testBit_ge_of_lt_two_pow hy (Nat.le_of_not_lt hi)]

lemma xor_lt_two_pow {a b k : Nat} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    a ^^^ b < 2 ^ k := by
  apply lt_two_pow_of_testBit
  intro i hi
  rw [Nat.testBit_xor, testBit_ge_of_lt_two_pow ha hi, testBit_ge_of_lt_two_pow hb hi]
  rfl

lemma rot_lt (k s x : Nat) : rot k s x < 2 ^ k :=
  Nat.mod_lt _ (Nat.two_pow_pos k)

lemma rot_testBit {k s x i : Nat} (hk : 0 < k) (hx : x < 2 ^ k) (hi : i < k) :
    (rot k s x).testBit i = x.testBit (rotIdx k s i) := by
  unfold rot rotIdx
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  set r := s % k with hr_def
  have hrmod : r < k := Nat.mod_lt s hk
  by_cases hlt : i < r
  · have hge : ¬ (r ≤ i) := by omega
    simp only [hge, decide_false, Bool.false_and, Bool.false_or]
    have hidx : k - r + i = (i + k - r) % k := by
      have h1 : i + k - r = k - r + i := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega)]
    rw [hidx]
  · have hge : r ≤ i := Nat.le_of_not_lt hlt
    simp only [hge, decide_true, Bool.true_and]
    have hbig : k ≤ k - r + i := by omega
    rw [testBit_ge_of_lt_two_pow hx hbig, Bool.or_false]
    have hidx : i - r = (i + k - r) % k := by
      have h1 : i + k - r = (i - r) + k := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hidx]

lemma mix_lt {k d z : Nat} (hz : z < 2 ^ k) : mix k d z < 2 ^ k :=
  xor_lt_two_pow (xor_lt_two_pow hz (rot_lt k d z)) (rot_lt k (k - d % k) z)

lemma rot_xor {k s a b : Nat} (hk : 0 < k) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    rot k s (a ^^^ b) = rot k s a ^^^ rot k s b := by
  apply eq_of_testBit_lt (rot_lt k s _) (xor_lt_two_pow (rot_lt k s a) (rot_lt k s b))
  intro i hi
  rw [Nat.testBit_xor, rot_testBit hk (xor_lt_two_pow ha hb) hi,
      rot_testBit hk ha hi, rot_testBit hk hb hi, Nat.testBit_xor]

lemma mix_xor {k d a b : Nat} (hk : 0 < k) (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    mix k d (a ^^^ b) = mix k d a ^^^ mix k d b := by
  unfold mix
  rw [rot_xor hk ha hb, rot_xor hk ha hb]
  apply eq_of_testBit_lt
  · exact xor_lt_two_pow (xor_lt_two_pow (xor_lt_two_pow ha hb) (xor_lt_two_pow (rot_lt k d a) (rot_lt k d b)))
      (xor_lt_two_pow (rot_lt k (k - d % k) a) (rot_lt k (k - d % k) b))
  · exact xor_lt_two_pow (xor_lt_two_pow (xor_lt_two_pow ha (rot_lt k d a)) (rot_lt k (k - d % k) a))
      (xor_lt_two_pow (xor_lt_two_pow hb (rot_lt k d b)) (rot_lt k (k - d % k) b))
  · intro i _
    simp only [Nat.testBit_xor]
    cases a.testBit i <;> cases b.testBit i <;>
    cases (rot k d a).testBit i <;> cases (rot k d b).testBit i <;>
    cases (rot k (k - d % k) a).testBit i <;> cases (rot k (k - d % k) b).testBit i <;> rfl

lemma mix_testBit {k d z i : Nat} (hk : 0 < k) (hz : z < 2 ^ k) (hi : i < k) :
    (mix k d z).testBit i =
      xor (xor (z.testBit i) (z.testBit (rotIdx k d i))) (z.testBit (rotIdx k (k - d % k) i)) := by
  unfold mix
  rw [Nat.testBit_xor, Nat.testBit_xor, rot_testBit hk hz hi, rot_testBit hk hz hi]

lemma rotIdx_compl {k d i : Nat} (hk : 0 < k) (hi : i < k) :
    rotIdx k (k - d % k) i = (i + d % k) % k := by
  unfold rotIdx
  have hr : d % k < k := Nat.mod_lt d hk
  by_cases h0 : d % k = 0
  · simp [h0, Nat.mod_eq_of_lt hi]
  · have hsub : (k - d % k) % k = k - d % k := Nat.mod_eq_of_lt (by omega)
    rw [hsub]
    have h1 : i + k - (k - d % k) = i + d % k := by omega
    rw [h1]

lemma mix_zero_of_ker {k d w : Nat} (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (hw : w < 2 ^ k) (hmix : mix k d w = 0) : w = 0 := by
  apply eq_of_testBit_lt hw (Nat.two_pow_pos k)
  intro i0 hi0
  rw [Nat.zero_testBit]
  set r := d % k with hr_def
  have hr : r < k := Nat.mod_lt d hk
  set f : Nat → Bool := fun t => w.testBit ((i0 + t * r) % k)
  have hf_rec : ∀ t : Nat, f (t + 2) = xor (f (t + 1)) (f t) := by
    intro t
    set pos := (i0 + (t + 1) * r) % k with hpos_def
    have hpos_lt : pos < k := Nat.mod_lt _ hk
    have h0 := congrArg (fun n => n.testBit pos) hmix
    rw [Nat.zero_testBit, mix_testBit hk hw hpos_lt, rotIdx_compl hk hpos_lt] at h0
    have hprev : rotIdx k d pos = (i0 + t * r) % k := by
      unfold rotIdx
      rw [← hr_def]
      have h1 : (pos + k - r) % k = (i0 + t * r) % k := by
        have htr : i0 + (t + 1) * r = (i0 + t * r) + r := by rw [Nat.succ_mul]; omega
        have h2 : (pos + k - r) + r = pos + k := by omega
        have hadd : ((pos + k - r) + r) % k = ((i0 + t * r) + r) % k := by
          rw [h2, Nat.add_mod_right, hpos_def, htr, Nat.mod_mod]
        have hstep : ((pos + k - r) + r + (k - r)) % k = ((i0 + t * r) + r + (k - r)) % k := by
          rw [Nat.add_mod ((pos + k - r) + r), hadd, ← Nat.add_mod ((i0 + t * r) + r)]
        have ha1 : (pos + k - r) + r + (k - r) = (pos + k - r) + k := by omega
        have hb1 : (i0 + t * r) + r + (k - r) = (i0 + t * r) + k := by omega
        rw [ha1, hb1, Nat.add_mod_right, Nat.add_mod_right] at hstep
        exact hstep
      exact h1
    have hnext : (pos + r) % k = (i0 + (t + 2) * r) % k := by
      have htr2 : (t + 2) * r = (t + 1) * r + r := Nat.succ_mul (t + 1) r
      rw [hpos_def, Nat.mod_add_mod, htr2]
      congr 1
      omega
    rw [hprev, ← hr_def, hnext] at h0
    change xor (xor (f (t + 1)) (f t)) (f (t + 2)) = false at h0
    cases h1 : f (t + 1) <;> cases h2 : f t <;> cases h3 : f (t + 2) <;>
      rw [h1, h2, h3] at h0 <;> first | rfl | cases h0
  have hf_per3 : ∀ t : Nat, f (t + 3) = f t := by
    intro t
    have h1 := hf_rec (t + 1)
    have h2 := hf_rec t
    have h13 : t + 1 + 2 = t + 3 := by omega
    rw [h13, h2] at h1
    cases hfa : f (t + 1) <;> cases hfb : f t <;> rw [hfa, hfb] at h1 <;> exact h1
  have hf_per3q : ∀ q t : Nat, f (t + 3 * q) = f t := by
    intro q
    induction q with
    | zero => intro t; simp
    | succ q ih =>
      intro t
      have h1 : t + 3 * (q + 1) = (t + 3 * q) + 3 := by omega
      rw [h1, hf_per3, ih]
  have hf_perk : ∀ t : Nat, f (t + k) = f t := by
    intro t
    change w.testBit ((i0 + (t + k) * r) % k) = w.testBit ((i0 + t * r) % k)
    congr 1
    have h1 : i0 + (t + k) * r = (i0 + t * r) + r * k := by
      rw [Nat.add_mul, Nat.mul_comm k r]
      omega
    rw [h1, Nat.add_mul_mod_self_right]
  have hf_per1 : ∀ t : Nat, f (t + 1) = f t := by
    intro t
    have hmod : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod with h1 | h2
    · have hk_eq : t + k = (t + 1) + 3 * (k / 3) := by omega
      have h := hf_perk t
      rw [hk_eq, hf_per3q] at h
      exact h
    · have hk_eq : t + k + k = (t + 1) + 3 * ((2 * k) / 3) := by omega
      have h := (hf_perk (t + k)).trans (hf_perk t)
      rw [hk_eq, hf_per3q] at h
      exact h
  have h01 := hf_per1 0
  have h02 := (hf_per1 1).trans h01
  have hrec0 := hf_rec 0
  rw [h01, h02] at hrec0
  have hf0 : f 0 = false := by
    cases h : f 0 with
    | false => rfl
    | true => rw [h] at hrec0; cases hrec0
  simpa [f, Nat.mod_eq_of_lt hi0] using hf0

lemma mix_injective {k d : Nat} (hk : 0 < k) (hk3 : k % 3 ≠ 0) :
    Function.Injective (fun u : Fin (2 ^ k) => (⟨mix k d u.val, mix_lt u.isLt⟩ : Fin (2 ^ k))) := by
  intro u v huv
  have hval : mix k d u.val = mix k d v.val := congrArg Fin.val huv
  have hxor : mix k d (u.val ^^^ v.val) = 0 := by
    rw [mix_xor hk u.isLt v.isLt, hval, Nat.xor_self]
  have h0 := mix_zero_of_ker hk hk3 (xor_lt_two_pow u.isLt v.isLt) hxor
  apply Fin.ext
  apply eq_of_testBit_lt u.isLt v.isLt
  intro i _
  have hb := congrArg (fun n => n.testBit i) h0
  rw [Nat.testBit_xor, Nat.zero_testBit] at hb
  cases hu : u.val.testBit i <;> cases hv : v.val.testBit i <;> simp_all

noncomputable def mixEquiv {k : Nat} (hk : 0 < k) (hk3 : k % 3 ≠ 0) (d s : Nat) (base : Fin (2 ^ k)) :
    Fin (2 ^ k) ≃ Fin (2 ^ k) :=
  Equiv.ofBijective
    (fun u : Fin (2 ^ k) =>
      ⟨mix k d (rot k s base.val ^^^ u.val),
       mix_lt (xor_lt_two_pow (rot_lt k s base.val) u.isLt)⟩)
    (Finite.injective_iff_bijective.mp (by
      intro u v huv
      have h1 := mix_injective hk hk3 (d := d)
        (a₁ := ⟨rot k s base.val ^^^ u.val, xor_lt_two_pow (rot_lt k s base.val) u.isLt⟩)
        (a₂ := ⟨rot k s base.val ^^^ v.val, xor_lt_two_pow (rot_lt k s base.val) v.isLt⟩)
        huv
      have hval : rot k s base.val ^^^ u.val = rot k s base.val ^^^ v.val := congrArg Fin.val h1
      apply Fin.ext
      apply eq_of_testBit_lt u.isLt v.isLt
      intro i _
      have hb := congrArg (fun n => n.testBit i) hval
      simp only [Nat.testBit_xor] at hb
      cases h1 : (rot k s base.val).testBit i <;>
      cases h2 : u.val.testBit i <;> cases h3 : v.val.testBit i <;>
        rw [h1, h2, h3] at hb <;> first | rfl | cases hb))

lemma foldl_or_bits_testBit (f : Nat → Bool) : ∀ n p : Nat,
    ((List.range n).foldl (fun acc i => acc ||| ((f i).toNat <<< i)) 0).testBit p =
      if p < n then f p else false := by
  intro n
  induction n with
  | zero =>
    intro p
    simp
  | succ n ih =>
    intro p
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [Nat.testBit_or, ih, Nat.testBit_shiftLeft]
    by_cases hlt : p < n
    · have hlt' : p < n + 1 := by omega
      have hge : ¬ (n ≤ p) := by omega
      simp [hlt, hlt', hge]
    · by_cases heq : p = n
      · subst heq
        have hlt' : p < p + 1 := by omega
        simp only [lt_irrefl, ite_false, Bool.false_or, le_refl, decide_true, Bool.true_and,
          Nat.sub_self, hlt', ite_true]
        cases f p <;> rfl
      · have hlt' : ¬ (p < n + 1) := by omega
        have hgt : p - n ≠ 0 := by omega
        have htb : (f n).toNat.testBit (p - n) = false := by
          cases f n with
          | false => simp
          | true =>
            exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
              (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ p - n)))
        simp [hlt, hlt', htb]

lemma chi_testBit (k x i : Nat) (hi : i < k) :
    (chi k x).testBit i =
      xor (x.testBit i) (!(x.testBit ((i + 1) % k)) && x.testBit ((i + 2) % k)) := by
  unfold chi
  rw [foldl_or_bits_testBit]
  simp [hi]

lemma chi_lt (k x : Nat) : chi k x < 2 ^ k := by
  apply lt_two_pow_of_testBit
  intro i hi
  unfold chi
  rw [foldl_or_bits_testBit]
  have h : ¬ (i < k) := by omega
  simp [h]

lemma run_lt {k d s t key name c : Nat} (hc : c < 2 ^ k) :
    run k d s t key name c < 2 ^ k := by
  unfold run
  exact xor_lt_two_pow (xor_lt_two_pow (chi_lt k _) (rot_lt k t key)) hc

lemma lt_two_pow_sub_iff {x k h : Nat} (hx : x < 2 ^ k) (hh : h ≤ k) :
    x < 2 ^ (k - h) ↔ ∀ i : Nat, k - h ≤ i → i < k → x.testBit i = false := by
  constructor
  · intro hlt i hi1 _
    exact testBit_ge_of_lt_two_pow hlt hi1
  · intro hall
    apply lt_two_pow_of_testBit
    intro i hi
    by_cases hik : i < k
    · exact hall i hi hik
    · exact testBit_ge_of_lt_two_pow hx (Nat.le_of_not_lt hik)

lemma foldl_xor_lt {k : Nat} : ∀ (l : List Nat) (acc : Nat),
    acc < 2 ^ k → (∀ a ∈ l, a < 2 ^ k) → l.foldl Nat.xor acc < 2 ^ k
  | [], acc, hacc, _ => hacc
  | a :: l, acc, hacc, hall => by
    simp only [List.foldl_cons]
    apply foldl_xor_lt l _ (xor_lt_two_pow hacc (hall a (by simp)))
    intro b hb
    exact hall b (by simp [hb])

lemma foldl_xor_testBit (p : Nat) : ∀ (l : List Nat) (acc : Nat),
    (l.foldl Nat.xor acc).testBit p = (l.map (fun a => a.testBit p)).foldl xor (acc.testBit p)
  | [], acc => rfl
  | a :: l, acc => by
    simp only [List.foldl_cons, List.map_cons, ← Nat.testBit_xor]
    exact foldl_xor_testBit p l (acc ^^^ a)

lemma keyVal_lt {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (mask : Fin (2 ^ m)) :
    keyVal base gen mask < 2 ^ k := by
  unfold keyVal
  apply foldl_xor_lt _ _ base.isLt
  intro a ha
  rw [List.mem_ofFn] at ha
  rcases ha with ⟨g, rfl⟩
  split_ifs
  · exact (gen g).isLt
  · exact Nat.two_pow_pos k

lemma foldl_xor_bool_append : ∀ (l1 l2 : List Bool) (acc : Bool),
    (l1 ++ l2).foldl xor acc = l2.foldl xor (l1.foldl xor acc)
  | [], l2, acc => rfl
  | a :: l1, l2, acc => foldl_xor_bool_append l1 l2 (xor acc a)

lemma foldl_xor_bool_shift : ∀ (l : List Bool) (a b : Bool),
    l.foldl xor (xor a b) = xor a (l.foldl xor b)
  | [], a, b => rfl
  | x :: l, a, b => by
    simp only [List.foldl_cons]
    have h : xor (xor a b) x = xor a (xor b x) := by
      cases a <;> cases b <;> cases x <;> rfl
    rw [h]
    exact foldl_xor_bool_shift l a (xor b x)

lemma foldl_xor_bool_false : ∀ (l : List Bool) (a : Bool),
    l.foldl xor a = xor a (l.foldl xor false)
  | l, a => by
    have h := foldl_xor_bool_shift l a false
    simpa using h

lemma foldl_xor_bool_all_false : ∀ (l : List Bool),
    (∀ b ∈ l, b = false) → l.foldl xor false = false
  | [], _ => rfl
  | a :: l, hall => by
    have ha : a = false := hall a (by simp)
    subst ha
    simp only [List.foldl_cons, Bool.xor_false]
    exact foldl_xor_bool_all_false l (fun b hb => hall b (by simp [hb]))

lemma foldl_xor_bool_ofFn_zero {m : Nat} (f : Fin m → Bool) :
    (List.ofFn (fun g : Fin m => false && f g)).foldl xor false = false := by
  apply foldl_xor_bool_all_false
  intro b hb
  rw [List.mem_ofFn] at hb
  rcases hb with ⟨g, rfl⟩
  rfl

lemma foldl_xor_bool_ofFn_single {m : Nat} (f : Fin m → Bool) (g0 : Fin m) :
    (List.ofFn (fun g : Fin m => decide (g = g0) && f g)).foldl xor false = f g0 := by
  have h : ∀ (n : Nat) (fn : Fin n → Bool) (idx : Fin n),
      (List.ofFn (fun g : Fin n => decide (g = idx) && fn g)).foldl xor false = fn idx := by
    intro n
    induction n with
    | zero => intro _ idx; exact Fin.elim0 idx
    | succ n ih =>
      intro fn idx
      rw [List.ofFn_succ, List.foldl_cons, Bool.false_xor]
      rw [foldl_xor_bool_false]
      cases idx using Fin.cases with
      | zero =>
        have hrest : (List.ofFn (fun g : Fin n => decide (g.succ = 0) && fn g.succ)).foldl xor false = false := by
          apply foldl_xor_bool_all_false
          intro b hb
          rw [List.mem_ofFn] at hb
          rcases hb with ⟨g, rfl⟩
          simp
        rw [hrest]
        simp
      | succ j =>
        have h0 : (decide ((0 : Fin (n + 1)) = j.succ) && fn 0) = false := by
          have hne : (0 : Fin (n + 1)) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
          simp [hne]
        rw [h0, Bool.false_xor]
        have heq : (fun g : Fin n => decide (g.succ = j.succ) && fn g.succ) =
            (fun g : Fin n => decide (g = j) && fn g.succ) := by
          funext g
          simp [Fin.succ_inj]
        rw [heq]
        exact ih (fun g => fn g.succ) j
  exact h m f g0

lemma foldl_xor_bool_ofFn_xor {m : Nat} (f1 f2 : Fin m → Bool) :
    (List.ofFn (fun g : Fin m => xor (f1 g) (f2 g))).foldl xor false =
      xor ((List.ofFn f1).foldl xor false) ((List.ofFn f2).foldl xor false) := by
  have h : ∀ (n : Nat) (a b : Fin n → Bool),
      (List.ofFn (fun g : Fin n => xor (a g) (b g))).foldl xor false =
        xor ((List.ofFn a).foldl xor false) ((List.ofFn b).foldl xor false) := by
    intro n
    induction n with
    | zero => intro _ _; rfl
    | succ n ih =>
      intro a b
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
      simp only [List.foldl_cons, Bool.false_xor]
      rw [foldl_xor_bool_false, foldl_xor_bool_false (List.ofFn (fun i => a i.succ)),
          foldl_xor_bool_false (List.ofFn (fun i => b i.succ)), ih]
      cases a 0 <;> cases b 0 <;>
      cases (List.ofFn (fun i : Fin n => a i.succ)).foldl xor false <;>
      cases (List.ofFn (fun i : Fin n => b i.succ)).foldl xor false <;> rfl
  exact h m f1 f2

lemma keyVal_testBit {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (mask : Fin (2 ^ m)) (p : Nat) :
    (keyVal base gen mask).testBit p =
      xor (base.val.testBit p)
        ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && (gen g).val.testBit p)).foldl xor false) := by
  unfold keyVal
  rw [foldl_xor_testBit, foldl_xor_bool_false]
  congr 1
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext g
  dsimp only [Function.comp]
  by_cases hm : mask.val.testBit g.val = true
  · simp [hm]
  · have hm' : mask.val.testBit g.val = false := Bool.eq_false_iff.mpr hm
    simp [hm']

lemma rot_keyVal_testBit {k m : Nat} (hk : 0 < k) (s : Nat)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (mask : Fin (2 ^ m)) {i : Nat} (hi : i < k) :
    (rot k s (keyVal base gen mask)).testBit i =
      xor ((rot k s base.val).testBit i)
        ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k s (gen g).val).testBit i)).foldl xor false) := by
  rw [rot_testBit hk (keyVal_lt base gen mask) hi, rot_testBit hk base.isLt hi, keyVal_testBit]
  congr 2
  apply congrArg List.ofFn
  funext g
  rw [rot_testBit hk (gen g).isLt hi]

lemma mix_rot_keyVal_testBit {k m : Nat} (hk : 0 < k) (d s : Nat)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (mask : Fin (2 ^ m)) {i : Nat} (hi : i < k) :
    (mix k d (rot k s (keyVal base gen mask) ^^^ base.val ^^^ base.val)).testBit i =
      xor ((mix k d (rot k s base.val)).testBit i)
        ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && (mix k d (rot k s (gen g).val)).testBit i)).foldl xor false) := by
  have hcancel : rot k s (keyVal base gen mask) ^^^ base.val ^^^ base.val = rot k s (keyVal base gen mask) := by
    rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [hcancel]
  rw [mix_testBit hk (rot_lt k s _) hi, mix_testBit hk (rot_lt k s _) hi]
  have hi1 : rotIdx k d i < k := Nat.mod_lt _ hk
  have hi2 : rotIdx k (k - d % k) i < k := Nat.mod_lt _ hk
  rw [rot_keyVal_testBit hk s base gen mask hi,
      rot_keyVal_testBit hk s base gen mask hi1,
      rot_keyVal_testBit hk s base gen mask hi2]
  have hfn : (fun g : Fin m => mask.val.testBit g.val && (mix k d (rot k s (gen g).val)).testBit i) =
      (fun g : Fin m => xor (xor (mask.val.testBit g.val && (rot k s (gen g).val).testBit i)
        (mask.val.testBit g.val && (rot k s (gen g).val).testBit (rotIdx k d i)))
        (mask.val.testBit g.val && (rot k s (gen g).val).testBit (rotIdx k (k - d % k) i))) := by
    funext g
    rw [mix_testBit hk (rot_lt k s _) hi]
    cases mask.val.testBit g.val <;>
    cases (rot k s (gen g).val).testBit i <;>
    cases (rot k s (gen g).val).testBit (rotIdx k d i) <;>
    cases (rot k s (gen g).val).testBit (rotIdx k (k - d % k) i) <;> rfl
  rw [hfn, foldl_xor_bool_ofFn_xor, foldl_xor_bool_ofFn_xor]
  generalize (rot k s base.val).testBit i = x0
  generalize (rot k s base.val).testBit (rotIdx k d i) = x1
  generalize (rot k s base.val).testBit (rotIdx k (k - d % k) i) = x2
  generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k s (gen g).val).testBit i)).foldl xor false = y0
  generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k s (gen g).val).testBit (rotIdx k d i))).foldl xor false = y1
  generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k s (gen g).val).testBit (rotIdx k (k - d % k) i))).foldl xor false = y2
  cases x0 <;> cases x1 <;> cases x2 <;> cases y0 <;> cases y1 <;> cases y2 <;> rfl

def deltaBit {k : Nat} (d s : Nat) (g : Fin (2 ^ k)) (i : Nat) : Bool :=
  (mix k d (rot k s g.val)).testBit i

def eBit {k : Nat} (d s t : Nat) (g : Fin (2 ^ k)) (i : Nat) : Bool :=
  xor (deltaBit d s g i) ((rot k t g.val).testBit i)

def baseOutBit {k : Nat} (t : Nat) (base c : Fin (2 ^ k)) (i : Nat) : Bool :=
  xor ((rot k t base.val).testBit i) (c.val.testBit i)

lemma run_testBit_via_y {k m : Nat} (hk : 0 < k) (d s t : Nat)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (c u : Fin (2 ^ k))
    (mask : Fin (2 ^ m)) {i : Nat} (hi : i < k) :
    let y := mix k d (rot k s base.val ^^^ u.val)
    let A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 1) % k))).foldl xor false
    let B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 2) % k))).foldl xor false
    let E := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eBit d s t (gen g) i)).foldl xor false
    (run k d s t (keyVal base gen mask) u.val c.val).testBit i =
      xor (y.testBit i)
        (xor (!(xor (y.testBit ((i + 1) % k)) A) && xor (y.testBit ((i + 2) % k)) B)
          (xor (baseOutBit t base c i) E)) := by
  dsimp only
  unfold run
  rw [Nat.testBit_xor, Nat.testBit_xor, chi_testBit k _ i hi]
  set z := rot k s (keyVal base gen mask) ^^^ u.val
  have hz_lt : z < 2 ^ k := xor_lt_two_pow (rot_lt k s _) u.isLt
  have hmix_eq : ∀ j, j < k →
      (mix k d z).testBit j =
        xor ((mix k d (rot k s base.val ^^^ u.val)).testBit j)
          ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) j)).foldl xor false) := by
    intro j hj
    have hz_split : z = (rot k s base.val ^^^ u.val) ^^^ (rot k s (keyVal base gen mask) ^^^ rot k s base.val) := by
      apply eq_of_testBit_lt hz_lt (xor_lt_two_pow (xor_lt_two_pow (rot_lt k s _) u.isLt)
        (xor_lt_two_pow (rot_lt k s _) (rot_lt k s _)))
      intro p _
      simp only [z, Nat.testBit_xor]
      cases (rot k s (keyVal base gen mask)).testBit p <;>
      cases (rot k s base.val).testBit p <;> cases u.val.testBit p <;> rfl
    rw [hz_split, mix_xor hk (xor_lt_two_pow (rot_lt k s _) u.isLt) (xor_lt_two_pow (rot_lt k s _) (rot_lt k s _)),
        Nat.testBit_xor, mix_xor hk (rot_lt k s _) (rot_lt k s _), Nat.testBit_xor]
    have hm := mix_rot_keyVal_testBit hk d s base gen mask hj
    have hcancel : rot k s (keyVal base gen mask) ^^^ base.val ^^^ base.val = rot k s (keyVal base gen mask) := by
      rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    rw [hcancel] at hm
    rw [hm]
    unfold deltaBit
    generalize (mix k d (rot k s base.val ^^^ u.val)).testBit j = a1
    generalize (mix k d (rot k s base.val)).testBit j = a2
    generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (mix k d (rot k s (gen g).val)).testBit j)).foldl xor false = a3
    cases a1 <;> cases a2 <;> cases a3 <;> rfl
  have hmi0 := hmix_eq i hi
  have hmi1 := hmix_eq ((i + 1) % k) (Nat.mod_lt _ hk)
  have hmi2 := hmix_eq ((i + 2) % k) (Nat.mod_lt _ hk)
  change xor (xor (xor ((mix k d z).testBit i)
      (!((mix k d z).testBit ((i + 1) % k)) && (mix k d z).testBit ((i + 2) % k)))
      ((rot k t (keyVal base gen mask)).testBit i)) (c.val.testBit i) = _
  rw [hmi0, hmi1, hmi2, rot_keyVal_testBit hk t base gen mask hi]
  have hE : (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eBit d s t (gen g) i)).foldl xor false =
      xor ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) i)).foldl xor false)
          ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k t (gen g).val).testBit i)).foldl xor false) := by
    rw [← foldl_xor_bool_ofFn_xor]
    congr 1
    apply congrArg List.ofFn
    funext g
    unfold eBit
    cases mask.val.testBit g.val <;> cases deltaBit d s (gen g) i <;> cases (rot k t (gen g).val).testBit i <;> rfl
  rw [hE]
  unfold baseOutBit
  generalize (mix k d (rot k s base.val ^^^ u.val)).testBit i = y0
  generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) i)).foldl xor false = d0
  generalize (!(xor ((mix k d (rot k s base.val ^^^ u.val)).testBit ((i + 1) % k))
    ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 1) % k))).foldl xor false)) &&
    xor ((mix k d (rot k s base.val ^^^ u.val)).testBit ((i + 2) % k))
    ((List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 2) % k))).foldl xor false)) = nl
  generalize (rot k t base.val).testBit i = rb
  generalize (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (rot k t (gen g).val).testBit i)).foldl xor false = rg
  generalize c.val.testBit i = cb
  cases y0 <;> cases d0 <;> cases nl <;> cases rb <;> cases rg <;> cases cb <;> rfl

def deltaFun (a b e u v : Bool) : Bool :=
  xor (xor (!u && v) (!(xor u a) && xor v b)) e

lemma deltaFun_eq (a b e : Bool) :
    deltaFun a b e false false = xor (!a && b) e ∧
    deltaFun a b e false true = xor (!(!a && !b)) e ∧
    deltaFun a b e true false = xor (a && b) e ∧
    deltaFun a b e true true = xor (a && !b) e := by
  cases a <;> cases b <;> cases e <;> decide

structure GenAcc where
  s10 : Bool
  s01 : Bool
  s11 : Bool
  f00 : Bool
  f01 : Bool
  f10 : Bool
  f11 : Bool

def genAccInit : GenAcc :=
  ⟨false, false, false, false, false, false, false⟩

def genAccStep (acc : GenAcc) (a b e : Bool) : GenAcc :=
  let na := !a
  let nb := !b
  let p00 := na && nb
  let p10 := a && nb
  let p01 := na && b
  let p11 := a && b
  ⟨acc.s10 || p10,
   acc.s01 || p01,
   acc.s11 || p11,
   acc.f00 || xor p01 e,
   acc.f01 || xor (!p00) e,
   acc.f10 || xor p11 e,
   acc.f11 || xor p10 e⟩

def genAccRun {m : Nat} (aFn bFn eFn : Fin m → Bool) : ∀ n : Nat, n ≤ m → GenAcc
  | 0, _ => genAccInit
  | n + 1, hn =>
    let prev := genAccRun aFn bFn eFn n (by omega)
    genAccStep prev (aFn ⟨n, hn⟩) (bFn ⟨n, hn⟩) (eFn ⟨n, hn⟩)

def accBad (acc : GenAcc) : Bool :=
  (acc.s10 && acc.s01) || (acc.s10 && acc.s11) || (acc.s01 && acc.s11)

def accOk (acc : GenAcc) (u v : Bool) : Bool :=
  !(accBad acc) &&
    !(match u, v with
      | false, false => acc.f00
      | false, true => acc.f01
      | true, false => acc.f10
      | true, true => acc.f11)

lemma genAccRun_props {m : Nat} (aFn bFn eFn : Fin m → Bool) :
    ∀ n (hn : n ≤ m),
      let acc := genAccRun aFn bFn eFn n hn
      (acc.s10 = true ↔ ∃ g : Fin m, g.val < n ∧ aFn g = true ∧ bFn g = false) ∧
      (acc.s01 = true ↔ ∃ g : Fin m, g.val < n ∧ aFn g = false ∧ bFn g = true) ∧
      (acc.s11 = true ↔ ∃ g : Fin m, g.val < n ∧ aFn g = true ∧ bFn g = true) ∧
      (∀ u v : Bool,
        (match u, v with
         | false, false => acc.f00
         | false, true => acc.f01
         | true, false => acc.f10
         | true, true => acc.f11) = true ↔
        ∃ g : Fin m, g.val < n ∧ deltaFun (aFn g) (bFn g) (eFn g) u v = true) := by
  intro n
  induction n with
  | zero =>
    intro hn
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [genAccRun, genAccInit]
    · simp [genAccRun, genAccInit]
    · simp [genAccRun, genAccInit]
    · intro u v
      cases u <;> cases v <;> simp [genAccRun, genAccInit]
  | succ n ih =>
    intro hn
    rcases ih (by omega) with ⟨h10, h01, h11, hf⟩
    set g0 : Fin m := ⟨n, hn⟩
    have hsplit : ∀ P : Fin m → Prop,
        (∃ g : Fin m, g.val < n + 1 ∧ P g) ↔
        (∃ g : Fin m, g.val < n ∧ P g) ∨ P g0 := by
      intro P
      constructor
      · rintro ⟨g, hg, hp⟩
        by_cases hlt : g.val < n
        · exact Or.inl ⟨g, hlt, hp⟩
        · have heq : g = g0 := Fin.ext (by dsimp [g0]; omega)
          rw [heq] at hp
          exact Or.inr hp
      · rintro (⟨g, hg, hp⟩ | hp)
        · exact ⟨g, by omega, hp⟩
        · exact ⟨g0, by simp [g0], hp⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · dsimp only [genAccRun, genAccStep]
      rw [Bool.or_eq_true, h10, hsplit]
      cases aFn g0 <;> cases bFn g0 <;> simp
    · dsimp only [genAccRun, genAccStep]
      rw [Bool.or_eq_true, h01, hsplit]
      cases aFn g0 <;> cases bFn g0 <;> simp
    · dsimp only [genAccRun, genAccStep]
      rw [Bool.or_eq_true, h11, hsplit]
      cases aFn g0 <;> cases bFn g0 <;> simp
    · intro u v
      have hfu := hf u v
      have hde := deltaFun_eq (aFn g0) (bFn g0) (eFn g0)
      cases u <;> cases v <;>
        (dsimp only [genAccRun, genAccStep]; rw [Bool.or_eq_true, hfu, hsplit])
      · rw [hde.1]
      · rw [hde.2.1]
      · rw [hde.2.2.1]
      · rw [hde.2.2.2]

lemma accBad_iff {m : Nat} (aFn bFn eFn : Fin m → Bool) :
    accBad (genAccRun aFn bFn eFn m (le_refl m)) = true ↔
      ∃ g1 g2 : Fin m, xor (aFn g1 && bFn g2) (aFn g2 && bFn g1) = true := by
  rcases genAccRun_props aFn bFn eFn m (le_refl m) with ⟨h10, h01, h11, _⟩
  unfold accBad
  simp only [Bool.or_eq_true, Bool.and_eq_true, h10, h01, h11]
  constructor
  · rintro ((⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩ | ⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩) |
      ⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩)
    · exact ⟨g1, g2, by simp [ha1, hb1, ha2, hb2]⟩
    · exact ⟨g1, g2, by simp [ha1, hb1, ha2, hb2]⟩
    · exact ⟨g1, g2, by simp [ha1, hb1, ha2, hb2]⟩
  · rintro ⟨g1, g2, hdet⟩
    cases ha1 : aFn g1 <;> cases hb1 : bFn g1 <;> cases ha2 : aFn g2 <;> cases hb2 : bFn g2
    all_goals simp_all
    · exact Or.inl (Or.inl ⟨⟨g2, ha2, hb2⟩, ⟨g1, ha1, hb1⟩⟩)
    · exact Or.inr ⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩
    · exact Or.inl (Or.inl ⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩)
    · exact Or.inl (Or.inr ⟨⟨g1, ha1, hb1⟩, ⟨g2, ha2, hb2⟩⟩)
    · exact Or.inr ⟨⟨g2, ha2, hb2⟩, ⟨g1, ha1, hb1⟩⟩
    · exact Or.inl (Or.inr ⟨⟨g2, ha2, hb2⟩, ⟨g1, ha1, hb1⟩⟩)

lemma mask_single_lt {m : Nat} (g : Fin m) : 2 ^ g.val < 2 ^ m :=
  Nat.pow_lt_pow_right (by decide : 1 < 2) g.isLt

lemma mask_pair_lt {m : Nat} {g1 g2 : Fin m} (hne : g1 ≠ g2) :
    2 ^ g1.val + 2 ^ g2.val < 2 ^ m := by
  have hval : g1.val ≠ g2.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have h1 : 2 ^ g1.val < 2 ^ g2.val := Nat.pow_lt_pow_right (by decide : 1 < 2) hlt
    have h2 : 2 ^ (g2.val + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) g2.isLt
    rw [Nat.pow_succ] at h2
    omega
  · have h1 : 2 ^ g2.val < 2 ^ g1.val := Nat.pow_lt_pow_right (by decide : 1 < 2) hgt
    have h2 : 2 ^ (g1.val + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide : 0 < 2) g1.isLt
    rw [Nat.pow_succ] at h2
    omega

lemma testBit_pair_pow_lt {a b j : Nat} (hab : a < b) :
    (2 ^ b + 2 ^ a).testBit j = xor (decide (j = b)) (decide (j = a)) := by
  have hlt : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by decide : 1 < 2) hab
  by_cases hjb : j < b
  · have hbj : 1 ≤ b - j := by omega
    have hpow : 2 ^ b = 2 ^ j * 2 ^ (b - j) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt hjb)]
    have heven : 2 ^ (b - j) % 2 = 0 := by
      have h1 : b - j = (b - j - 1) + 1 := by omega
      rw [h1, Nat.pow_succ]
      omega
    rw [Nat.testBit_eq_decide_div_mod_eq, hpow, Nat.mul_add_div (Nat.two_pow_pos j)]
    have hmod : (2 ^ (b - j) + 2 ^ a / 2 ^ j) % 2 = (2 ^ a / 2 ^ j) % 2 := by omega
    rw [hmod, ← Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_two_pow]
    have hne : j ≠ b := by omega
    by_cases hja : j = a
    · subst hja; simp [hne]
    · have haj : a ≠ j := Ne.symm hja
      simp [hne, hja, haj]
  · by_cases heq : j = b
    · subst heq
      rw [Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : (2 ^ j + 2 ^ a) / 2 ^ j = 1 := by
        have h1 : 2 ^ j + 2 ^ a = 2 ^ j * 1 + 2 ^ a := by omega
        rw [h1, Nat.mul_add_div (Nat.two_pow_pos j), Nat.div_eq_of_lt hlt]
      rw [hdiv]
      have hne : j ≠ a := by omega
      simp [hne]
    · have hgt : b + 1 ≤ j := by omega
      have hsum_lt : 2 ^ b + 2 ^ a < 2 ^ j := by
        have h1 : 2 ^ (b + 1) ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) hgt
        rw [Nat.pow_succ] at h1
        omega
      rw [Nat.testBit_lt_two_pow hsum_lt]
      have hne1 : j ≠ b := heq
      have hne2 : j ≠ a := by omega
      simp [hne1, hne2]

lemma testBit_pair_pow {a b j : Nat} (hne : a ≠ b) :
    (2 ^ a + 2 ^ b).testBit j = xor (decide (j = a)) (decide (j = b)) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [Nat.add_comm, testBit_pair_pow_lt hlt, Bool.xor_comm]
  · exact testBit_pair_pow_lt hgt

lemma all_masks_bit_iff {m : Nat} (aFn bFn eFn : Fin m → Bool) (y0 y1 y2 bout : Bool) :
    (∀ mask : Fin (2 ^ m),
      let A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false
      let B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false
      let E := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eFn g)).foldl xor false
      xor y0 (xor (!(xor y1 A) && xor y2 B) (xor bout E)) = false) ↔
    (accOk (genAccRun aFn bFn eFn m (le_refl m)) y1 y2 = true ∧
      y0 = xor (!y1 && y2) bout) := by
  set acc := genAccRun aFn bFn eFn m (le_refl m)
  set F : Fin (2 ^ m) → Bool := fun mask =>
    let A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false
    let B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false
    let E := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eFn g)).foldl xor false
    xor y0 (xor (!(xor y1 A) && xor y2 B) (xor bout E))
  have hF0 : F ⟨0, Nat.two_pow_pos m⟩ = xor y0 (xor (!y1 && y2) bout) := by
    simp only [F, Nat.zero_testBit, foldl_xor_bool_ofFn_zero, Bool.xor_false]
  have hFg : ∀ g : Fin m,
      F ⟨2 ^ g.val, mask_single_lt g⟩ =
        xor y0 (xor (!(xor y1 (aFn g)) && xor y2 (bFn g)) (xor bout (eFn g))) := by
    intro g
    simp only [F]
    have htb : ∀ fn : Fin m → Bool,
        (List.ofFn (fun g' : Fin m => (2 ^ g.val).testBit g'.val && fn g')).foldl xor false = fn g := by
      intro fn
      have heq : (fun g' : Fin m => (2 ^ g.val).testBit g'.val && fn g') =
          (fun g' : Fin m => decide (g' = g) && fn g') := by
        funext g'
        rw [Nat.testBit_two_pow]
        by_cases h : g' = g
        · subst h; simp
        · have hv : g.val ≠ g'.val := fun hv => h (Fin.ext hv.symm)
          simp [h, hv]
      rw [heq]
      exact foldl_xor_bool_ofFn_single fn g
    rw [htb aFn, htb bFn, htb eFn]
  have hFpair : ∀ (g1 g2 : Fin m) (hne : g1 ≠ g2),
      F ⟨2 ^ g1.val + 2 ^ g2.val, mask_pair_lt hne⟩ =
        xor y0 (xor (!(xor y1 (xor (aFn g1) (aFn g2))) && xor y2 (xor (bFn g1) (bFn g2)))
          (xor bout (xor (eFn g1) (eFn g2)))) := by
    intro g1 g2 hne
    simp only [F]
    have hvalne : g1.val ≠ g2.val := fun h => hne (Fin.ext h)
    have htb : ∀ fn : Fin m → Bool,
        (List.ofFn (fun g' : Fin m => (2 ^ g1.val + 2 ^ g2.val).testBit g'.val && fn g')).foldl xor false =
          xor (fn g1) (fn g2) := by
      intro fn
      have heq : (fun g' : Fin m => (2 ^ g1.val + 2 ^ g2.val).testBit g'.val && fn g') =
          (fun g' : Fin m => xor (decide (g' = g1) && fn g') (decide (g' = g2) && fn g')) := by
        funext g'
        rw [testBit_pair_pow hvalne]
        have h1 : decide (g'.val = g1.val) = decide (g' = g1) := by
          simp [Fin.ext_iff]
        have h2 : decide (g'.val = g2.val) = decide (g' = g2) := by
          simp [Fin.ext_iff]
        rw [h1, h2]
        cases decide (g' = g1) <;> cases decide (g' = g2) <;> cases fn g' <;> rfl
      rw [heq, foldl_xor_bool_ofFn_xor, foldl_xor_bool_ofFn_single, foldl_xor_bool_ofFn_single]
    rw [htb aFn, htb bFn, htb eFn]
  constructor
  · intro hall
    have h0 : F ⟨0, Nat.two_pow_pos m⟩ = false := hall ⟨0, Nat.two_pow_pos m⟩
    rw [hF0] at h0
    have hy0 : y0 = xor (!y1 && y2) bout := by
      cases y0 <;> cases y1 <;> cases y2 <;> cases bout <;> simp_all
    refine ⟨?_, hy0⟩
    unfold accOk
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true']
    constructor
    · cases hbad : accBad acc with
      | false => rfl
      | true =>
        exfalso
        rcases (accBad_iff aFn bFn eFn).mp hbad with ⟨g1, g2, hdet⟩
        have hne : g1 ≠ g2 := by
          intro heq
          subst heq
          simp at hdet
        have c0 : F ⟨0, Nat.two_pow_pos m⟩ = false := hall ⟨0, Nat.two_pow_pos m⟩
        have c1 : F ⟨2 ^ g1.val, mask_single_lt g1⟩ = false := hall ⟨2 ^ g1.val, mask_single_lt g1⟩
        have c2 : F ⟨2 ^ g2.val, mask_single_lt g2⟩ = false := hall ⟨2 ^ g2.val, mask_single_lt g2⟩
        have c12 : F ⟨2 ^ g1.val + 2 ^ g2.val, mask_pair_lt hne⟩ = false :=
          hall ⟨2 ^ g1.val + 2 ^ g2.val, mask_pair_lt hne⟩
        rw [hF0] at c0
        rw [hFg g1] at c1
        rw [hFg g2] at c2
        rw [hFpair g1 g2 hne] at c12
        have hx4 : ∀ (u1 u2 a1 b1 a2 b2 : Bool),
            xor (a1 && b2) (a2 && b1) = true →
            xor (xor (!u1 && u2) (!(xor u1 a1) && xor u2 b1))
                (xor (!(xor u1 a2) && xor u2 b2) (!(xor u1 (xor a1 a2)) && xor u2 (xor b1 b2))) = true := by decide
        have h4x : ∀ (u0 ub e1 e2 z0 z1 z2 z12 : Bool),
            xor u0 (xor z0 ub) = false →
            xor u0 (xor z1 (xor ub e1)) = false →
            xor u0 (xor z2 (xor ub e2)) = false →
            xor u0 (xor z12 (xor ub (xor e1 e2))) = false →
            xor (xor z0 z1) (xor z2 z12) = false := by decide
        have hfalse := h4x y0 bout (eFn g1) (eFn g2) (!y1 && y2)
          (!(xor y1 (aFn g1)) && xor y2 (bFn g1))
          (!(xor y1 (aFn g2)) && xor y2 (bFn g2))
          (!(xor y1 (xor (aFn g1) (aFn g2))) && xor y2 (xor (bFn g1) (bFn g2))) c0 c1 c2 c12
        have htrue := hx4 y1 y2 (aFn g1) (bFn g1) (aFn g2) (bFn g2) hdet
        rw [hfalse] at htrue
        cases htrue
    · cases hf : (match y1, y2 with
        | false, false => acc.f00
        | false, true => acc.f01
        | true, false => acc.f10
        | true, true => acc.f11) with
      | false => rfl
      | true =>
        exfalso
        have hprops := (genAccRun_props aFn bFn eFn m (le_refl m)).2.2.2 y1 y2
        rcases hprops.mp hf with ⟨g, _, hdg⟩
        have cg : F ⟨2 ^ g.val, mask_single_lt g⟩ = false := hall ⟨2 ^ g.val, mask_single_lt g⟩
        rw [hFg g, hy0] at cg
        unfold deltaFun at hdg
        have hx1 : ∀ (u1 u2 ub a b e : Bool),
            xor (xor (!u1 && u2) (!(xor u1 a) && xor u2 b)) e = true →
            xor (xor (!u1 && u2) ub) (xor (!(xor u1 a) && xor u2 b) (xor ub e)) = false →
            False := by decide
        exact hx1 y1 y2 bout (aFn g) (bFn g) (eFn g) hdg cg
  · rintro ⟨hok, hy0⟩
    unfold accOk at hok
    rw [Bool.and_eq_true, Bool.not_eq_true', Bool.not_eq_true'] at hok
    rcases hok with ⟨hnbad, hnf⟩
    have hno_det : ∀ g1 g2 : Fin m, xor (aFn g1 && bFn g2) (aFn g2 && bFn g1) = false := by
      intro g1 g2
      cases hd : xor (aFn g1 && bFn g2) (aFn g2 && bFn g1) with
      | false => rfl
      | true =>
        have hb := (accBad_iff aFn bFn eFn).mpr ⟨g1, g2, hd⟩
        rw [hnbad] at hb
        cases hb
    have hall_g : ∀ g : Fin m, deltaFun (aFn g) (bFn g) (eFn g) y1 y2 = false := by
      intro g
      cases hd : deltaFun (aFn g) (bFn g) (eFn g) y1 y2 with
      | false => rfl
      | true =>
        have hprops := (genAccRun_props aFn bFn eFn m (le_refl m)).2.2.2 y1 y2
        have hft := hprops.mpr ⟨g, g.isLt, hd⟩
        rw [hnf] at hft
        cases hft
    have hAB_lin : ∃ cA cB : Bool, ∀ mask : Fin (2 ^ m),
        let A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false
        let B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false
        (A && B) = xor (cA && A) (cB && B) := by
      by_cases h10 : ∃ g : Fin m, aFn g = true ∧ bFn g = false
      · refine ⟨false, false, fun mask => ?_⟩
        dsimp only
        have hB0 : (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false = false := by
          apply foldl_xor_bool_all_false
          intro x hx
          rw [List.mem_ofFn] at hx
          rcases hx with ⟨g, rfl⟩
          rcases h10 with ⟨g0, ha0, hb0⟩
          have hd := hno_det g0 g
          rw [ha0, hb0] at hd
          cases hb : bFn g <;> simp_all
        simp [hB0]
      · by_cases h01 : ∃ g : Fin m, aFn g = false ∧ bFn g = true
        · refine ⟨false, false, fun mask => ?_⟩
          dsimp only
          have hA0 : (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false = false := by
            apply foldl_xor_bool_all_false
            intro x hx
            rw [List.mem_ofFn] at hx
            rcases hx with ⟨g, rfl⟩
            rcases h01 with ⟨g0, ha0, hb0⟩
            have hd := hno_det g0 g
            rw [ha0, hb0] at hd
            cases ha : aFn g <;> simp_all
          simp [hA0]
        · refine ⟨true, false, fun mask => ?_⟩
          dsimp only
          have hab : aFn = bFn := by
            funext g
            cases ha : aFn g <;> cases hb : bFn g
            · rfl
            · exfalso; exact h01 ⟨g, ha, hb⟩
            · exfalso; exact h10 ⟨g, ha, hb⟩
            · rfl
          rw [hab]
          cases (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false <;> rfl
    rcases hAB_lin with ⟨cA, cB, hAB⟩
    have hAB_g : ∀ g : Fin m, (aFn g && bFn g) = xor (cA && aFn g) (cB && bFn g) := by
      intro g
      have h := hAB ⟨2 ^ g.val, mask_single_lt g⟩
      dsimp only at h
      have htb : ∀ fn : Fin m → Bool,
          (List.ofFn (fun g' : Fin m => (2 ^ g.val).testBit g'.val && fn g')).foldl xor false = fn g := by
        intro fn
        have heq : (fun g' : Fin m => (2 ^ g.val).testBit g'.val && fn g') =
            (fun g' : Fin m => decide (g' = g) && fn g') := by
          funext g'
          rw [Nat.testBit_two_pow]
          by_cases h' : g' = g
          · subst h'; simp
          · have hv : g.val ≠ g'.val := fun hv => h' (Fin.ext hv.symm)
            simp [h', hv]
        rw [heq]
        exact foldl_xor_bool_ofFn_single fn g
      rw [htb aFn, htb bFn] at h
      exact h
    intro mask
    dsimp only
    set A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false
    set B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false
    set E := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eFn g)).foldl xor false
    have hexpand : ∀ a b e : Bool, (a && b) = xor (cA && a) (cB && b) →
        xor (xor (!y1 && y2) (!(xor y1 a) && xor y2 b)) e =
          xor (xor ((xor y2 cA) && a) ((xor (!y1) cB) && b)) e := by
      have hall7 : ∀ (u1 u2 kA kB a b e : Bool), (a && b) = xor (kA && a) (kB && b) →
          xor (xor (!u1 && u2) (!(xor u1 a) && xor u2 b)) e =
            xor (xor ((xor u2 kA) && a) ((xor (!u1) kB) && b)) e := by decide
      intro a b e hlin
      exact hall7 y1 y2 cA cB a b e hlin
    have hlin_g : ∀ g : Fin m,
        xor (xor ((xor y2 cA) && aFn g) ((xor (!y1) cB) && bFn g)) (eFn g) = false := by
      intro g
      have h1 := hexpand (aFn g) (bFn g) (eFn g) (hAB_g g)
      have h2 := hall_g g
      unfold deltaFun at h2
      rw [← h1]
      exact h2
    have hsum : xor (xor ((xor y2 cA) && A) ((xor (!y1) cB) && B)) E = false := by
      have hdist : ∀ (c : Bool) (fn : Fin m → Bool),
          (c && (List.ofFn (fun g : Fin m => mask.val.testBit g.val && fn g)).foldl xor false) =
            (List.ofFn (fun g : Fin m => mask.val.testBit g.val && (c && fn g))).foldl xor false := by
        intro c fn
        cases c with
        | false =>
          rw [Bool.false_and]
          symm
          apply foldl_xor_bool_all_false
          intro x hx
          rw [List.mem_ofFn] at hx
          rcases hx with ⟨g, rfl⟩
          simp
        | true =>
          simp
      rw [show A = (List.ofFn (fun g : Fin m => mask.val.testBit g.val && aFn g)).foldl xor false from rfl,
          show B = (List.ofFn (fun g : Fin m => mask.val.testBit g.val && bFn g)).foldl xor false from rfl,
          show E = (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eFn g)).foldl xor false from rfl]
      rw [hdist (xor y2 cA) aFn, hdist (xor (!y1) cB) bFn,
          ← foldl_xor_bool_ofFn_xor, ← foldl_xor_bool_ofFn_xor]
      apply foldl_xor_bool_all_false
      intro x hx
      rw [List.mem_ofFn] at hx
      rcases hx with ⟨g, rfl⟩
      have hlg := hlin_g g
      have hstep : ∀ (mb x1 x2 x3 : Bool), xor (xor x1 x2) x3 = false →
          xor (xor (mb && x1) (mb && x2)) (mb && x3) = false := by decide
      exact hstep (mask.val.testBit g.val) ((xor y2 cA) && aFn g) ((xor (!y1) cB) && bFn g) (eFn g) hlg
    have hfull := hexpand A B E (hAB mask)
    rw [hy0]
    have hcomb : ∀ (u1 u2 u3 u4 : Bool),
        xor (xor u1 u2) (xor u3 (xor u2 u4)) = xor (xor u1 u3) u4 := by decide
    rw [hcomb (!y1 && y2) bout (!(xor y1 A) && xor y2 B) E, hfull, hsum]

def bitOk {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (i : Nat)
    (u v : Bool) : Bool :=
  accOk (genAccRun
    (fun g => deltaBit d s (gen g) ((i + 1) % k))
    (fun g => deltaBit d s (gen g) ((i + 2) % k))
    (fun g => eBit d s t (gen g) i) m (le_refl m)) u v

structure TailState where
  ok : Bool
  b1 : Bool
  b2 : Bool

def tailStep {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (i : Nat) (st : TailState) : TailState :=
  let ok' := st.ok && bitOk d s t base gen i st.b1 st.b2
  let v := xor (!st.b1 && st.b2) (baseOutBit t base c i)
  ⟨ok', v, st.b1⟩

def tailRun {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) : Nat → TailState
  | 0 => ⟨if k = 1 then t0 == t1 else true, t0, t1⟩
  | step + 1 =>
    tailStep d s t base gen c (k - 1 - step) (tailRun d s t base gen c t0 t1 step)

def validTail {k m : Nat} (h d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) : Bool :=
  let st := tailRun d s t base gen c t0 t1 h
  if h = k then st.ok && (st.b1 == t0) && (st.b2 == t1)
  else if h + 1 = k then st.ok && (st.b1 == t1)
  else st.ok

def tailSeq {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) (idx : Nat) : Bool :=
  if idx < k then (tailRun d s t base gen c t0 t1 (k - idx)).b1
  else if idx = k then t0
  else t1

lemma tailRun_b1_b2 {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) :
    ∀ step : Nat, step ≤ k →
      (tailRun d s t base gen c t0 t1 step).b1 = tailSeq d s t base gen c t0 t1 (k - step) ∧
      (tailRun d s t base gen c t0 t1 step).b2 = tailSeq d s t base gen c t0 t1 (k - step + 1) := by
  intro step
  induction step with
  | zero =>
    intro _
    simp [tailRun, tailSeq]
  | succ step ih =>
    intro hle
    rcases ih (by omega) with ⟨hb1, hb2⟩
    have hsub1 : k - (step + 1) < k := by omega
    have hsub2 : k - (k - (step + 1)) = step + 1 := by omega
    have hsub3 : k - (step + 1) + 1 = k - step := by omega
    constructor
    · simp only [tailSeq, hsub1, ite_true, hsub2]
    · simp only [tailRun, tailStep, hsub3, hb1]

lemma tailSeq_rec {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) {i : Nat} (hi : i < k) :
    tailSeq d s t base gen c t0 t1 i =
      xor (!(tailSeq d s t base gen c t0 t1 (i + 1)) && tailSeq d s t base gen c t0 t1 (i + 2))
        (baseOutBit t base c i) := by
  have hki : k - i = (k - 1 - i) + 1 := by omega
  have hstep : k - 1 - (k - 1 - i) = i := by omega
  have hprev := tailRun_b1_b2 d s t base gen c t0 t1 (k - 1 - i) (by omega)
  have hp1 : k - (k - 1 - i) = i + 1 := by omega
  have hp2 : i + 1 + 1 = i + 2 := rfl
  rw [hp1, hp2] at hprev
  unfold tailSeq
  simp only [hi, ite_true]
  rw [hki]
  simp only [tailRun, tailStep, hstep, hprev.1, hprev.2]
  rfl

lemma tailRun_ok_iff {k m : Nat} (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) (t0 t1 : Bool) :
    ∀ step : Nat, step ≤ k →
      ((tailRun d s t base gen c t0 t1 step).ok = true ↔
        (if k = 1 then t0 = t1 else True) ∧
        ∀ i : Nat, k - step ≤ i → i < k →
          bitOk d s t base gen i
            (tailSeq d s t base gen c t0 t1 (i + 1))
            (tailSeq d s t base gen c t0 t1 (i + 2)) = true) := by
  intro step
  induction step with
  | zero =>
    intro _
    simp only [tailRun, Nat.sub_zero]
    constructor
    · intro h
      refine ⟨?_, fun i hi1 hi2 => by omega⟩
      by_cases hk1 : k = 1
      · simp only [hk1, ite_true, beq_iff_eq] at h ⊢
        exact h
      · simp [hk1]
    · rintro ⟨h1, _⟩
      by_cases hk1 : k = 1
      · simp only [hk1, ite_true, beq_iff_eq] at h1 ⊢
        exact h1
      · simp [hk1]
  | succ step ih =>
    intro hle
    rcases tailRun_b1_b2 d s t base gen c t0 t1 step (by omega) with ⟨hb1, hb2⟩
    have hidx : k - step = k - 1 - step + 1 := by omega
    have hidx2 : k - 1 - step + 1 + 1 = k - 1 - step + 2 := rfl
    simp only [tailRun, tailStep, Bool.and_eq_true, ih (by omega), hb1, hb2]
    rw [hidx, hidx2]
    constructor
    · rintro ⟨⟨hk1, hall⟩, hcur⟩
      refine ⟨hk1, fun i hi1 hi2 => ?_⟩
      by_cases heq : i = k - 1 - step
      · subst heq; exact hcur
      · exact hall i (by omega) hi2
    · rintro ⟨hk1, hall⟩
      refine ⟨⟨hk1, fun i hi1 hi2 => hall i (by omega) hi2⟩, hall (k - 1 - step) (by omega) (by omega)⟩

def sideCount {k m : Nat} (h d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k))
    (c : Fin (2 ^ k)) : Nat :=
  let v := validTail h d s t base gen c
  (v false false).toNat + (v false true).toNat + (v true false).toNat + (v true true).toNat

lemma sideCount_le_four {k m : Nat} (h d s t : Nat) (base : Fin (2 ^ k))
    (gen : Fin m → Fin (2 ^ k)) (c : Fin (2 ^ k)) :
    sideCount h d s t base gen c ≤ 4 := by
  unfold sideCount
  dsimp only
  generalize validTail h d s t base gen c false false = a
  generalize validTail h d s t base gen c false true = b
  generalize validTail h d s t base gen c true false = e
  generalize validTail h d s t base gen c true true = f
  cases a <;> cases b <;> cases e <;> cases f <;> decide

lemma nat_card_validTail {k m : Nat} (h d s t : Nat) (base : Fin (2 ^ k))
    (gen : Fin m → Fin (2 ^ k)) (c : Fin (2 ^ k)) :
    Nat.card { p : Bool × Bool // validTail h d s t base gen c p.1 p.2 = true } =
      sideCount h d s t base gen c := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold sideCount
  dsimp only
  generalize validTail h d s t base gen c = v
  have hsum : (Finset.univ.filter (fun p : Bool × Bool => v p.1 p.2 = true)).card =
      (v false false).toNat + (v false true).toNat + (v true false).toNat + (v true true).toNat := by
    have h4 : ∀ (a b e f : Bool),
        (Finset.univ.filter (fun p : Bool × Bool =>
          (match p.1, p.2 with
           | false, false => a
           | false, true => b
           | true, false => e
           | true, true => f) = true)).card =
        a.toNat + b.toNat + e.toNat + f.toNat := by decide
    have hfeq : Finset.univ.filter (fun p : Bool × Bool => v p.1 p.2 = true) =
        Finset.univ.filter (fun p : Bool × Bool =>
          (match p.1, p.2 with
           | false, false => v false false
           | false, true => v false true
           | true, false => v true false
           | true, true => v true true) = true) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases x <;> cases y <;> rfl
    rw [hfeq]
    exact h4 (v false false) (v false true) (v true false) (v true true)
  exact hsum

def bitsOfFin {k : Nat} (y : Fin (2 ^ k)) : Fin k → Bool :=
  fun i => y.val.testBit i.val

def finOfBits {k : Nat} (f : Fin k → Bool) : Fin (2 ^ k) :=
  ⟨(List.range k).foldl (fun acc i => acc ||| ((if hi : i < k then f ⟨i, hi⟩ else false).toNat <<< i)) 0,
   lt_two_pow_of_testBit (fun p hp => by
     rw [foldl_or_bits_testBit]
     have h : ¬ (p < k) := by omega
     simp [h])⟩

def finBitsEquiv (k : Nat) : Fin (2 ^ k) ≃ (Fin k → Bool) where
  toFun := bitsOfFin
  invFun := finOfBits
  left_inv := fun y => by
    apply Fin.ext
    apply eq_of_testBit_lt (finOfBits (bitsOfFin y)).isLt y.isLt
    intro i hi
    unfold finOfBits bitsOfFin
    dsimp only
    rw [foldl_or_bits_testBit]
    simp [hi]
  right_inv := fun f => by
    funext i
    unfold finOfBits bitsOfFin
    dsimp only
    rw [foldl_or_bits_testBit]
    simp [i.isLt]

lemma side_card_eq {k m : Nat} (hk : 0 < k) (hk3 : k % 3 ≠ 0) {h : Nat} (hh : h ≤ k)
    (d s t : Nat) (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (c : Fin (2 ^ k)) :
    Nat.card { u : Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
      run k d s t (keyVal base gen mask) u.val c.val < 2 ^ (k - h) } =
      2 ^ (k - (h + 2)) * sideCount h d s t base gen c := by
  let P_y : (Fin k → Bool) → Prop := fun f =>
    ∀ i : Nat, k - h ≤ i → ∀ hi : i < k,
      bitOk d s t base gen i (f ⟨(i + 1) % k, Nat.mod_lt _ hk⟩) (f ⟨(i + 2) % k, Nat.mod_lt _ hk⟩) = true ∧
      f ⟨i, hi⟩ = xor (!(f ⟨(i + 1) % k, Nat.mod_lt _ hk⟩) && f ⟨(i + 2) % k, Nat.mod_lt _ hk⟩) (baseOutBit t base c i)
  have hE1 : { u : Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
      run k d s t (keyVal base gen mask) u.val c.val < 2 ^ (k - h) } ≃ { f : Fin k → Bool // P_y f } := by
    refine Equiv.subtypeEquiv ((mixEquiv hk hk3 d s base).trans (finBitsEquiv k)) ?_
    intro u
    set y := mix k d (rot k s base.val ^^^ u.val)
    have hiff1 : (∀ mask : Fin (2 ^ m), run k d s t (keyVal base gen mask) u.val c.val < 2 ^ (k - h)) ↔
        (∀ i : Nat, k - h ≤ i → i < k → ∀ mask : Fin (2 ^ m),
          (run k d s t (keyVal base gen mask) u.val c.val).testBit i = false) := by
      constructor
      · intro hall i hi1 hi2 mask
        exact (lt_two_pow_sub_iff (run_lt c.isLt) hh).mp (hall mask) i hi1 hi2
      · intro hall mask
        exact (lt_two_pow_sub_iff (run_lt c.isLt) hh).mpr (fun i hi1 hi2 => hall i hi1 hi2 mask)
    rw [hiff1]
    constructor
    · intro hall i hi1 hi2
      have hmask := hall i hi1 hi2
      have hrew : ∀ mask : Fin (2 ^ m),
          let A := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 1) % k))).foldl xor false
          let B := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && deltaBit d s (gen g) ((i + 2) % k))).foldl xor false
          let E := (List.ofFn (fun g : Fin m => mask.val.testBit g.val && eBit d s t (gen g) i)).foldl xor false
          xor (y.testBit i) (xor (!(xor (y.testBit ((i + 1) % k)) A) && xor (y.testBit ((i + 2) % k)) B)
            (xor (baseOutBit t base c i) E)) = false := by
        intro mask
        dsimp only
        rw [← run_testBit_via_y hk d s t base gen c u mask hi2]
        exact hmask mask
      exact (all_masks_bit_iff
        (fun g => deltaBit d s (gen g) ((i + 1) % k))
        (fun g => deltaBit d s (gen g) ((i + 2) % k))
        (fun g => eBit d s t (gen g) i)
        (y.testBit i) (y.testBit ((i + 1) % k)) (y.testBit ((i + 2) % k)) (baseOutBit t base c i)).mp hrew
    · intro hall i hi1 hi2 mask
      have ha := hall i hi1 hi2
      rw [run_testBit_via_y hk d s t base gen c u mask hi2]
      exact (all_masks_bit_iff
        (fun g => deltaBit d s (gen g) ((i + 1) % k))
        (fun g => deltaBit d s (gen g) ((i + 2) % k))
        (fun g => eBit d s t (gen g) i)
        (y.testBit i) (y.testBit ((i + 1) % k)) (y.testBit ((i + 2) % k)) (baseOutBit t base c i)).mpr ha mask
  have hwrap1 : ∀ (f : Fin k → Bool) (t0 t1 : Bool) (n : Nat),
      f ⟨0, hk⟩ = t0 →
      (∀ j, k - n ≤ j → ∀ hj : j < k, f ⟨j, hj⟩ = tailSeq d s t base gen c t0 t1 j) →
      ∀ j, k - (n + 1) ≤ j → j < k →
        f ⟨(j + 1) % k, Nat.mod_lt _ hk⟩ = tailSeq d s t base gen c t0 t1 (j + 1) := by
    intro f t0 t1 n hf0 hprev j hj1 hj2
    by_cases h1k : j + 1 < k
    · have hfin : (⟨(j + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨j + 1, h1k⟩ :=
        Fin.ext (Nat.mod_eq_of_lt h1k)
      rw [hfin]
      exact hprev (j + 1) (by omega) h1k
    · have hjeq : j + 1 = k := by omega
      have hfin : (⟨(j + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨0, hk⟩ := by
        apply Fin.ext; dsimp only; rw [hjeq, Nat.mod_self]
      rw [hfin, hf0, hjeq]
      simp [tailSeq]
  have hwrap2 : ∀ (f : Fin k → Bool) (t0 t1 : Bool) (n : Nat),
      f ⟨0, hk⟩ = t0 →
      (if h1 : 1 < k then f ⟨1, h1⟩ else f ⟨0, hk⟩) = t1 →
      (∀ j, k - n ≤ j → ∀ hj : j < k, f ⟨j, hj⟩ = tailSeq d s t base gen c t0 t1 j) →
      ∀ j, k - (n + 1) ≤ j → j < k →
        f ⟨(j + 2) % k, Nat.mod_lt _ hk⟩ = tailSeq d s t base gen c t0 t1 (j + 2) := by
    intro f t0 t1 n hf0 hf1 hprev j hj1 hj2
    by_cases h2k : j + 2 < k
    · have hfin : (⟨(j + 2) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨j + 2, h2k⟩ :=
        Fin.ext (Nat.mod_eq_of_lt h2k)
      rw [hfin]
      exact hprev (j + 2) (by omega) h2k
    · by_cases h2eq : j + 2 = k
      · have hfin : (⟨(j + 2) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨0, hk⟩ := by
          apply Fin.ext; dsimp only; rw [h2eq, Nat.mod_self]
        rw [hfin, hf0, h2eq]
        simp [tailSeq]
      · have hjeq : j + 2 = k + 1 := by omega
        have hne1 : ¬ (k + 1 < k) := by omega
        have hne2 : k + 1 ≠ k := by omega
        rw [hjeq]
        simp only [tailSeq, hne1, hne2, ite_false]
        by_cases hk1 : 1 < k
        · have hmod : (k + 1) % k = 1 := by
            rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hk1]
          have hfin : (⟨(k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨1, hk1⟩ := Fin.ext hmod
          rw [hfin]
          simpa [hk1] using hf1
        · have hk_eq : k = 1 := by omega
          have hfin : (⟨(k + 1) % k, Nat.mod_lt _ hk⟩ : Fin k) = ⟨0, hk⟩ := by
            apply Fin.ext; dsimp only; rw [hk_eq]
          rw [hfin]
          simpa [hk1] using hf1
  have hseq_from_Py : ∀ (f : Fin k → Bool), P_y f →
      let t0 := f ⟨0, hk⟩
      let t1 := if h1 : 1 < k then f ⟨1, h1⟩ else f ⟨0, hk⟩
      ∀ i, k - h ≤ i → ∀ hi : i < k, f ⟨i, hi⟩ = tailSeq d s t base gen c t0 t1 i := by
    intro f hf t0 t1
    have hdown : ∀ n, n ≤ h → ∀ j, k - n ≤ j → ∀ hj : j < k, f ⟨j, hj⟩ = tailSeq d s t base gen c t0 t1 j := by
      intro n
      induction n with
      | zero => intro _ j hj1 hj2; omega
      | succ n ih =>
        intro hn j hj1 hj2
        by_cases hgt : k - n ≤ j
        · exact ih (by omega) j hgt hj2
        · have hrec := (hf j (by omega) hj2).2
          have h1 := hwrap1 f t0 t1 n rfl (ih (by omega)) j (by omega) hj2
          have h2 := hwrap2 f t0 t1 n rfl rfl (ih (by omega)) j (by omega) hj2
          rw [hrec, h1, h2, ← tailSeq_rec d s t base gen c t0 t1 hj2]
    exact hdown h (le_refl h)
  have hE2 : { f : Fin k → Bool // P_y f } ≃
      { p : Bool × Bool // validTail h d s t base gen c p.1 p.2 = true } × (Fin (k - (h + 2)) → Bool) := by
    let toF : { f : Fin k → Bool // P_y f } →
        { p : Bool × Bool // validTail h d s t base gen c p.1 p.2 = true } × (Fin (k - (h + 2)) → Bool) :=
      fun ⟨f, hf⟩ =>
        let t0 := f ⟨0, hk⟩
        let t1 := if h1 : 1 < k then f ⟨1, h1⟩ else f ⟨0, hk⟩
        let free : Fin (k - (h + 2)) → Bool := fun j => f ⟨j.val + 2, by omega⟩
        have hseq_eq := hseq_from_Py f hf
        have hvalid : validTail h d s t base gen c t0 t1 = true := by
          have hok : (tailRun d s t base gen c t0 t1 h).ok = true := by
            rw [tailRun_ok_iff d s t base gen c t0 t1 h hh]
            refine ⟨?_, ?_⟩
            · by_cases hk1 : k = 1 <;> simp [hk1, t0, t1]
            · intro i hi1 hi2
              have hbi := (hf i hi1 hi2).1
              have h1 := hwrap1 f t0 t1 h rfl hseq_eq i (by omega) hi2
              have h2 := hwrap2 f t0 t1 h rfl rfl hseq_eq i (by omega) hi2
              rw [h1, h2] at hbi
              exact hbi
          rcases tailRun_b1_b2 d s t base gen c t0 t1 h hh with ⟨hb1, hb2⟩
          unfold validTail
          dsimp only
          split_ifs with hhk hhk1
          · simp only [Bool.and_eq_true, beq_iff_eq]
            refine ⟨⟨hok, ?_⟩, ?_⟩
            · rw [hb1, hhk, Nat.sub_self]
              exact (hseq_eq 0 (by omega) hk).symm
            · rw [hb2, hhk, Nat.sub_self, Nat.zero_add]
              by_cases hk1 : 1 < k
              · have hs1 := hseq_eq 1 (by omega) hk1
                dsimp only [t0, t1] at hs1 ⊢
                simp only [hk1, dite_true] at hs1 ⊢
                exact hs1.symm
              · have hk_eq : k = 1 := by omega
                have hnot1 : ¬ (1 < k) := hk1
                dsimp only [t0, t1]
                simp [tailSeq, hk_eq]
          · simp only [Bool.and_eq_true, beq_iff_eq]
            refine ⟨hok, ?_⟩
            rw [hb1]
            have hkh : k - h = 1 := by omega
            rw [hkh]
            by_cases hk1 : 1 < k
            · have hs1 := hseq_eq 1 (by omega) hk1
              dsimp only [t0, t1] at hs1 ⊢
              simp only [hk1, dite_true] at hs1 ⊢
              exact hs1.symm
            · have hk_eq : k = 1 := by omega
              dsimp only [t0, t1]
              simp [tailSeq, hk_eq]
          · exact hok
        (⟨(t0, t1), hvalid⟩, free)
    let fromF : { p : Bool × Bool // validTail h d s t base gen c p.1 p.2 = true } × (Fin (k - (h + 2)) → Bool) →
        { f : Fin k → Bool // P_y f } :=
      fun ⟨⟨⟨t0, t1⟩, hvalid⟩, free⟩ =>
        let f : Fin k → Bool := fun idx =>
          if hge : k - h ≤ idx.val then tailSeq d s t base gen c t0 t1 idx.val
          else if h0 : idx.val = 0 then t0
          else if h1 : idx.val = 1 then t1
          else free ⟨idx.val - 2, by omega⟩
        have hok_st : (tailRun d s t base gen c t0 t1 h).ok = true := by
          unfold validTail at hvalid
          dsimp only at hvalid
          split_ifs at hvalid <;> simp_all
        have hok_all := (tailRun_ok_iff d s t base gen c t0 t1 h hh).mp hok_st
        have hbb := tailRun_b1_b2 d s t base gen c t0 t1 h hh
        have hf0 : f ⟨0, hk⟩ = t0 := by
          dsimp only [f]
          by_cases h0 : k - h ≤ 0
          · simp only [h0, dite_true]
            have hhk : h = k := by omega
            unfold validTail at hvalid
            simp only [hhk, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
            have hb1 := hbb.1
            rw [hhk, Nat.sub_self] at hb1
            rw [← hb1]
            exact hvalid.1.2
          · simp only [h0, dite_false, dite_true]
        have hf1 : (if h1 : 1 < k then f ⟨1, h1⟩ else f ⟨0, hk⟩) = t1 := by
          by_cases hk1 : 1 < k
          · simp only [hk1, dite_true, f]
            by_cases h1 : k - h ≤ 1
            · simp only [h1, dite_true]
              by_cases hhk : h = k
              · unfold validTail at hvalid
                simp only [hhk, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
                have hb2 := hbb.2
                rw [hhk, Nat.sub_self, Nat.zero_add] at hb2
                rw [← hb2]
                exact hvalid.2
              · have hhk1 : h + 1 = k := by omega
                unfold validTail at hvalid
                simp only [hhk, hhk1, ite_false, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
                have hb1 := hbb.1
                have hkh : k - h = 1 := by omega
                rw [hkh] at hb1
                rw [← hb1]
                exact hvalid.2
            · simp only [h1, dite_false, show (1 : Nat) ≠ 0 by decide, dite_true]
          · simp only [hk1, dite_false]
            have hk_eq : k = 1 := by omega
            have ht01 : t0 = t1 := by
              have h' := hok_all.1
              simp [hk_eq] at h'
              exact h'
            rw [hf0, ht01]
        have hf_seq : ∀ j, k - h ≤ j → ∀ hj : j < k, f ⟨j, hj⟩ = tailSeq d s t base gen c t0 t1 j := by
          intro j hj1 hj2
          dsimp only [f]
          simp [hj1]
        have hf_valid : P_y f := by
          intro i hi1 hi2
          have h1 := hwrap1 f t0 t1 h hf0 hf_seq i (by omega) hi2
          have h2 := hwrap2 f t0 t1 h hf0 hf1 hf_seq i (by omega) hi2
          rw [h1, h2]
          refine ⟨hok_all.2 i hi1 hi2, ?_⟩
          simp only [f, hi1, dite_true]
          exact tailSeq_rec d s t base gen c t0 t1 hi2
        ⟨f, hf_valid⟩
    refine ⟨toF, fromF, ?_, ?_⟩
    · rintro ⟨f, hf⟩
      apply Subtype.ext
      funext idx
      dsimp only [toF, fromF]
      by_cases hge : k - h ≤ idx.val
      · simp only [hge, dite_true]
        exact (hseq_from_Py f hf idx.val hge idx.isLt).symm
      · simp only [hge, dite_false]
        by_cases h0 : idx.val = 0
        · simp only [h0, dite_true]
          congr 1; exact Fin.ext h0.symm
        · simp only [h0, dite_false]
          by_cases h1 : idx.val = 1
          · simp only [h1, dite_true]
            have hk1 : 1 < k := by omega
            simp only [hk1, dite_true]
            congr 1; exact Fin.ext h1.symm
          · simp only [h1, dite_false]
            congr 1; apply Fin.ext; dsimp only; omega
    · rintro ⟨⟨⟨t0, t1⟩, hvalid⟩, free⟩
      dsimp only [toF, fromF]
      have hok_st : (tailRun d s t base gen c t0 t1 h).ok = true := by
        unfold validTail at hvalid; dsimp only at hvalid; split_ifs at hvalid <;> simp_all
      have hok_all := (tailRun_ok_iff d s t base gen c t0 t1 h hh).mp hok_st
      have hbb := tailRun_b1_b2 d s t base gen c t0 t1 h hh
      apply Prod.ext
      · apply Subtype.ext
        apply Prod.ext
        · dsimp only
          by_cases h0 : k - h ≤ 0
          · simp only [h0, dite_true]
            have hhk : h = k := by omega
            unfold validTail at hvalid
            simp only [hhk, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
            have hb1 := hbb.1
            rw [hhk, Nat.sub_self] at hb1
            rw [← hb1]
            exact hvalid.1.2
          · simp only [h0, dite_false, dite_true]
        · dsimp only
          by_cases hk1 : 1 < k
          · simp only [hk1, dite_true]
            by_cases h1 : k - h ≤ 1
            · simp only [h1, dite_true]
              by_cases hhk : h = k
              · unfold validTail at hvalid
                simp only [hhk, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
                have hb2 := hbb.2
                rw [hhk, Nat.sub_self, Nat.zero_add] at hb2
                rw [← hb2]
                exact hvalid.2
              · have hhk1 : h + 1 = k := by omega
                unfold validTail at hvalid
                simp only [hhk, hhk1, ite_false, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
                have hb1 := hbb.1
                have hkh : k - h = 1 := by omega
                rw [hkh] at hb1
                rw [← hb1]
                exact hvalid.2
            · simp only [h1, dite_false, show (1 : Nat) ≠ 0 by decide, dite_true]
          · simp only [hk1, dite_false]
            have hk_eq : k = 1 := by omega
            have ht01 : t0 = t1 := by
              have h' := hok_all.1
              simp [hk_eq] at h'
              exact h'
            by_cases h0 : k - h ≤ 0
            · simp only [h0, dite_true]
              have hhk : h = k := by omega
              unfold validTail at hvalid
              simp only [hhk, ite_true, Bool.and_eq_true, beq_iff_eq] at hvalid
              have hb1 := hbb.1
              rw [hhk, Nat.sub_self] at hb1
              rw [← hb1, hvalid.1.2, ht01]
            · simp only [h0, dite_false, dite_true, ht01]
      · funext j
        dsimp only
        have h1 : ¬ (k - h ≤ j.val + 2) := by omega
        have h2 : j.val + 2 ≠ 0 := by omega
        have h3 : j.val + 2 ≠ 1 := by omega
        simp only [h1, h2, h3, dite_false, Nat.add_sub_cancel]
  rw [Nat.card_congr (hE1.trans hE2), Nat.card_prod, nat_card_validTail, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.mul_comm]

def wireVal (gs : List Gate) (x : List Bool) (w : Nat) : Bool :=
  (({ gates := gs, output := 0 } : Circuit).wires x).getD w false

def Good (n : Nat) (gs : List Gate) : Prop :=
  FanInTwo ⟨gs, 0⟩ ∧ ReadsBack n ⟨gs, 0⟩

def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ rest, gs2 = gs1 ++ rest

lemma extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

lemma extends_trans {g1 g2 g3 : List Gate} (h12 : Extends g1 g2) (h23 : Extends g2 g3) :
    Extends g1 g3 := by
  rcases h12 with ⟨r1, rfl⟩
  rcases h23 with ⟨r2, rfl⟩
  exact ⟨r1 ++ r2, by rw [List.append_assoc]⟩

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) {i : Nat} (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun idx => w.getD idx false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (acc ++ [g.op.eval (g.inputs.map fun idx => acc.getD idx false)]).length := by
      simp; omega
    rw [ih _ hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wireVal_extends {gs1 gs2 : List Gate} {x : List Bool} {w : Nat}
    (hext : Extends gs1 gs2) (hw : w < x.length + gs1.length) :
    wireVal gs2 x w = wireVal gs1 x w := by
  rcases hext with ⟨rest, rfl⟩
  unfold wireVal Circuit.wires
  rw [List.foldl_append]
  apply foldl_wires_getD_lt
  rw [foldl_wires_len]
  exact hw

lemma wireVal_input (gs : List Gate) (x : List Bool) {i : Nat} (hi : i < x.length) :
    wireVal gs x i = x.getD i false :=
  foldl_wires_getD_lt gs x hi

def emitGate (n : Nat) (gs : List Gate) (op : GateOp) (ins : List Nat) : List Gate × Nat :=
  (gs ++ [⟨op, ins⟩], n + gs.length)

lemma emitGate_good {n : Nat} {gs : List Gate} {op : GateOp} {ins : List Nat}
    (hg : Good n gs)
    (hop : op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hilen : ins.length ≤ 2)
    (hins : ∀ i ∈ ins, i < n + gs.length) :
    Good n (emitGate n gs op ins).1 := by
  rcases hg with ⟨hfan, hback⟩
  constructor
  · intro g hgmem
    simp only [emitGate, List.mem_append, List.mem_singleton] at hgmem
    rcases hgmem with h1 | rfl
    · exact hfan g h1
    · exact ⟨hop, hilen⟩
  · intro j hj i hi
    simp only [emitGate, List.length_append, List.length_singleton] at hj
    unfold gateAt at hi
    simp only [emitGate, List.getD_eq_getElem?_getD] at hi
    by_cases hlt : j < gs.length
    · rw [List.getElem?_append_left hlt] at hi
      have hb := hback j hlt i
      unfold gateAt at hb
      simp only [List.getD_eq_getElem?_getD] at hb
      exact hb hi
    · have heq : j = gs.length := by omega
      subst heq
      rw [List.getElem?_append_right (le_refl _)] at hi
      simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some] at hi
      exact hins i hi

lemma emitGate_extends (n : Nat) (gs : List Gate) (op : GateOp) (ins : List Nat) :
    Extends gs (emitGate n gs op ins).1 :=
  ⟨[⟨op, ins⟩], rfl⟩

lemma emitGate_len (n : Nat) (gs : List Gate) (op : GateOp) (ins : List Nat) :
    (emitGate n gs op ins).1.length = gs.length + 1 := by
  simp [emitGate]

lemma emitGate_lt (n : Nat) (gs : List Gate) (op : GateOp) (ins : List Nat) :
    (emitGate n gs op ins).2 < n + (emitGate n gs op ins).1.length := by
  simp [emitGate]

lemma emitGate_val {n : Nat} (gs : List Gate) (op : GateOp) (ins : List Nat)
    (x : List Bool) (hx : x.length = n) :
    wireVal (emitGate n gs op ins).1 x (emitGate n gs op ins).2 =
      op.eval (ins.map (wireVal gs x)) := by
  unfold wireVal emitGate Circuit.wires
  dsimp only
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  set prev := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
  have hlen : prev.length = n + gs.length := by
    rw [foldl_wires_len, hx]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega : prev.length ≤ n + gs.length)]
  simp [hlen]

def emitFalse (n : Nat) (gs : List Gate) : List Gate × Nat :=
  emitGate n gs GateOp.or []

def emitTrue (n : Nat) (gs : List Gate) : List Gate × Nat :=
  emitGate n gs GateOp.and []

def emitNot (n : Nat) (gs : List Gate) (a : Nat) : List Gate × Nat :=
  emitGate n gs GateOp.not [a]

def emitAnd (n : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate n gs GateOp.and [a, b]

def emitOr (n : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  emitGate n gs GateOp.or [a, b]

lemma wireVal_of_ext {gs1 gs2 : List Gate} {x : List Bool} {n w : Nat} {v : Bool}
    (hx : x.length = n) (he : Extends gs1 gs2) (hw : w < n + gs1.length)
    (hv : wireVal gs1 x w = v) : wireVal gs2 x w = v := by
  rw [wireVal_extends he (by rw [hx]; exact hw), hv]

lemma ext_len {gs1 gs2 : List Gate} (he : Extends gs1 gs2) : gs1.length ≤ gs2.length := by
  rcases he with ⟨r, rfl⟩
  simp

lemma emitFalse_spec {n : Nat} {gs : List Gate} (hg : Good n gs) (x : List Bool) (hx : x.length = n) :
    let r := emitFalse n gs
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = false := by
  unfold emitFalse
  refine ⟨emitGate_good hg (by simp) (by simp) (by simp),
    emitGate_extends _ _ _ _, emitGate_len _ _ _ _, emitGate_lt _ _ _ _, ?_⟩
  rw [emitGate_val _ _ _ x hx]; rfl

lemma emitTrue_spec {n : Nat} {gs : List Gate} (hg : Good n gs) (x : List Bool) (hx : x.length = n) :
    let r := emitTrue n gs
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = true := by
  unfold emitTrue
  refine ⟨emitGate_good hg (by simp) (by simp) (by simp),
    emitGate_extends _ _ _ _, emitGate_len _ _ _ _, emitGate_lt _ _ _ _, ?_⟩
  rw [emitGate_val _ _ _ x hx]; rfl

lemma emitNot_spec {n : Nat} {gs : List Gate} {a : Nat} (hg : Good n gs) (ha : a < n + gs.length)
    (x : List Bool) (hx : x.length = n) :
    let r := emitNot n gs a
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = !(wireVal gs x a) := by
  unfold emitNot
  refine ⟨emitGate_good hg (by simp) (by simp) (by simp [ha]),
    emitGate_extends _ _ _ _, emitGate_len _ _ _ _, emitGate_lt _ _ _ _, ?_⟩
  rw [emitGate_val _ _ _ x hx]; rfl

lemma emitAnd_spec {n : Nat} {gs : List Gate} {a b : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitAnd n gs a b
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = (wireVal gs x a && wireVal gs x b) := by
  unfold emitAnd
  refine ⟨emitGate_good hg (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    emitGate_extends _ _ _ _, emitGate_len _ _ _ _, emitGate_lt _ _ _ _, ?_⟩
  rw [emitGate_val _ _ _ x hx]; simp [GateOp.eval]

lemma emitOr_spec {n : Nat} {gs : List Gate} {a b : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitOr n gs a b
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 1 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = (wireVal gs x a || wireVal gs x b) := by
  unfold emitOr
  refine ⟨emitGate_good hg (by simp) (by simp) (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    emitGate_extends _ _ _ _, emitGate_len _ _ _ _, emitGate_lt _ _ _ _, ?_⟩
  rw [emitGate_val _ _ _ x hx]; simp [GateOp.eval]

def emitXor (n : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  let (g1, wo) := emitOr n gs a b
  let (g2, wa) := emitAnd n g1 a b
  let (g3, wn) := emitNot n g2 wa
  emitAnd n g3 wo wn

lemma emitXor_spec {n : Nat} {gs : List Gate} {a b : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitXor n gs a b
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = xor (wireVal gs x a) (wireVal gs x b) := by
  dsimp only
  unfold emitXor
  rcases h1 : emitOr n gs a b with ⟨g1, wo⟩; dsimp only
  have q1 := emitOr_spec (a := a) (b := b) hg ha hb x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwo, hvo⟩
  rcases h2 : emitAnd n g1 a b with ⟨g2, wa⟩; dsimp only
  have q2 := emitAnd_spec (a := a) (b := b) hg1 (by omega) (by omega) x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwa, hva⟩
  rcases h3 : emitNot n g2 wa with ⟨g3, wn⟩; dsimp only
  have q3 := emitNot_spec (a := wa) hg2 hwa x hx; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwn, hvn⟩
  rcases h4 : emitAnd n g3 wo wn with ⟨g4, wr⟩; dsimp only
  have q4 := emitAnd_spec (a := wo) (b := wn) hg3 (by omega) hwn x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwr, hvr⟩
  refine ⟨hg4, extends_trans he1 (extends_trans he2 (extends_trans he3 he4)), by omega, hwr, ?_⟩
  rw [hvr, hvn, wireVal_of_ext hx (extends_trans he2 he3) hwo hvo, hva,
      wireVal_of_ext hx he1 ha rfl, wireVal_of_ext hx he1 hb rfl]
  cases wireVal gs x a <;> cases wireVal gs x b <;> rfl

def emitEq (n : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat :=
  let (g1, wx) := emitXor n gs a b
  emitNot n g1 wx

lemma emitEq_spec {n : Nat} {gs : List Gate} {a b : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitEq n gs a b
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 5 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = (wireVal gs x a == wireVal gs x b) := by
  dsimp only
  unfold emitEq
  rcases h1 : emitXor n gs a b with ⟨g1, wx⟩; dsimp only
  have q1 := emitXor_spec (a := a) (b := b) hg ha hb x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwx, hvx⟩
  rcases h2 : emitNot n g1 wx with ⟨g2, wr⟩; dsimp only
  have q2 := emitNot_spec (a := wx) hg1 hwx x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwr, hvr⟩
  refine ⟨hg2, extends_trans he1 he2, by omega, hwr, ?_⟩
  rw [hvr, hvx]
  cases wireVal gs x a <;> cases wireVal gs x b <;> rfl

def emitMux (n : Nat) (gs : List Gate) (sel v0 v1 : Nat) : List Gate × Nat :=
  let (g1, ns) := emitNot n gs sel
  let (g2, a) := emitAnd n g1 ns v0
  let (g3, b) := emitAnd n g2 sel v1
  emitOr n g3 a b

lemma emitMux_spec {n : Nat} {gs : List Gate} {sel v0 v1 : Nat} (hg : Good n gs)
    (hs : sel < n + gs.length) (h0 : v0 < n + gs.length) (h1 : v1 < n + gs.length)
    (x : List Bool) (hx : x.length = n) :
    let r := emitMux n gs sel v0 v1
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 4 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 = (if wireVal gs x sel then wireVal gs x v1 else wireVal gs x v0) := by
  dsimp only
  unfold emitMux
  rcases k1 : emitNot n gs sel with ⟨g1, ns⟩; dsimp only
  have q1 := emitNot_spec (a := sel) hg hs x hx; rw [k1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hns, hvns⟩
  rcases k2 : emitAnd n g1 ns v0 with ⟨g2, wa⟩; dsimp only
  have q2 := emitAnd_spec (a := ns) (b := v0) hg1 hns (by omega) x hx; rw [k2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwa, hva⟩
  rcases k3 : emitAnd n g2 sel v1 with ⟨g3, wb⟩; dsimp only
  have q3 := emitAnd_spec (a := sel) (b := v1) hg2 (by omega) (by omega) x hx; rw [k3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwb, hvb⟩
  rcases k4 : emitOr n g3 wa wb with ⟨g4, wr⟩; dsimp only
  have q4 := emitOr_spec (a := wa) (b := wb) hg3 (by omega) hwb x hx; rw [k4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwr, hvr⟩
  refine ⟨hg4, extends_trans he1 (extends_trans he2 (extends_trans he3 he4)), by omega, hwr, ?_⟩
  rw [hvr, wireVal_of_ext hx he3 hwa hva, hvns, wireVal_of_ext hx he1 h0 rfl,
      hvb, wireVal_of_ext hx (extends_trans he1 he2) hs rfl,
      wireVal_of_ext hx (extends_trans he1 he2) h1 rfl]
  cases wireVal gs x sel <;> cases wireVal gs x v0 <;> cases wireVal gs x v1 <;> rfl

def emitMux4 (n : Nat) (gs : List Gate) (s1 s2 v00 v01 v10 v11 : Nat) : List Gate × Nat :=
  let (g1, m0) := emitMux n gs s2 v00 v01
  let (g2, m1) := emitMux n g1 s2 v10 v11
  emitMux n g2 s1 m0 m1

lemma emitMux4_spec {n : Nat} {gs : List Gate} {s1 s2 v00 v01 v10 v11 : Nat} (hg : Good n gs)
    (hs1 : s1 < n + gs.length) (hs2 : s2 < n + gs.length)
    (h00 : v00 < n + gs.length) (h01 : v01 < n + gs.length)
    (h10 : v10 < n + gs.length) (h11 : v11 < n + gs.length)
    (x : List Bool) (hx : x.length = n) :
    let r := emitMux4 n gs s1 s2 v00 v01 v10 v11
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 12 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 =
        (match wireVal gs x s1, wireVal gs x s2 with
         | false, false => wireVal gs x v00
         | false, true => wireVal gs x v01
         | true, false => wireVal gs x v10
         | true, true => wireVal gs x v11) := by
  dsimp only
  unfold emitMux4
  rcases k1 : emitMux n gs s2 v00 v01 with ⟨g1, m0⟩; dsimp only
  have q1 := emitMux_spec (sel := s2) (v0 := v00) (v1 := v01) hg hs2 h00 h01 x hx; rw [k1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hm0, hvm0⟩
  rcases k2 : emitMux n g1 s2 v10 v11 with ⟨g2, m1⟩; dsimp only
  have q2 := emitMux_spec (sel := s2) (v0 := v10) (v1 := v11) hg1 (by omega) (by omega) (by omega) x hx; rw [k2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hm1, hvm1⟩
  rcases k3 : emitMux n g2 s1 m0 m1 with ⟨g3, wr⟩; dsimp only
  have q3 := emitMux_spec (sel := s1) (v0 := m0) (v1 := m1) hg2 (by omega) (by omega) hm1 x hx; rw [k3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwr, hvr⟩
  refine ⟨hg3, extends_trans he1 (extends_trans he2 he3), by omega, hwr, ?_⟩
  rw [hvr, wireVal_of_ext hx (extends_trans he1 he2) hs1 rfl,
      wireVal_of_ext hx he2 hm0 hvm0, hvm1,
      wireVal_of_ext hx he1 hs2 rfl, wireVal_of_ext hx he1 h10 rfl, wireVal_of_ext hx he1 h11 rfl]
  cases wireVal gs x s1 <;> cases wireVal gs x s2 <;> rfl

def emitHA (n : Nat) (gs : List Gate) (a b : Nat) : List Gate × Nat × Nat :=
  let (g1, s) := emitXor n gs a b
  let (g2, c) := emitAnd n g1 a b
  (g2, s, c)

lemma emitHA_spec {n : Nat} {gs : List Gate} {a b : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitHA n gs a b
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 5 ∧
      r.2.1 < n + r.1.length ∧ r.2.2 < n + r.1.length ∧
      wireVal r.1 x r.2.1 = xor (wireVal gs x a) (wireVal gs x b) ∧
      wireVal r.1 x r.2.2 = (wireVal gs x a && wireVal gs x b) := by
  dsimp only
  unfold emitHA
  rcases k1 : emitXor n gs a b with ⟨g1, ws⟩; dsimp only
  have q1 := emitXor_spec (a := a) (b := b) hg ha hb x hx; rw [k1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hws, hvs⟩
  rcases k2 : emitAnd n g1 a b with ⟨g2, wc⟩; dsimp only
  have q2 := emitAnd_spec (a := a) (b := b) hg1 (by omega) (by omega) x hx; rw [k2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwc, hvc⟩
  refine ⟨hg2, extends_trans he1 he2, by omega, by omega, hwc,
    wireVal_of_ext hx he2 hws hvs, ?_⟩
  rw [hvc, wireVal_of_ext hx he1 ha rfl, wireVal_of_ext hx he1 hb rfl]

def emitFA (n : Nat) (gs : List Gate) (a b c : Nat) : List Gate × Nat × Nat :=
  let (g1, s1, c1) := emitHA n gs a b
  let (g2, s2, c2) := emitHA n g1 s1 c
  let (g3, cout) := emitOr n g2 c1 c2
  (g3, s2, cout)

lemma emitFA_spec {n : Nat} {gs : List Gate} {a b c : Nat} (hg : Good n gs)
    (ha : a < n + gs.length) (hb : b < n + gs.length) (hc : c < n + gs.length)
    (x : List Bool) (hx : x.length = n) :
    let r := emitFA n gs a b c
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 11 ∧
      r.2.1 < n + r.1.length ∧ r.2.2 < n + r.1.length ∧
      wireVal r.1 x r.2.1 = xor (xor (wireVal gs x a) (wireVal gs x b)) (wireVal gs x c) ∧
      wireVal r.1 x r.2.2 =
        ((wireVal gs x a && wireVal gs x b) ||
         (xor (wireVal gs x a) (wireVal gs x b) && wireVal gs x c)) := by
  dsimp only
  unfold emitFA
  rcases k1 : emitHA n gs a b with ⟨g1, s1, c1⟩; dsimp only
  have q1 := emitHA_spec (a := a) (b := b) hg ha hb x hx; rw [k1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hs1, hc1, hvs1, hvc1⟩
  rcases k2 : emitHA n g1 s1 c with ⟨g2, s2, c2⟩; dsimp only
  have q2 := emitHA_spec (a := s1) (b := c) hg1 hs1 (by omega) x hx; rw [k2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hs2, hc2, hvs2, hvc2⟩
  rcases k3 : emitOr n g2 c1 c2 with ⟨g3, cout⟩; dsimp only
  have q3 := emitOr_spec (a := c1) (b := c2) hg2 (by omega) hc2 x hx; rw [k3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hco, hvco⟩
  refine ⟨hg3, extends_trans he1 (extends_trans he2 he3), by omega, by omega, hco, ?_, ?_⟩
  · rw [wireVal_of_ext hx he3 hs2 hvs2, hvs1, wireVal_of_ext hx he1 hc rfl]
  · rw [hvco, wireVal_of_ext hx he2 hc1 hvc1, hvc2, hvs1, wireVal_of_ext hx he1 hc rfl]

def pop4Spec (b0 b1 b2 b3 : Bool) : Bool × Bool × Bool :=
  let x0 := xor b0 b1
  let y0 := b0 && b1
  let x1 := xor b2 b3
  let y1 := b2 && b3
  let s0 := xor x0 x1
  let cm := x0 && x1
  let u := xor y0 y1
  let v1 := y0 && y1
  let s1 := xor u cm
  let v2 := u && cm
  (s0, s1, v1 || v2)

lemma pop4Spec_val (b0 b1 b2 b3 : Bool) :
    let (s0, s1, s2) := pop4Spec b0 b1 b2 b3
    s0.toNat + 2 * s1.toNat + 4 * s2.toNat =
      b0.toNat + b1.toNat + b2.toNat + b3.toNat := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> decide

def emitPop4 (n : Nat) (gs : List Gate) (b0 b1 b2 b3 : Nat) : List Gate × Nat × Nat × Nat :=
  let (g1, x0, y0) := emitHA n gs b0 b1
  let (g2, x1, y1) := emitHA n g1 b2 b3
  let (g3, s0, cm) := emitHA n g2 x0 x1
  let (g4, s1, s2) := emitFA n g3 y0 y1 cm
  (g4, s0, s1, s2)

lemma emitPop4_spec {n : Nat} {gs : List Gate} {b0 b1 b2 b3 : Nat} (hg : Good n gs)
    (h0 : b0 < n + gs.length) (h1 : b1 < n + gs.length)
    (h2 : b2 < n + gs.length) (h3 : b3 < n + gs.length) (x : List Bool) (hx : x.length = n) :
    let r := emitPop4 n gs b0 b1 b2 b3
    let sp := pop4Spec (wireVal gs x b0) (wireVal gs x b1) (wireVal gs x b2) (wireVal gs x b3)
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 26 ∧
      r.2.1 < n + r.1.length ∧ r.2.2.1 < n + r.1.length ∧ r.2.2.2 < n + r.1.length ∧
      wireVal r.1 x r.2.1 = sp.1 ∧ wireVal r.1 x r.2.2.1 = sp.2.1 ∧ wireVal r.1 x r.2.2.2 = sp.2.2 := by
  dsimp only
  unfold emitPop4
  rcases k1 : emitHA n gs b0 b1 with ⟨g1, x0, y0⟩; dsimp only
  have q1 := emitHA_spec (a := b0) (b := b1) hg h0 h1 x hx; rw [k1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hx0, hy0, hvx0, hvy0⟩
  rcases k2 : emitHA n g1 b2 b3 with ⟨g2, x1, y1⟩; dsimp only
  have q2 := emitHA_spec (a := b2) (b := b3) hg1 (by omega) (by omega) x hx; rw [k2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hx1, hy1, hvx1, hvy1⟩
  rcases k3 : emitHA n g2 x0 x1 with ⟨g3, s0, cm⟩; dsimp only
  have q3 := emitHA_spec (a := x0) (b := x1) hg2 (by omega) hx1 x hx; rw [k3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hs0, hcm, hvs0, hvcm⟩
  rcases k4 : emitFA n g3 y0 y1 cm with ⟨g4, s1, s2⟩; dsimp only
  have q4 := emitFA_spec (a := y0) (b := y1) (c := cm) hg3 (by omega) (by omega) hcm x hx; rw [k4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hs1, hs2, hvs1, hvs2⟩
  have vx1 : wireVal g2 x x1 = xor (wireVal gs x b2) (wireVal gs x b3) := by
    rw [hvx1, wireVal_of_ext hx he1 h2 rfl, wireVal_of_ext hx he1 h3 rfl]
  have vy1 : wireVal g2 x y1 = (wireVal gs x b2 && wireVal gs x b3) := by
    rw [hvy1, wireVal_of_ext hx he1 h2 rfl, wireVal_of_ext hx he1 h3 rfl]
  have vs0 : wireVal g3 x s0 = xor (xor (wireVal gs x b0) (wireVal gs x b1)) (xor (wireVal gs x b2) (wireVal gs x b3)) := by
    rw [hvs0, wireVal_of_ext hx he2 hx0 hvx0, vx1]
  have vcm : wireVal g3 x cm = (xor (wireVal gs x b0) (wireVal gs x b1) && xor (wireVal gs x b2) (wireVal gs x b3)) := by
    rw [hvcm, wireVal_of_ext hx he2 hx0 hvx0, vx1]
  refine ⟨hg4, extends_trans he1 (extends_trans he2 (extends_trans he3 he4)),
    by omega, by omega, hs1, hs2, ?_, ?_, ?_⟩
  · rw [wireVal_of_ext hx he4 hs0 vs0]; rfl
  · rw [hvs1, wireVal_of_ext hx (extends_trans he2 he3) hy0 hvy0, wireVal_of_ext hx he3 hy1 vy1, vcm]; rfl
  · rw [hvs2, wireVal_of_ext hx (extends_trans he2 he3) hy0 hvy0, wireVal_of_ext hx he3 hy1 vy1, vcm]; rfl

def mul3Spec (r0 r1 r2 c0 c1 c2 : Bool) : Fin 5 → Bool :=
  let p00 := r0 && c0
  let p01 := r0 && c1
  let p02 := r0 && c2
  let p10 := r1 && c0
  let p11 := r1 && c1
  let p12 := r1 && c2
  let p20 := r2 && c0
  let p21 := r2 && c1
  let p22 := r2 && c2
  let z1 := xor p01 p10
  let k1 := p01 && p10
  let w2 := xor (xor p02 p11) p20
  let c2a := (p02 && p11) || (xor p02 p11 && p20)
  let z2 := xor w2 k1
  let c2b := w2 && k1
  let w3 := xor (xor p12 p21) c2a
  let c3a := (p12 && p21) || (xor p12 p21 && c2a)
  let z3 := xor w3 c2b
  let c3b := w3 && c2b
  let z4 := xor (xor p22 c3a) c3b
  fun i => match i.val with
    | 0 => p00
    | 1 => z1
    | 2 => z2
    | 3 => z3
    | _ => z4

lemma mul3Spec_testBit (r0 r1 r2 c0 c1 c2 : Bool)
    (hr : r0.toNat + 2 * r1.toNat + 4 * r2.toNat ≤ 4)
    (hc : c0.toNat + 2 * c1.toNat + 4 * c2.toNat ≤ 4)
    (i : Fin 5) :
    mul3Spec r0 r1 r2 c0 c1 c2 i =
      ((r0.toNat + 2 * r1.toNat + 4 * r2.toNat) * (c0.toNat + 2 * c1.toNat + 4 * c2.toNat)).testBit i.val := by
  fin_cases i <;>
  cases r0 <;> cases r1 <;> cases r2 <;> cases c0 <;> cases c1 <;> cases c2 <;>
  first | decide | (simp at hr hc; omega)

def emitMul3 (n : Nat) (gs : List Gate) (r0 r1 r2 c0 c1 c2 : Nat) : List Gate × (Fin 5 → Nat) :=
  let (g1, p00) := emitAnd n gs r0 c0
  let (g2, p01) := emitAnd n g1 r0 c1
  let (g3, p02) := emitAnd n g2 r0 c2
  let (g4, p10) := emitAnd n g3 r1 c0
  let (g5, p11) := emitAnd n g4 r1 c1
  let (g6, p12) := emitAnd n g5 r1 c2
  let (g7, p20) := emitAnd n g6 r2 c0
  let (g8, p21) := emitAnd n g7 r2 c1
  let (g9, p22) := emitAnd n g8 r2 c2
  let (g10, z1, k1) := emitHA n g9 p01 p10
  let (g11, w2, c2a) := emitFA n g10 p02 p11 p20
  let (g12, z2, c2b) := emitHA n g11 w2 k1
  let (g13, w3, c3a) := emitFA n g12 p12 p21 c2a
  let (g14, z3, c3b) := emitHA n g13 w3 c2b
  let (g15, z4, _) := emitFA n g14 p22 c3a c3b
  (g15, fun i => match i.val with
    | 0 => p00
    | 1 => z1
    | 2 => z2
    | 3 => z3
    | _ => z4)

lemma emitMul3_spec {n : Nat} {gs : List Gate} {r0 r1 r2 c0 c1 c2 : Nat} (hg : Good n gs)
    (hr0 : r0 < n + gs.length) (hr1 : r1 < n + gs.length) (hr2 : r2 < n + gs.length)
    (hc0 : c0 < n + gs.length) (hc1 : c1 < n + gs.length) (hc2 : c2 < n + gs.length)
    (x : List Bool) (hx : x.length = n) :
    let res := emitMul3 n gs r0 r1 r2 c0 c1 c2
    Good n res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 57 ∧
      (∀ i : Fin 5, res.2 i < n + res.1.length) ∧
      (∀ i : Fin 5, wireVal res.1 x (res.2 i) =
        mul3Spec (wireVal gs x r0) (wireVal gs x r1) (wireVal gs x r2)
          (wireVal gs x c0) (wireVal gs x c1) (wireVal gs x c2) i) := by
  dsimp only
  unfold emitMul3
  rcases h1 : emitAnd n gs r0 c0 with ⟨g1, p00⟩; dsimp only
  have q1 := emitAnd_spec (a := r0) (b := c0) hg hr0 hc0 x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hp00, hvp00⟩
  rcases h2 : emitAnd n g1 r0 c1 with ⟨g2, p01⟩; dsimp only
  have q2 := emitAnd_spec (a := r0) (b := c1) hg1 (by omega) (by omega) x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hp01, hvp01⟩
  rcases h3 : emitAnd n g2 r0 c2 with ⟨g3, p02⟩; dsimp only
  have q3 := emitAnd_spec (a := r0) (b := c2) hg2 (by omega) (by omega) x hx; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hp02, hvp02⟩
  rcases h4 : emitAnd n g3 r1 c0 with ⟨g4, p10⟩; dsimp only
  have q4 := emitAnd_spec (a := r1) (b := c0) hg3 (by omega) (by omega) x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hp10, hvp10⟩
  rcases h5 : emitAnd n g4 r1 c1 with ⟨g5, p11⟩; dsimp only
  have q5 := emitAnd_spec (a := r1) (b := c1) hg4 (by omega) (by omega) x hx; rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hp11, hvp11⟩
  rcases h6 : emitAnd n g5 r1 c2 with ⟨g6, p12⟩; dsimp only
  have q6 := emitAnd_spec (a := r1) (b := c2) hg5 (by omega) (by omega) x hx; rw [h6] at q6; dsimp only at q6; rcases q6 with ⟨hg6, he6, hl6, hp12, hvp12⟩
  rcases h7 : emitAnd n g6 r2 c0 with ⟨g7, p20⟩; dsimp only
  have q7 := emitAnd_spec (a := r2) (b := c0) hg6 (by omega) (by omega) x hx; rw [h7] at q7; dsimp only at q7; rcases q7 with ⟨hg7, he7, hl7, hp20, hvp20⟩
  rcases h8 : emitAnd n g7 r2 c1 with ⟨g8, p21⟩; dsimp only
  have q8 := emitAnd_spec (a := r2) (b := c1) hg7 (by omega) (by omega) x hx; rw [h8] at q8; dsimp only at q8; rcases q8 with ⟨hg8, he8, hl8, hp21, hvp21⟩
  rcases h9 : emitAnd n g8 r2 c2 with ⟨g9, p22⟩; dsimp only
  have q9 := emitAnd_spec (a := r2) (b := c2) hg8 (by omega) (by omega) x hx; rw [h9] at q9; dsimp only at q9; rcases q9 with ⟨hg9, he9, hl9, hp22, hvp22⟩
  rcases h10 : emitHA n g9 p01 p10 with ⟨g10, z1, k1⟩; dsimp only
  have q10 := emitHA_spec (a := p01) (b := p10) hg9 (by omega) (by omega) x hx; rw [h10] at q10; dsimp only at q10; rcases q10 with ⟨hg10, he10, hl10, hz1, hk1, hvz1, hvk1⟩
  rcases h11 : emitFA n g10 p02 p11 p20 with ⟨g11, w2, c2a⟩; dsimp only
  have q11 := emitFA_spec (a := p02) (b := p11) (c := p20) hg10 (by omega) (by omega) (by omega) x hx; rw [h11] at q11; dsimp only at q11; rcases q11 with ⟨hg11, he11, hl11, hw2, hc2a, hvw2, hvc2a⟩
  rcases h12 : emitHA n g11 w2 k1 with ⟨g12, z2, c2b⟩; dsimp only
  have q12 := emitHA_spec (a := w2) (b := k1) hg11 hw2 (by omega) x hx; rw [h12] at q12; dsimp only at q12; rcases q12 with ⟨hg12, he12, hl12, hz2, hc2b, hvz2, hvc2b⟩
  rcases h13 : emitFA n g12 p12 p21 c2a with ⟨g13, w3, c3a⟩; dsimp only
  have q13 := emitFA_spec (a := p12) (b := p21) (c := c2a) hg12 (by omega) (by omega) (by omega) x hx; rw [h13] at q13; dsimp only at q13; rcases q13 with ⟨hg13, he13, hl13, hw3, hc3a, hvw3, hvc3a⟩
  rcases h14 : emitHA n g13 w3 c2b with ⟨g14, z3, c3b⟩; dsimp only
  have q14 := emitHA_spec (a := w3) (b := c2b) hg13 hw3 (by omega) x hx; rw [h14] at q14; dsimp only at q14; rcases q14 with ⟨hg14, he14, hl14, hz3, hc3b, hvz3, hvc3b⟩
  rcases h15 : emitFA n g14 p22 c3a c3b with ⟨g15, z4, c4⟩; dsimp only
  have q15 := emitFA_spec (a := p22) (b := c3a) (c := c3b) hg14 (by omega) (by omega) hc3b x hx; rw [h15] at q15; dsimp only at q15; rcases q15 with ⟨hg15, he15, hl15, hz4, _, hvz4, _⟩
  have e02 := extends_trans he1 he2
  have e03 := extends_trans e02 he3
  have e04 := extends_trans e03 he4
  have e05 := extends_trans e04 he5
  have e06 := extends_trans e05 he6
  have e07 := extends_trans e06 he7
  have e08 := extends_trans e07 he8
  have e09 := extends_trans e08 he9
  have e015 := extends_trans e09 (extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 he15)))))
  have e29 := extends_trans he3 (extends_trans he4 (extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8 he9)))))
  have e49 := extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8 he9)))
  have e310 := extends_trans he4 (extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8 (extends_trans he9 he10)))))
  have e510 := extends_trans he6 (extends_trans he7 (extends_trans he8 (extends_trans he9 he10)))
  have e710 := extends_trans he8 (extends_trans he9 he10)
  have e612 := extends_trans he7 (extends_trans he8 (extends_trans he9 (extends_trans he10 (extends_trans he11 he12))))
  have e812 := extends_trans he9 (extends_trans he10 (extends_trans he11 he12))
  have e914 := extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 he14)))
  have vp01 : wireVal g2 x p01 = (wireVal gs x r0 && wireVal gs x c1) := by
    rw [hvp01, wireVal_of_ext hx he1 hr0 rfl, wireVal_of_ext hx he1 hc1 rfl]
  have vp02 : wireVal g3 x p02 = (wireVal gs x r0 && wireVal gs x c2) := by
    rw [hvp02, wireVal_of_ext hx e02 hr0 rfl, wireVal_of_ext hx e02 hc2 rfl]
  have vp10 : wireVal g4 x p10 = (wireVal gs x r1 && wireVal gs x c0) := by
    rw [hvp10, wireVal_of_ext hx e03 hr1 rfl, wireVal_of_ext hx e03 hc0 rfl]
  have vp11 : wireVal g5 x p11 = (wireVal gs x r1 && wireVal gs x c1) := by
    rw [hvp11, wireVal_of_ext hx e04 hr1 rfl, wireVal_of_ext hx e04 hc1 rfl]
  have vp12 : wireVal g6 x p12 = (wireVal gs x r1 && wireVal gs x c2) := by
    rw [hvp12, wireVal_of_ext hx e05 hr1 rfl, wireVal_of_ext hx e05 hc2 rfl]
  have vp20 : wireVal g7 x p20 = (wireVal gs x r2 && wireVal gs x c0) := by
    rw [hvp20, wireVal_of_ext hx e06 hr2 rfl, wireVal_of_ext hx e06 hc0 rfl]
  have vp21 : wireVal g8 x p21 = (wireVal gs x r2 && wireVal gs x c1) := by
    rw [hvp21, wireVal_of_ext hx e07 hr2 rfl, wireVal_of_ext hx e07 hc1 rfl]
  have vp22 : wireVal g9 x p22 = (wireVal gs x r2 && wireVal gs x c2) := by
    rw [hvp22, wireVal_of_ext hx e08 hr2 rfl, wireVal_of_ext hx e08 hc2 rfl]
  have vz1 : wireVal g10 x z1 = xor (wireVal gs x r0 && wireVal gs x c1) (wireVal gs x r1 && wireVal gs x c0) := by
    rw [hvz1, wireVal_of_ext hx e29 hp01 vp01, wireVal_of_ext hx e49 hp10 vp10]
  have vk1 : wireVal g10 x k1 = ((wireVal gs x r0 && wireVal gs x c1) && (wireVal gs x r1 && wireVal gs x c0)) := by
    rw [hvk1, wireVal_of_ext hx e29 hp01 vp01, wireVal_of_ext hx e49 hp10 vp10]
  have vw2 : wireVal g11 x w2 = xor (xor (wireVal gs x r0 && wireVal gs x c2) (wireVal gs x r1 && wireVal gs x c1)) (wireVal gs x r2 && wireVal gs x c0) := by
    rw [hvw2, wireVal_of_ext hx e310 hp02 vp02, wireVal_of_ext hx e510 hp11 vp11, wireVal_of_ext hx e710 hp20 vp20]
  have vc2a : wireVal g11 x c2a = (((wireVal gs x r0 && wireVal gs x c2) && (wireVal gs x r1 && wireVal gs x c1)) || (xor (wireVal gs x r0 && wireVal gs x c2) (wireVal gs x r1 && wireVal gs x c1) && (wireVal gs x r2 && wireVal gs x c0))) := by
    rw [hvc2a, wireVal_of_ext hx e310 hp02 vp02, wireVal_of_ext hx e510 hp11 vp11, wireVal_of_ext hx e710 hp20 vp20]
  have vz2 : wireVal g12 x z2 = xor (wireVal g11 x w2) (wireVal g10 x k1) := by
    rw [hvz2, wireVal_of_ext hx he11 hk1 rfl]
  have vc2b : wireVal g12 x c2b = (wireVal g11 x w2 && wireVal g10 x k1) := by
    rw [hvc2b, wireVal_of_ext hx he11 hk1 rfl]
  have vw3 : wireVal g13 x w3 = xor (xor (wireVal gs x r1 && wireVal gs x c2) (wireVal gs x r2 && wireVal gs x c1)) (wireVal g11 x c2a) := by
    rw [hvw3, wireVal_of_ext hx e612 hp12 vp12, wireVal_of_ext hx e812 hp21 vp21, wireVal_of_ext hx he12 hc2a rfl]
  have vc3a : wireVal g13 x c3a = (((wireVal gs x r1 && wireVal gs x c2) && (wireVal gs x r2 && wireVal gs x c1)) || (xor (wireVal gs x r1 && wireVal gs x c2) (wireVal gs x r2 && wireVal gs x c1) && wireVal g11 x c2a)) := by
    rw [hvc3a, wireVal_of_ext hx e612 hp12 vp12, wireVal_of_ext hx e812 hp21 vp21, wireVal_of_ext hx he12 hc2a rfl]
  have vz3 : wireVal g14 x z3 = xor (wireVal g13 x w3) (wireVal g12 x c2b) := by
    rw [hvz3, wireVal_of_ext hx he13 hc2b rfl]
  have vc3b : wireVal g14 x c3b = (wireVal g13 x w3 && wireVal g12 x c2b) := by
    rw [hvc3b, wireVal_of_ext hx he13 hc2b rfl]
  have vz4 : wireVal g15 x z4 = xor (xor (wireVal gs x r2 && wireVal gs x c2) (wireVal g13 x c3a)) (wireVal g14 x c3b) := by
    rw [hvz4, wireVal_of_ext hx e914 hp22 vp22, wireVal_of_ext hx he14 hc3a rfl]
  refine ⟨hg15, e015, by omega, ?_, ?_⟩
  · intro i
    fin_cases i
    · change p00 < n + g15.length; omega
    · change z1 < n + g15.length; omega
    · change z2 < n + g15.length; omega
    · change z3 < n + g15.length; omega
    · change z4 < n + g15.length; omega
  · intro i
    fin_cases i
    · change wireVal g15 x p00 = (wireVal gs x r0 && wireVal gs x c0)
      have e115 := extends_trans he2 (extends_trans he3 (extends_trans he4 (extends_trans he5
        (extends_trans he6 (extends_trans he7 (extends_trans he8 (extends_trans he9
        (extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 he15))))))))))))
      rw [wireVal_of_ext hx e115 hp00 hvp00]
    · change wireVal g15 x z1 = xor (wireVal gs x r0 && wireVal gs x c1) (wireVal gs x r1 && wireVal gs x c0)
      have e1015 := extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 he15)))
      rw [wireVal_of_ext hx e1015 hz1 vz1]
    · change wireVal g15 x z2 = _
      have e1215 := extends_trans he13 (extends_trans he14 he15)
      rw [wireVal_of_ext hx e1215 hz2 vz2, vw2, vk1]; rfl
    · change wireVal g15 x z3 = _
      rw [wireVal_of_ext hx he15 hz3 vz3, vw3, vc2b, vw2, vk1, vc2a]; rfl
    · change wireVal g15 x z4 = _
      rw [vz4, vc3a, vc3b, vw3, vc2b, vw2, vk1, vc2a]; rfl

lemma pack_len {k : Nat} (w : Fin (2 ^ k)) : (pack w).length = k := by
  simp [pack]

lemma pack_getD {k : Nat} (w : Fin (2 ^ k)) {p : Nat} (hp : p < k) :
    (pack w).getD p false = w.val.testBit p := by
  unfold pack
  simp [List.getD_eq_getElem?_getD, hp]

lemma flatten_ofFn_len {k m : Nat} (gen : Fin m → Fin (2 ^ k)) :
    (List.ofFn (fun g : Fin m => pack (gen g))).flatten.length = m * k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, pack_len, ih (fun g => gen g.succ)]
    rw [Nat.succ_mul]
    omega

lemma flatten_ofFn_getD {k m : Nat} (gen : Fin m → Fin (2 ^ k)) (g : Fin m) {p : Nat} (hp : p < k) :
    (List.ofFn (fun i : Fin m => pack (gen i))).flatten.getD (g.val * k + p) false = (gen g).val.testBit p := by
  induction m with
  | zero => exact Fin.elim0 g
  | succ m ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases g using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [pack_len]; exact hp)]
      have h := pack_getD (gen 0) hp
      simpa [List.getD_eq_getElem?_getD] using h
    | succ j =>
      simp only [Fin.val_succ, List.getD_eq_getElem?_getD]
      have hge : (pack (gen 0)).length ≤ (j.val + 1) * k + p := by
        rw [pack_len, Nat.succ_mul]; omega
      rw [List.getElem?_append_right hge, pack_len]
      have hsub : (j.val + 1) * k + p - k = j.val * k + p := by
        rw [Nat.succ_mul]; omega
      rw [hsub]
      have h := ih (fun i => gen i.succ) j
      simpa [List.getD_eq_getElem?_getD] using h

def inputVec {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k)) : List Bool :=
  pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten ++ pack cr ++ pack cc

lemma inputVec_len {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k)) :
    (inputVec base gen cr cc).length = (m + 3) * k := by
  unfold inputVec
  simp only [List.length_append, pack_len, flatten_ofFn_len]
  have h1 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
  omega

lemma inputVec_base {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    {p : Nat} (hp : p < k) :
    (inputVec base gen cr cc).getD p false = base.val.testBit p := by
  unfold inputVec
  rw [List.append_assoc, List.append_assoc]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [pack_len]; exact hp)]
  have h := pack_getD base hp
  simpa [List.getD_eq_getElem?_getD] using h

lemma inputVec_gen {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    (g : Fin m) {p : Nat} (hp : p < k) :
    (inputVec base gen cr cc).getD (k + g.val * k + p) false = (gen g).val.testBit p := by
  unfold inputVec
  rw [List.append_assoc, List.append_assoc]
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by rw [pack_len]; omega), pack_len]
  have hsub : k + g.val * k + p - k = g.val * k + p := by omega
  rw [hsub]
  have hlt : g.val * k + p < (List.ofFn (fun i : Fin m => pack (gen i))).flatten.length := by
    rw [flatten_ofFn_len]
    have h1 : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k g.isLt
    rw [Nat.succ_mul] at h1
    omega
  rw [List.getElem?_append_left hlt]
  have h := flatten_ofFn_getD gen g hp
  simpa [List.getD_eq_getElem?_getD] using h

lemma inputVec_cr {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    {p : Nat} (hp : p < k) :
    (inputVec base gen cr cc).getD ((m + 1) * k + p) false = cr.val.testBit p := by
  unfold inputVec
  simp only [List.getD_eq_getElem?_getD]
  have hlt : (m + 1) * k + p < (pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten ++ pack cr).length := by
    simp only [List.length_append, pack_len, flatten_ofFn_len]
    have h1 : (m + 1) * k = m * k + k := Nat.succ_mul m k
    omega
  rw [List.getElem?_append_left hlt]
  have hge : (pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten).length ≤ (m + 1) * k + p := by
    simp only [List.length_append, pack_len, flatten_ofFn_len]
    have h1 : (m + 1) * k = m * k + k := Nat.succ_mul m k
    omega
  rw [List.getElem?_append_right hge]
  have hsub : (m + 1) * k + p - (pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten).length = p := by
    simp only [List.length_append, pack_len, flatten_ofFn_len]
    have h1 : (m + 1) * k = m * k + k := Nat.succ_mul m k
    omega
  rw [hsub]
  have h := pack_getD cr hp
  simpa [List.getD_eq_getElem?_getD] using h

lemma inputVec_cc {k m : Nat} (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    {p : Nat} (hp : p < k) :
    (inputVec base gen cr cc).getD ((m + 2) * k + p) false = cc.val.testBit p := by
  unfold inputVec
  simp only [List.getD_eq_getElem?_getD]
  have hge : (pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten ++ pack cr).length ≤ (m + 2) * k + p := by
    simp only [List.length_append, pack_len, flatten_ofFn_len]
    have h1 : (m + 2) * k = m * k + 2 * k := Nat.add_mul m 2 k
    omega
  rw [List.getElem?_append_right hge]
  have hsub : (m + 2) * k + p - (pack base ++ (List.ofFn (fun i : Fin m => pack (gen i))).flatten ++ pack cr).length = p := by
    simp only [List.length_append, pack_len, flatten_ofFn_len]
    have h1 : (m + 2) * k = m * k + 2 * k := Nat.add_mul m 2 k
    omega
  rw [hsub]
  have h := pack_getD cc hp
  simpa [List.getD_eq_getElem?_getD] using h

def emitDeltaBit (k m d s gIdx pos : Nat) (gs : List Gate) : List Gate × Nat :=
  let n := (m + 3) * k
  let w0 := k + gIdx * k + rotIdx k s pos
  let w1 := k + gIdx * k + rotIdx k s (rotIdx k d pos)
  let w2 := k + gIdx * k + rotIdx k s (rotIdx k (k - d % k) pos)
  let (g1, x01) := emitXor n gs w0 w1
  emitXor n g1 x01 w2

lemma emitDeltaBit_spec {k m d s : Nat} (hk : 0 < k) (g : Fin m) {pos : Nat} (hpos : pos < k)
    {gs : List Gate} (hg : Good ((m + 3) * k) gs)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k)) :
    let x := inputVec base gen cr cc
    let r := emitDeltaBit k m d s g.val pos gs
    Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 8 ∧
      r.2 < (m + 3) * k + r.1.length ∧
      wireVal r.1 x r.2 = deltaBit d s (gen g) pos := by
  dsimp only
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  have hp0 : rotIdx k s pos < k := Nat.mod_lt _ hk
  have hp1 : rotIdx k s (rotIdx k d pos) < k := Nat.mod_lt _ hk
  have hp2 : rotIdx k s (rotIdx k (k - d % k) pos) < k := Nat.mod_lt _ hk
  have hgm : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k g.isLt
  have hm3 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
  have hgn : (g.val + 1) * k = g.val * k + k := Nat.succ_mul g.val k
  have hw0 : k + g.val * k + rotIdx k s pos < n := by omega
  have hw1 : k + g.val * k + rotIdx k s (rotIdx k d pos) < n := by omega
  have hw2 : k + g.val * k + rotIdx k s (rotIdx k (k - d % k) pos) < n := by omega
  unfold emitDeltaBit
  dsimp only
  simp only [← hn_def]
  rcases h1 : emitXor n gs (k + g.val * k + rotIdx k s pos) (k + g.val * k + rotIdx k s (rotIdx k d pos)) with ⟨g1, x01⟩; dsimp only
  have q1 := emitXor_spec (a := (k + g.val * k + rotIdx k s pos)) (b := (k + g.val * k + rotIdx k s (rotIdx k d pos))) hg (by omega) (by omega) x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hx01, hvx01⟩
  rcases h2 : emitXor n g1 x01 (k + g.val * k + rotIdx k s (rotIdx k (k - d % k) pos)) with ⟨g2, wr⟩; dsimp only
  have q2 := emitXor_spec (a := x01) (b := (k + g.val * k + rotIdx k s (rotIdx k (k - d % k) pos))) hg1 hx01 (by omega) x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwr, hvr⟩
  refine ⟨hg2, extends_trans he1 he2, by omega, hwr, ?_⟩
  rw [hvr, hvx01,
      wireVal_input gs x (by rw [hx]; exact hw0),
      wireVal_input gs x (by rw [hx]; exact hw1),
      wireVal_input g1 x (by rw [hx]; exact hw2),
      inputVec_gen base gen cr cc g hp0,
      inputVec_gen base gen cr cc g hp1,
      inputVec_gen base gen cr cc g hp2]
  unfold deltaBit
  have hd1 : rotIdx k d pos < k := Nat.mod_lt _ hk
  have hd2 : rotIdx k (k - d % k) pos < k := Nat.mod_lt _ hk
  rw [mix_testBit hk (rot_lt k s _) hpos,
      rot_testBit hk (gen g).isLt hpos,
      rot_testBit hk (gen g).isLt hd1,
      rot_testBit hk (gen g).isLt hd2]

structure AccWires where
  s10 : Nat
  s01 : Nat
  s11 : Nat
  f00 : Nat
  f01 : Nat
  f10 : Nat
  f11 : Nat

def AccWires.lt (aw : AccWires) (bound : Nat) : Prop :=
  aw.s10 < bound ∧ aw.s01 < bound ∧ aw.s11 < bound ∧
  aw.f00 < bound ∧ aw.f01 < bound ∧ aw.f10 < bound ∧ aw.f11 < bound

def AccWires.matches (aw : AccWires) (gs : List Gate) (x : List Bool) (acc : GenAcc) : Prop :=
  wireVal gs x aw.s10 = acc.s10 ∧
  wireVal gs x aw.s01 = acc.s01 ∧
  wireVal gs x aw.s11 = acc.s11 ∧
  wireVal gs x aw.f00 = acc.f00 ∧
  wireVal gs x aw.f01 = acc.f01 ∧
  wireVal gs x aw.f10 = acc.f10 ∧
  wireVal gs x aw.f11 = acc.f11

def emitGenStep (k m d s t i gIdx : Nat) (gs : List Gate) (aw : AccWires) : List Gate × AccWires :=
  let n := (m + 3) * k
  let (g1, wd) := emitDeltaBit k m d s gIdx i gs
  let (g2, wa) := emitDeltaBit k m d s gIdx ((i + 1) % k) g1
  let (g3, wb) := emitDeltaBit k m d s gIdx ((i + 2) % k) g2
  let wrho := k + gIdx * k + rotIdx k t i
  let (g4, we) := emitXor n g3 wd wrho
  let (g5, wna) := emitNot n g4 wa
  let (g6, wnb) := emitNot n g5 wb
  let (g7, wp00) := emitAnd n g6 wna wnb
  let (g8, wp10) := emitAnd n g7 wa wnb
  let (g9, wp01) := emitAnd n g8 wna wb
  let (g10, wp11) := emitAnd n g9 wa wb
  let (g11, wnp00) := emitNot n g10 wp00
  let (g12, ws10) := emitOr n g11 aw.s10 wp10
  let (g13, ws01) := emitOr n g12 aw.s01 wp01
  let (g14, ws11) := emitOr n g13 aw.s11 wp11
  let (g15, wd00) := emitXor n g14 wp01 we
  let (g16, wd01) := emitXor n g15 wnp00 we
  let (g17, wd10) := emitXor n g16 wp11 we
  let (g18, wd11) := emitXor n g17 wp10 we
  let (g19, wf00) := emitOr n g18 aw.f00 wd00
  let (g20, wf01) := emitOr n g19 aw.f01 wd01
  let (g21, wf10) := emitOr n g20 aw.f10 wd10
  let (g22, wf11) := emitOr n g21 aw.f11 wd11
  (g22, ⟨ws10, ws01, ws11, wf00, wf01, wf10, wf11⟩)

lemma emitGenStep_spec {k m d s t i : Nat} (hk : 0 < k) (hi : i < k) (g : Fin m)
    {gs : List Gate} {aw : AccWires} {acc : GenAcc}
    (hg : Good ((m + 3) * k) gs) (haw : aw.lt ((m + 3) * k + gs.length))
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    (hmatch : aw.matches gs (inputVec base gen cr cc) acc) :
    let x := inputVec base gen cr cc
    let r := emitGenStep k m d s t i g.val gs aw
    Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 58 ∧
      r.2.lt ((m + 3) * k + r.1.length) ∧
      r.2.matches r.1 x (genAccStep acc
        (deltaBit d s (gen g) ((i + 1) % k))
        (deltaBit d s (gen g) ((i + 2) % k))
        (eBit d s t (gen g) i)) := by
  dsimp only
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  have hrt : rotIdx k t i < k := Nat.mod_lt _ hk
  have hgm : (g.val + 1) * k ≤ m * k := Nat.mul_le_mul_right k g.isLt
  have hm3 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
  have hgn : (g.val + 1) * k = g.val * k + k := Nat.succ_mul g.val k
  have hwrho : k + g.val * k + rotIdx k t i < n := by omega
  rcases haw with ⟨hs10, hs01, hs11, hf00, hf01, hf10, hf11⟩
  rcases hmatch with ⟨ms10, ms01, ms11, mf00, mf01, mf10, mf11⟩
  unfold emitGenStep
  rcases h1 : emitDeltaBit k m d s g.val i gs with ⟨g1, wd⟩; dsimp only
  have q1 := emitDeltaBit_spec (d := d) (s := s) (pos := i) hk g hi hg base gen cr cc; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwd, hvd⟩
  rcases h2 : emitDeltaBit k m d s g.val ((i + 1) % k) g1 with ⟨g2, wa⟩; dsimp only
  have q2 := emitDeltaBit_spec (d := d) (s := s) (pos := (i + 1) % k) hk g (Nat.mod_lt _ hk) hg1 base gen cr cc; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwa, hva⟩
  rcases h3 : emitDeltaBit k m d s g.val ((i + 2) % k) g2 with ⟨g3, wb⟩; dsimp only
  have q3 := emitDeltaBit_spec (d := d) (s := s) (pos := (i + 2) % k) hk g (Nat.mod_lt _ hk) hg2 base gen cr cc; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwb, hvb⟩
  rcases h4 : emitXor n g3 wd (k + g.val * k + rotIdx k t i) with ⟨g4, we⟩; dsimp only
  have q4 := emitXor_spec (a := wd) (b := (k + g.val * k + rotIdx k t i)) hg3 (by omega) (by omega) x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwe, hve⟩
  rcases h5 : emitNot n g4 wa with ⟨g5, wna⟩; dsimp only
  have q5 := emitNot_spec (a := wa) hg4 (by omega) x hx; rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hwna, hvna⟩
  rcases h6 : emitNot n g5 wb with ⟨g6, wnb⟩; dsimp only
  have q6 := emitNot_spec (a := wb) hg5 (by omega) x hx; rw [h6] at q6; dsimp only at q6; rcases q6 with ⟨hg6, he6, hl6, hwnb, hvnb⟩
  rcases h7 : emitAnd n g6 wna wnb with ⟨g7, wp00⟩; dsimp only
  have q7 := emitAnd_spec (a := wna) (b := wnb) hg6 (by omega) hwnb x hx; rw [h7] at q7; dsimp only at q7; rcases q7 with ⟨hg7, he7, hl7, hwp00, hvp00⟩
  rcases h8 : emitAnd n g7 wa wnb with ⟨g8, wp10⟩; dsimp only
  have q8 := emitAnd_spec (a := wa) (b := wnb) hg7 (by omega) (by omega) x hx; rw [h8] at q8; dsimp only at q8; rcases q8 with ⟨hg8, he8, hl8, hwp10, hvp10⟩
  rcases h9 : emitAnd n g8 wna wb with ⟨g9, wp01⟩; dsimp only
  have q9 := emitAnd_spec (a := wna) (b := wb) hg8 (by omega) (by omega) x hx; rw [h9] at q9; dsimp only at q9; rcases q9 with ⟨hg9, he9, hl9, hwp01, hvp01⟩
  rcases h10 : emitAnd n g9 wa wb with ⟨g10, wp11⟩; dsimp only
  have q10 := emitAnd_spec (a := wa) (b := wb) hg9 (by omega) (by omega) x hx; rw [h10] at q10; dsimp only at q10; rcases q10 with ⟨hg10, he10, hl10, hwp11, hvp11⟩
  rcases h11 : emitNot n g10 wp00 with ⟨g11, wnp00⟩; dsimp only
  have q11 := emitNot_spec (a := wp00) hg10 (by omega) x hx; rw [h11] at q11; dsimp only at q11; rcases q11 with ⟨hg11, he11, hl11, hwnp00, hvnp00⟩
  rcases h12 : emitOr n g11 aw.s10 wp10 with ⟨g12, ws10⟩; dsimp only
  have q12 := emitOr_spec (a := aw.s10) (b := wp10) hg11 (by omega) (by omega) x hx; rw [h12] at q12; dsimp only at q12; rcases q12 with ⟨hg12, he12, hl12, hws10, hvs10⟩
  rcases h13 : emitOr n g12 aw.s01 wp01 with ⟨g13, ws01⟩; dsimp only
  have q13 := emitOr_spec (a := aw.s01) (b := wp01) hg12 (by omega) (by omega) x hx; rw [h13] at q13; dsimp only at q13; rcases q13 with ⟨hg13, he13, hl13, hws01, hvs01⟩
  rcases h14 : emitOr n g13 aw.s11 wp11 with ⟨g14, ws11⟩; dsimp only
  have q14 := emitOr_spec (a := aw.s11) (b := wp11) hg13 (by omega) (by omega) x hx; rw [h14] at q14; dsimp only at q14; rcases q14 with ⟨hg14, he14, hl14, hws11, hvs11⟩
  rcases h15 : emitXor n g14 wp01 we with ⟨g15, wd00⟩; dsimp only
  have q15 := emitXor_spec (a := wp01) (b := we) hg14 (by omega) (by omega) x hx; rw [h15] at q15; dsimp only at q15; rcases q15 with ⟨hg15, he15, hl15, hwd00, hvd00⟩
  rcases h16 : emitXor n g15 wnp00 we with ⟨g16, wd01⟩; dsimp only
  have q16 := emitXor_spec (a := wnp00) (b := we) hg15 (by omega) (by omega) x hx; rw [h16] at q16; dsimp only at q16; rcases q16 with ⟨hg16, he16, hl16, hwd01, hvd01⟩
  rcases h17 : emitXor n g16 wp11 we with ⟨g17, wd10⟩; dsimp only
  have q17 := emitXor_spec (a := wp11) (b := we) hg16 (by omega) (by omega) x hx; rw [h17] at q17; dsimp only at q17; rcases q17 with ⟨hg17, he17, hl17, hwd10, hvd10⟩
  rcases h18 : emitXor n g17 wp10 we with ⟨g18, wd11⟩; dsimp only
  have q18 := emitXor_spec (a := wp10) (b := we) hg17 (by omega) (by omega) x hx; rw [h18] at q18; dsimp only at q18; rcases q18 with ⟨hg18, he18, hl18, hwd11, hvd11⟩
  rcases h19 : emitOr n g18 aw.f00 wd00 with ⟨g19, wf00⟩; dsimp only
  have q19 := emitOr_spec (a := aw.f00) (b := wd00) hg18 (by omega) (by omega) x hx; rw [h19] at q19; dsimp only at q19; rcases q19 with ⟨hg19, he19, hl19, hwf00, hvf00⟩
  rcases h20 : emitOr n g19 aw.f01 wd01 with ⟨g20, wf01⟩; dsimp only
  have q20 := emitOr_spec (a := aw.f01) (b := wd01) hg19 (by omega) (by omega) x hx; rw [h20] at q20; dsimp only at q20; rcases q20 with ⟨hg20, he20, hl20, hwf01, hvf01⟩
  rcases h21 : emitOr n g20 aw.f10 wd10 with ⟨g21, wf10⟩; dsimp only
  have q21 := emitOr_spec (a := aw.f10) (b := wd10) hg20 (by omega) (by omega) x hx; rw [h21] at q21; dsimp only at q21; rcases q21 with ⟨hg21, he21, hl21, hwf10, hvf10⟩
  rcases h22 : emitOr n g21 aw.f11 wd11 with ⟨g22, wf11⟩; dsimp only
  have q22 := emitOr_spec (a := aw.f11) (b := wd11) hg21 (by omega) (by omega) x hx; rw [h22] at q22; dsimp only at q22; rcases q22 with ⟨hg22, he22, hl22, hwf11, hvf11⟩
  have e011 := extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4
    (extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8
    (extends_trans he9 (extends_trans he10 he11)))))))))
  have e018 := extends_trans e011 (extends_trans he12 (extends_trans he13 (extends_trans he14
    (extends_trans he15 (extends_trans he16 (extends_trans he17 he18))))))
  have e022 := extends_trans e018 (extends_trans he19 (extends_trans he20 (extends_trans he21 he22)))
  have e414 := extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8
    (extends_trans he9 (extends_trans he10 (extends_trans he11 (extends_trans he12
    (extends_trans he13 he14))))))))
  have e1222 := extends_trans he13 (extends_trans he14 (extends_trans he15 (extends_trans he16
    (extends_trans he17 (extends_trans he18 (extends_trans he19 (extends_trans he20
    (extends_trans he21 he22))))))))
  have e1322 := extends_trans he14 (extends_trans he15 (extends_trans he16
    (extends_trans he17 (extends_trans he18 (extends_trans he19 (extends_trans he20
    (extends_trans he21 he22)))))))
  have e1422 := extends_trans he15 (extends_trans he16
    (extends_trans he17 (extends_trans he18 (extends_trans he19 (extends_trans he20
    (extends_trans he21 he22))))))
  have ve : wireVal g4 x we = eBit d s t (gen g) i := by
    rw [hve, wireVal_of_ext hx (extends_trans he2 he3) hwd hvd,
        wireVal_input g3 x (by rw [hx]; exact hwrho),
        inputVec_gen base gen cr cc g hrt, ← rot_testBit hk (gen g).isLt hi]
    rfl
  have vna : wireVal g5 x wna = !(deltaBit d s (gen g) ((i + 1) % k)) := by
    rw [hvna, wireVal_of_ext hx (extends_trans he3 he4) hwa hva]
  have vnb : wireVal g6 x wnb = !(deltaBit d s (gen g) ((i + 2) % k)) := by
    rw [hvnb, wireVal_of_ext hx (extends_trans he4 he5) hwb hvb]
  have vp00 : wireVal g7 x wp00 = (!(deltaBit d s (gen g) ((i + 1) % k)) && !(deltaBit d s (gen g) ((i + 2) % k))) := by
    rw [hvp00, wireVal_of_ext hx he6 hwna vna, vnb]
  have vp10 : wireVal g8 x wp10 = (deltaBit d s (gen g) ((i + 1) % k) && !(deltaBit d s (gen g) ((i + 2) % k))) := by
    rw [hvp10, wireVal_of_ext hx (extends_trans he3 (extends_trans he4 (extends_trans he5 (extends_trans he6 he7)))) hwa hva,
        wireVal_of_ext hx he7 hwnb vnb]
  have vp01 : wireVal g9 x wp01 = (!(deltaBit d s (gen g) ((i + 1) % k)) && deltaBit d s (gen g) ((i + 2) % k)) := by
    rw [hvp01, wireVal_of_ext hx (extends_trans he6 (extends_trans he7 he8)) hwna vna,
        wireVal_of_ext hx (extends_trans he4 (extends_trans he5 (extends_trans he6 (extends_trans he7 he8)))) hwb hvb]
  have vp11 : wireVal g10 x wp11 = (deltaBit d s (gen g) ((i + 1) % k) && deltaBit d s (gen g) ((i + 2) % k)) := by
    rw [hvp11, wireVal_of_ext hx (extends_trans he3 (extends_trans he4 (extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8 he9)))))) hwa hva,
        wireVal_of_ext hx (extends_trans he4 (extends_trans he5 (extends_trans he6 (extends_trans he7 (extends_trans he8 he9))))) hwb hvb]
  have vnp00 : wireVal g11 x wnp00 = !(!(deltaBit d s (gen g) ((i + 1) % k)) && !(deltaBit d s (gen g) ((i + 2) % k))) := by
    rw [hvnp00, wireVal_of_ext hx (extends_trans he8 (extends_trans he9 he10)) hwp00 vp00]
  have vd00 : wireVal g15 x wd00 = xor (!(deltaBit d s (gen g) ((i + 1) % k)) && deltaBit d s (gen g) ((i + 2) % k)) (eBit d s t (gen g) i) := by
    rw [hvd00, wireVal_of_ext hx (extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 he14)))) hwp01 vp01,
        wireVal_of_ext hx e414 hwe ve]
  have vd01 : wireVal g16 x wd01 = xor (!(!(deltaBit d s (gen g) ((i + 1) % k)) && !(deltaBit d s (gen g) ((i + 2) % k)))) (eBit d s t (gen g) i) := by
    rw [hvd01, wireVal_of_ext hx (extends_trans he12 (extends_trans he13 (extends_trans he14 he15))) hwnp00 vnp00,
        wireVal_of_ext hx (extends_trans e414 he15) hwe ve]
  have vd10 : wireVal g17 x wd10 = xor (deltaBit d s (gen g) ((i + 1) % k) && deltaBit d s (gen g) ((i + 2) % k)) (eBit d s t (gen g) i) := by
    rw [hvd10, wireVal_of_ext hx (extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 (extends_trans he15 he16))))) hwp11 vp11,
        wireVal_of_ext hx (extends_trans e414 (extends_trans he15 he16)) hwe ve]
  have vd11 : wireVal g18 x wd11 = xor (deltaBit d s (gen g) ((i + 1) % k) && !(deltaBit d s (gen g) ((i + 2) % k))) (eBit d s t (gen g) i) := by
    rw [hvd11, wireVal_of_ext hx (extends_trans he9 (extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 (extends_trans he15 (extends_trans he16 he17)))))))) hwp10 vp10,
        wireVal_of_ext hx (extends_trans e414 (extends_trans he15 (extends_trans he16 he17))) hwe ve]
  dsimp only [AccWires.lt]
  refine ⟨hg22, e022, by omega, ⟨by omega, by omega, by omega, by omega, by omega, by omega, hwf11⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [wireVal_of_ext hx e1222 hws10 hvs10, wireVal_of_ext hx e011 hs10 ms10,
        wireVal_of_ext hx (extends_trans he9 (extends_trans he10 he11)) hwp10 vp10]; rfl
  · rw [wireVal_of_ext hx e1322 hws01 hvs01, wireVal_of_ext hx (extends_trans e011 he12) hs01 ms01,
        wireVal_of_ext hx (extends_trans he10 (extends_trans he11 he12)) hwp01 vp01]; rfl
  · rw [wireVal_of_ext hx e1422 hws11 hvs11, wireVal_of_ext hx (extends_trans e011 (extends_trans he12 he13)) hs11 ms11,
        wireVal_of_ext hx (extends_trans he11 (extends_trans he12 he13)) hwp11 vp11]; rfl
  · rw [wireVal_of_ext hx (extends_trans he20 (extends_trans he21 he22)) hwf00 hvf00,
        wireVal_of_ext hx e018 hf00 mf00,
        wireVal_of_ext hx (extends_trans he16 (extends_trans he17 he18)) hwd00 vd00]; rfl
  · rw [wireVal_of_ext hx (extends_trans he21 he22) hwf01 hvf01,
        wireVal_of_ext hx (extends_trans e018 he19) hf01 mf01,
        wireVal_of_ext hx (extends_trans he17 (extends_trans he18 he19)) hwd01 vd01]; rfl
  · rw [wireVal_of_ext hx he22 hwf10 hvf10,
        wireVal_of_ext hx (extends_trans e018 (extends_trans he19 he20)) hf10 mf10,
        wireVal_of_ext hx (extends_trans he18 (extends_trans he19 he20)) hwd10 vd10]; rfl
  · rw [hvf11, wireVal_of_ext hx (extends_trans e018 (extends_trans he19 (extends_trans he20 he21))) hf11 mf11,
        wireVal_of_ext hx (extends_trans he19 (extends_trans he20 he21)) hwd11 vd11]; rfl

def emitGenLoop (k m d s t i : Nat) (wFalse : Nat) (gs : List Gate) : Nat → List Gate × AccWires
  | 0 => (gs, ⟨wFalse, wFalse, wFalse, wFalse, wFalse, wFalse, wFalse⟩)
  | n + 1 =>
    let (gs1, aw1) := emitGenLoop k m d s t i wFalse gs n
    emitGenStep k m d s t i n gs1 aw1

lemma emitGenLoop_spec {k m d s t i : Nat} (hk : 0 < k) (hi : i < k)
    {wFalse : Nat} {gs : List Gate}
    (hg : Good ((m + 3) * k) gs) (hwf : wFalse < (m + 3) * k + gs.length)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k))
    (hwf_val : wireVal gs (inputVec base gen cr cc) wFalse = false) :
    ∀ n (hn : n ≤ m),
      let r := emitGenLoop k m d s t i wFalse gs n
      Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 58 * n ∧
        r.2.lt ((m + 3) * k + r.1.length) ∧
        r.2.matches r.1 (inputVec base gen cr cc)
          (genAccRun
            (fun g => deltaBit d s (gen g) ((i + 1) % k))
            (fun g => deltaBit d s (gen g) ((i + 2) % k))
            (fun g => eBit d s t (gen g) i) n hn) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨hg, extends_refl gs, by simp [emitGenLoop],
      ⟨hwf, hwf, hwf, hwf, hwf, hwf, hwf⟩,
      ⟨hwf_val, hwf_val, hwf_val, hwf_val, hwf_val, hwf_val, hwf_val⟩⟩
  | succ n ih =>
    intro hn
    dsimp only
    unfold emitGenLoop
    rcases hp : emitGenLoop k m d s t i wFalse gs n with ⟨gs1, aw1⟩; dsimp only
    have prev := ih (by omega); rw [hp] at prev; dsimp only at prev; rcases prev with ⟨hgp, hep, hlp, hltp, hmp⟩
    rcases hs : emitGenStep k m d s t i n gs1 aw1 with ⟨gs2, aw2⟩; dsimp only
    have q := emitGenStep_spec (d := d) (s := s) (t := t) hk hi ⟨n, hn⟩ hgp hltp base gen cr cc hmp
    rw [hs] at q; dsimp only at q; rcases q with ⟨hg2, he2, hl2, hlt2, hm2⟩
    refine ⟨hg2, extends_trans hep he2, by omega, hlt2, hm2⟩

structure BitWires where
  bout : Nat
  ok00 : Nat
  ok01 : Nat
  ok10 : Nat
  ok11 : Nat

def BitWires.lt (bw : BitWires) (bound : Nat) : Prop :=
  bw.bout < bound ∧ bw.ok00 < bound ∧ bw.ok01 < bound ∧ bw.ok10 < bound ∧ bw.ok11 < bound

def emitBitWires (k m d s t cOff i wFalse : Nat) (gs : List Gate) : List Gate × BitWires :=
  let n := (m + 3) * k
  let (g0, aw) := emitGenLoop k m d s t i wFalse gs m
  let (g1, wbout) := emitXor n g0 (rotIdx k t i) (cOff + i)
  let (g2, wa1) := emitAnd n g1 aw.s10 aw.s01
  let (g3, wa2) := emitAnd n g2 aw.s10 aw.s11
  let (g4, wa3) := emitAnd n g3 aw.s01 aw.s11
  let (g5, wo1) := emitOr n g4 wa1 wa2
  let (g6, wbad) := emitOr n g5 wo1 wa3
  let (g7, wnbad) := emitNot n g6 wbad
  let (g8, wnf00) := emitNot n g7 aw.f00
  let (g9, wnf01) := emitNot n g8 aw.f01
  let (g10, wnf10) := emitNot n g9 aw.f10
  let (g11, wnf11) := emitNot n g10 aw.f11
  let (g12, wok00) := emitAnd n g11 wnbad wnf00
  let (g13, wok01) := emitAnd n g12 wnbad wnf01
  let (g14, wok10) := emitAnd n g13 wnbad wnf10
  let (g15, wok11) := emitAnd n g14 wnbad wnf11
  (g15, ⟨wbout, wok00, wok01, wok10, wok11⟩)

lemma emitBitWires_spec {k m d s t cOff i wFalse : Nat} (hk : 0 < k) (hi : i < k)
    (hcOff : cOff + k ≤ (m + 3) * k)
    {gs : List Gate} (hg : Good ((m + 3) * k) gs) (hwf : wFalse < (m + 3) * k + gs.length)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc c : Fin (2 ^ k))
    (hc_in : (inputVec base gen cr cc).getD (cOff + i) false = c.val.testBit i)
    (hwf_val : wireVal gs (inputVec base gen cr cc) wFalse = false) :
    let x := inputVec base gen cr cc
    let r := emitBitWires k m d s t cOff i wFalse gs
    Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + (58 * m + 18) ∧
      r.2.lt ((m + 3) * k + r.1.length) ∧
      wireVal r.1 x r.2.bout = baseOutBit t base c i ∧
      wireVal r.1 x r.2.ok00 = bitOk d s t base gen i false false ∧
      wireVal r.1 x r.2.ok01 = bitOk d s t base gen i false true ∧
      wireVal r.1 x r.2.ok10 = bitOk d s t base gen i true false ∧
      wireVal r.1 x r.2.ok11 = bitOk d s t base gen i true true := by
  dsimp only
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  have hrt : rotIdx k t i < k := Nat.mod_lt _ hk
  have hm3 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
  have hw_base : rotIdx k t i < n := by omega
  have hw_c : cOff + i < n := by omega
  unfold emitBitWires
  rcases h0 : emitGenLoop k m d s t i wFalse gs m with ⟨g0, aw⟩; dsimp only
  have q0 := emitGenLoop_spec (d := d) (s := s) (t := t) hk hi hg hwf base gen cr cc hwf_val m (le_refl m)
  rw [h0] at q0; dsimp only at q0; rcases q0 with ⟨hg0, he0, hl0, ⟨hs10, hs01, hs11, hf00, hf01, hf10, hf11⟩, ⟨ms10, ms01, ms11, mf00, mf01, mf10, mf11⟩⟩
  rcases h1 : emitXor n g0 (rotIdx k t i) (cOff + i) with ⟨g1, wbout⟩; dsimp only
  have q1 := emitXor_spec (a := (rotIdx k t i)) (b := (cOff + i)) hg0 (by omega) (by omega) x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwbout, hvbout⟩
  rcases h2 : emitAnd n g1 aw.s10 aw.s01 with ⟨g2, wa1⟩; dsimp only
  have q2 := emitAnd_spec (a := aw.s10) (b := aw.s01) hg1 (by omega) (by omega) x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwa1, hva1⟩
  rcases h3 : emitAnd n g2 aw.s10 aw.s11 with ⟨g3, wa2⟩; dsimp only
  have q3 := emitAnd_spec (a := aw.s10) (b := aw.s11) hg2 (by omega) (by omega) x hx; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwa2, hva2⟩
  rcases h4 : emitAnd n g3 aw.s01 aw.s11 with ⟨g4, wa3⟩; dsimp only
  have q4 := emitAnd_spec (a := aw.s01) (b := aw.s11) hg3 (by omega) (by omega) x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwa3, hva3⟩
  rcases h5 : emitOr n g4 wa1 wa2 with ⟨g5, wo1⟩; dsimp only
  have q5 := emitOr_spec (a := wa1) (b := wa2) hg4 (by omega) (by omega) x hx; rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hwo1, hvo1⟩
  rcases h6 : emitOr n g5 wo1 wa3 with ⟨g6, wbad⟩; dsimp only
  have q6 := emitOr_spec (a := wo1) (b := wa3) hg5 hwo1 (by omega) x hx; rw [h6] at q6; dsimp only at q6; rcases q6 with ⟨hg6, he6, hl6, hwbad, hvbad⟩
  rcases h7 : emitNot n g6 wbad with ⟨g7, wnbad⟩; dsimp only
  have q7 := emitNot_spec (a := wbad) hg6 hwbad x hx; rw [h7] at q7; dsimp only at q7; rcases q7 with ⟨hg7, he7, hl7, hwnbad, hvnbad⟩
  rcases h8 : emitNot n g7 aw.f00 with ⟨g8, wnf00⟩; dsimp only
  have q8 := emitNot_spec (a := aw.f00) hg7 (by omega) x hx; rw [h8] at q8; dsimp only at q8; rcases q8 with ⟨hg8, he8, hl8, hwnf00, hvnf00⟩
  rcases h9 : emitNot n g8 aw.f01 with ⟨g9, wnf01⟩; dsimp only
  have q9 := emitNot_spec (a := aw.f01) hg8 (by omega) x hx; rw [h9] at q9; dsimp only at q9; rcases q9 with ⟨hg9, he9, hl9, hwnf01, hvnf01⟩
  rcases h10 : emitNot n g9 aw.f10 with ⟨g10, wnf10⟩; dsimp only
  have q10 := emitNot_spec (a := aw.f10) hg9 (by omega) x hx; rw [h10] at q10; dsimp only at q10; rcases q10 with ⟨hg10, he10, hl10, hwnf10, hvnf10⟩
  rcases h11 : emitNot n g10 aw.f11 with ⟨g11, wnf11⟩; dsimp only
  have q11 := emitNot_spec (a := aw.f11) hg10 (by omega) x hx; rw [h11] at q11; dsimp only at q11; rcases q11 with ⟨hg11, he11, hl11, hwnf11, hvnf11⟩
  rcases h12 : emitAnd n g11 wnbad wnf00 with ⟨g12, wok00⟩; dsimp only
  have q12 := emitAnd_spec (a := wnbad) (b := wnf00) hg11 (by omega) (by omega) x hx; rw [h12] at q12; dsimp only at q12; rcases q12 with ⟨hg12, he12, hl12, hwok00, hvok00⟩
  rcases h13 : emitAnd n g12 wnbad wnf01 with ⟨g13, wok01⟩; dsimp only
  have q13 := emitAnd_spec (a := wnbad) (b := wnf01) hg12 (by omega) (by omega) x hx; rw [h13] at q13; dsimp only at q13; rcases q13 with ⟨hg13, he13, hl13, hwok01, hvok01⟩
  rcases h14 : emitAnd n g13 wnbad wnf10 with ⟨g14, wok10⟩; dsimp only
  have q14 := emitAnd_spec (a := wnbad) (b := wnf10) hg13 (by omega) (by omega) x hx; rw [h14] at q14; dsimp only at q14; rcases q14 with ⟨hg14, he14, hl14, hwok10, hvok10⟩
  rcases h15 : emitAnd n g14 wnbad wnf11 with ⟨g15, wok11⟩; dsimp only
  have q15 := emitAnd_spec (a := wnbad) (b := wnf11) hg14 (by omega) (by omega) x hx; rw [h15] at q15; dsimp only at q15; rcases q15 with ⟨hg15, he15, hl15, hwok11, hvok11⟩
  have e115 := extends_trans he2 (extends_trans he3 (extends_trans he4 (extends_trans he5
    (extends_trans he6 (extends_trans he7 (extends_trans he8 (extends_trans he9
    (extends_trans he10 (extends_trans he11 (extends_trans he12 (extends_trans he13 (extends_trans he14 he15))))))))))))
  have e07 := extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4
    (extends_trans he5 (extends_trans he6 he7)))))
  have e711 := extends_trans he8 (extends_trans he9 (extends_trans he10 he11))
  set acc := genAccRun (fun g => deltaBit d s (gen g) ((i + 1) % k))
    (fun g => deltaBit d s (gen g) ((i + 2) % k)) (fun g => eBit d s t (gen g) i) m (le_refl m)
  have vbout : wireVal g1 x wbout = baseOutBit t base c i := by
    rw [hvbout, wireVal_input g0 x (by rw [hx]; exact hw_base),
        wireVal_input g0 x (by rw [hx]; exact hw_c),
        inputVec_base base gen cr cc hrt, hc_in, ← rot_testBit hk base.isLt hi]; rfl
  have va1 : wireVal g2 x wa1 = (acc.s10 && acc.s01) := by
    rw [hva1, wireVal_of_ext hx he1 hs10 ms10, wireVal_of_ext hx he1 hs01 ms01]
  have va2 : wireVal g3 x wa2 = (acc.s10 && acc.s11) := by
    rw [hva2, wireVal_of_ext hx (extends_trans he1 he2) hs10 ms10, wireVal_of_ext hx (extends_trans he1 he2) hs11 ms11]
  have va3 : wireVal g4 x wa3 = (acc.s01 && acc.s11) := by
    rw [hva3, wireVal_of_ext hx (extends_trans he1 (extends_trans he2 he3)) hs01 ms01,
        wireVal_of_ext hx (extends_trans he1 (extends_trans he2 he3)) hs11 ms11]
  have vnbad : wireVal g7 x wnbad = !(accBad acc) := by
    rw [hvnbad, hvbad, hvo1, wireVal_of_ext hx (extends_trans he3 he4) hwa1 va1,
        wireVal_of_ext hx he4 hwa2 va2, wireVal_of_ext hx he5 hwa3 va3]; rfl
  have vnf00 : wireVal g8 x wnf00 = !acc.f00 := by rw [hvnf00, wireVal_of_ext hx e07 hf00 mf00]
  have vnf01 : wireVal g9 x wnf01 = !acc.f01 := by rw [hvnf01, wireVal_of_ext hx (extends_trans e07 he8) hf01 mf01]
  have vnf10 : wireVal g10 x wnf10 = !acc.f10 := by rw [hvnf10, wireVal_of_ext hx (extends_trans e07 (extends_trans he8 he9)) hf10 mf10]
  have vnf11 : wireVal g11 x wnf11 = !acc.f11 := by rw [hvnf11, wireVal_of_ext hx (extends_trans e07 (extends_trans he8 (extends_trans he9 he10))) hf11 mf11]
  dsimp only [BitWires.lt]
  refine ⟨hg15, extends_trans he0 (extends_trans he1 e115), by omega,
    ⟨by omega, by omega, by omega, by omega, hwok11⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact wireVal_of_ext hx e115 hwbout vbout
  · rw [wireVal_of_ext hx (extends_trans he13 (extends_trans he14 he15)) hwok00 hvok00,
        wireVal_of_ext hx e711 hwnbad vnbad,
        wireVal_of_ext hx (extends_trans he9 (extends_trans he10 he11)) hwnf00 vnf00]; rfl
  · rw [wireVal_of_ext hx (extends_trans he14 he15) hwok01 hvok01,
        wireVal_of_ext hx (extends_trans e711 he12) hwnbad vnbad,
        wireVal_of_ext hx (extends_trans he10 (extends_trans he11 he12)) hwnf01 vnf01]; rfl
  · rw [wireVal_of_ext hx he15 hwok10 hvok10,
        wireVal_of_ext hx (extends_trans e711 (extends_trans he12 he13)) hwnbad vnbad,
        wireVal_of_ext hx (extends_trans he11 (extends_trans he12 he13)) hwnf10 vnf10]; rfl
  · rw [hvok11,
        wireVal_of_ext hx (extends_trans e711 (extends_trans he12 (extends_trans he13 he14))) hwnbad vnbad,
        wireVal_of_ext hx (extends_trans he12 (extends_trans he13 he14)) hwnf11 vnf11]; rfl

structure TailWires where
  ok : Nat
  b1 : Nat
  b2 : Nat

def TailWires.lt (tw : TailWires) (bound : Nat) : Prop :=
  tw.ok < bound ∧ tw.b1 < bound ∧ tw.b2 < bound

def TailWires.matches (tw : TailWires) (gs : List Gate) (x : List Bool) (st : TailState) : Prop :=
  wireVal gs x tw.ok = st.ok ∧ wireVal gs x tw.b1 = st.b1 ∧ wireVal gs x tw.b2 = st.b2

lemma tailWires_ext {n : Nat} {tw : TailWires} {st : TailState} {gs1 gs2 : List Gate} {x : List Bool}
    (hx : x.length = n) (hlt : tw.lt (n + gs1.length)) (hm : tw.matches gs1 x st) (he : Extends gs1 gs2) :
    tw.lt (n + gs2.length) ∧ tw.matches gs2 x st := by
  have hlen := ext_len he
  rcases hlt with ⟨h1, h2, h3⟩
  rcases hm with ⟨m1, m2, m3⟩
  refine ⟨⟨by omega, by omega, by omega⟩,
    ⟨wireVal_of_ext hx he h1 m1, wireVal_of_ext hx he h2 m2, wireVal_of_ext hx he h3 m3⟩⟩

def emitTailStep (n : Nat) (gs : List Gate) (bw : BitWires) (tw : TailWires) : List Gate × TailWires :=
  let (g1, wok) := emitMux4 n gs tw.b1 tw.b2 bw.ok00 bw.ok01 bw.ok10 bw.ok11
  let (g2, wok') := emitAnd n g1 tw.ok wok
  let (g3, wnb1) := emitNot n g2 tw.b1
  let (g4, wand) := emitAnd n g3 wnb1 tw.b2
  let (g5, wv) := emitXor n g4 wand bw.bout
  (g5, ⟨wok', wv, tw.b1⟩)

lemma emitTailStep_spec {k m d s t i : Nat} {gs : List Gate} {bw : BitWires} {tw : TailWires} {st : TailState}
    (hg : Good ((m + 3) * k) gs) (hbw : bw.lt ((m + 3) * k + gs.length))
    (htw : tw.lt ((m + 3) * k + gs.length))
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc c : Fin (2 ^ k))
    (hbout : wireVal gs (inputVec base gen cr cc) bw.bout = baseOutBit t base c i)
    (h00 : wireVal gs (inputVec base gen cr cc) bw.ok00 = bitOk d s t base gen i false false)
    (h01 : wireVal gs (inputVec base gen cr cc) bw.ok01 = bitOk d s t base gen i false true)
    (h10 : wireVal gs (inputVec base gen cr cc) bw.ok10 = bitOk d s t base gen i true false)
    (h11 : wireVal gs (inputVec base gen cr cc) bw.ok11 = bitOk d s t base gen i true true)
    (hmatch : tw.matches gs (inputVec base gen cr cc) st) :
    let x := inputVec base gen cr cc
    let r := emitTailStep ((m + 3) * k) gs bw tw
    Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + 19 ∧
      r.2.lt ((m + 3) * k + r.1.length) ∧
      r.2.matches r.1 x (tailStep d s t base gen c i st) := by
  dsimp only
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  rcases hbw with ⟨hbout_lt, h00_lt, h01_lt, h10_lt, h11_lt⟩
  rcases htw with ⟨hok_lt, hb1_lt, hb2_lt⟩
  rcases hmatch with ⟨mok, mb1, mb2⟩
  unfold emitTailStep
  rcases h1 : emitMux4 n gs tw.b1 tw.b2 bw.ok00 bw.ok01 bw.ok10 bw.ok11 with ⟨g1, wok⟩; dsimp only
  have q1 := emitMux4_spec (s1 := tw.b1) (s2 := tw.b2) (v00 := bw.ok00) (v01 := bw.ok01) (v10 := bw.ok10) (v11 := bw.ok11) hg hb1_lt hb2_lt h00_lt h01_lt h10_lt h11_lt x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwok, hvok⟩
  rcases h2 : emitAnd n g1 tw.ok wok with ⟨g2, wok'⟩; dsimp only
  have q2 := emitAnd_spec (a := tw.ok) (b := wok) hg1 (by omega) hwok x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwok', hvok'⟩
  rcases h3 : emitNot n g2 tw.b1 with ⟨g3, wnb1⟩; dsimp only
  have q3 := emitNot_spec (a := tw.b1) hg2 (by omega) x hx; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hwnb1, hvnb1⟩
  rcases h4 : emitAnd n g3 wnb1 tw.b2 with ⟨g4, wand⟩; dsimp only
  have q4 := emitAnd_spec (a := wnb1) (b := tw.b2) hg3 hwnb1 (by omega) x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwand, hvand⟩
  rcases h5 : emitXor n g4 wand bw.bout with ⟨g5, wv⟩; dsimp only
  have q5 := emitXor_spec (a := wand) (b := bw.bout) hg4 hwand (by omega) x hx; rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hwv, hvv⟩
  have e05 := extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4 he5)))
  dsimp only [TailWires.lt]
  refine ⟨hg5, e05, by omega, ⟨by omega, hwv, by omega⟩, ?_, ?_, ?_⟩
  · rw [wireVal_of_ext hx (extends_trans he3 (extends_trans he4 he5)) hwok' hvok',
        wireVal_of_ext hx he1 hok_lt mok, hvok, mb1, mb2]
    cases hst1 : st.b1 <;> cases hst2 : st.b2 <;> simp [tailStep, hst1, hst2, h00, h01, h10, h11]
  · rw [hvv, hvand, hvnb1,
        wireVal_of_ext hx (extends_trans he1 he2) hb1_lt mb1,
        wireVal_of_ext hx (extends_trans he1 (extends_trans he2 he3)) hb2_lt mb2,
        wireVal_of_ext hx (extends_trans he1 (extends_trans he2 (extends_trans he3 he4))) hbout_lt hbout]; rfl
  · exact wireVal_of_ext hx e05 hb1_lt mb1

structure FourTails where
  t00 : TailWires
  t01 : TailWires
  t10 : TailWires
  t11 : TailWires

def FourTails.lt (ft : FourTails) (bound : Nat) : Prop :=
  ft.t00.lt bound ∧ ft.t01.lt bound ∧ ft.t10.lt bound ∧ ft.t11.lt bound

def emitBackLoop (k m d s t cOff wFalse wTrue : Nat) (gs : List Gate) : Nat → List Gate × FourTails
  | 0 =>
    let wDiff := if k = 1 then wFalse else wTrue
    (gs, ⟨⟨wTrue, wFalse, wFalse⟩, ⟨wDiff, wFalse, wTrue⟩, ⟨wDiff, wTrue, wFalse⟩, ⟨wTrue, wTrue, wTrue⟩⟩)
  | step + 1 =>
    let n := (m + 3) * k
    let (g0, ft) := emitBackLoop k m d s t cOff wFalse wTrue gs step
    let (g1, bw) := emitBitWires k m d s t cOff (k - 1 - step) wFalse g0
    let (g2, nt00) := emitTailStep n g1 bw ft.t00
    let (g3, nt01) := emitTailStep n g2 bw ft.t01
    let (g4, nt10) := emitTailStep n g3 bw ft.t10
    let (g5, nt11) := emitTailStep n g4 bw ft.t11
    (g5, ⟨nt00, nt01, nt10, nt11⟩)

lemma emitBackLoop_spec {k m d s t cOff wFalse wTrue : Nat} (hk : 0 < k)
    (hcOff : cOff + k ≤ (m + 3) * k)
    {gs : List Gate} (hg : Good ((m + 3) * k) gs)
    (hwf : wFalse < (m + 3) * k + gs.length) (hwt : wTrue < (m + 3) * k + gs.length)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc c : Fin (2 ^ k))
    (hc_in : ∀ i, i < k → (inputVec base gen cr cc).getD (cOff + i) false = c.val.testBit i)
    (hwf_val : wireVal gs (inputVec base gen cr cc) wFalse = false)
    (hwt_val : wireVal gs (inputVec base gen cr cc) wTrue = true) :
    ∀ step, step ≤ k →
      let x := inputVec base gen cr cc
      let r := emitBackLoop k m d s t cOff wFalse wTrue gs step
      Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length = gs.length + (58 * m + 94) * step ∧
        r.2.lt ((m + 3) * k + r.1.length) ∧
        r.2.t00.matches r.1 x (tailRun d s t base gen c false false step) ∧
        r.2.t01.matches r.1 x (tailRun d s t base gen c false true step) ∧
        r.2.t10.matches r.1 x (tailRun d s t base gen c true false step) ∧
        r.2.t11.matches r.1 x (tailRun d s t base gen c true true step) := by
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  intro step
  induction step with
  | zero =>
    intro _
    dsimp only [emitBackLoop, tailRun]
    have hwd : (if k = 1 then wFalse else wTrue) < n + gs.length := by split_ifs <;> assumption
    have hwd_val : wireVal gs x (if k = 1 then wFalse else wTrue) = (if k = 1 then false else true) := by
      split_ifs <;> assumption
    refine ⟨hg, extends_refl gs, by simp,
      ⟨⟨hwt, hwf, hwf⟩, ⟨hwd, hwf, hwt⟩, ⟨hwd, hwt, hwf⟩, ⟨hwt, hwt, hwt⟩⟩,
      ⟨by split_ifs <;> exact hwt_val, hwf_val, hwf_val⟩,
      ⟨by simpa using hwd_val, hwf_val, hwt_val⟩,
      ⟨by simpa using hwd_val, hwt_val, hwf_val⟩,
      ⟨by split_ifs <;> exact hwt_val, hwt_val, hwt_val⟩⟩
  | succ step ih =>
    intro hle
    dsimp only
    unfold emitBackLoop
    rcases h0 : emitBackLoop k m d s t cOff wFalse wTrue gs step with ⟨g0, ft⟩; dsimp only
    have q0 := ih (by omega); rw [h0] at q0; dsimp only at q0
    rcases q0 with ⟨hg0, he0, hl0, ⟨lt00, lt01, lt10, lt11⟩, m00, m01, m10, m11⟩
    have hi : k - 1 - step < k := by omega
    have hwf0 : wFalse < n + g0.length := by omega
    have hwf0_val : wireVal g0 x wFalse = false := wireVal_of_ext hx he0 hwf hwf_val
    rcases h1 : emitBitWires k m d s t cOff (k - 1 - step) wFalse g0 with ⟨g1, bw⟩; dsimp only
    have q1 := emitBitWires_spec (d := d) (s := s) (t := t) hk hi hcOff hg0 hwf0 base gen cr cc c (hc_in _ hi) hwf0_val
    rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hbw1, vb1, v00, v01, v10, v11⟩
    have e00 := tailWires_ext hx lt00 m00 he1
    rcases h2 : emitTailStep n g1 bw ft.t00 with ⟨g2, nt00⟩; dsimp only
    have q2 := emitTailStep_spec hg1 hbw1 e00.1 base gen cr cc c vb1 v00 v01 v10 v11 e00.2
    rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hlt2, hm2⟩
    have bw_ext : ∀ {ga gb : List Gate}, bw.lt (n + ga.length) → Extends ga gb →
        wireVal ga x bw.bout = baseOutBit t base c (k - 1 - step) →
        wireVal ga x bw.ok00 = bitOk d s t base gen (k - 1 - step) false false →
        wireVal ga x bw.ok01 = bitOk d s t base gen (k - 1 - step) false true →
        wireVal ga x bw.ok10 = bitOk d s t base gen (k - 1 - step) true false →
        wireVal ga x bw.ok11 = bitOk d s t base gen (k - 1 - step) true true →
        bw.lt (n + gb.length) ∧
        wireVal gb x bw.bout = baseOutBit t base c (k - 1 - step) ∧
        wireVal gb x bw.ok00 = bitOk d s t base gen (k - 1 - step) false false ∧
        wireVal gb x bw.ok01 = bitOk d s t base gen (k - 1 - step) false true ∧
        wireVal gb x bw.ok10 = bitOk d s t base gen (k - 1 - step) true false ∧
        wireVal gb x bw.ok11 = bitOk d s t base gen (k - 1 - step) true true := by
      intro ga gb hlt he hb a00 a01 a10 a11
      have hl := ext_len he
      rcases hlt with ⟨h1, h2, h3, h4, h5⟩
      refine ⟨⟨by omega, by omega, by omega, by omega, by omega⟩,
        wireVal_of_ext hx he h1 hb, wireVal_of_ext hx he h2 a00,
        wireVal_of_ext hx he h3 a01, wireVal_of_ext hx he h4 a10,
        wireVal_of_ext hx he h5 a11⟩
    rcases bw_ext hbw1 he2 vb1 v00 v01 v10 v11 with ⟨hbw2, vb2, u00, u01, u10, u11⟩
    have e01 := tailWires_ext hx lt01 m01 (extends_trans he1 he2)
    rcases h3 : emitTailStep n g2 bw ft.t01 with ⟨g3, nt01⟩; dsimp only
    have q3 := emitTailStep_spec hg2 hbw2 e01.1 base gen cr cc c vb2 u00 u01 u10 u11 e01.2
    rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hlt3, hm3⟩
    rcases bw_ext hbw2 he3 vb2 u00 u01 u10 u11 with ⟨hbw3, vb3, w00, w01, w10, w11⟩
    have e10 := tailWires_ext hx lt10 m10 (extends_trans he1 (extends_trans he2 he3))
    rcases h4 : emitTailStep n g3 bw ft.t10 with ⟨g4, nt10⟩; dsimp only
    have q4 := emitTailStep_spec hg3 hbw3 e10.1 base gen cr cc c vb3 w00 w01 w10 w11 e10.2
    rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hlt4, hm4⟩
    rcases bw_ext hbw3 he4 vb3 w00 w01 w10 w11 with ⟨hbw4, vb4, z00, z01, z10, z11⟩
    have e11 := tailWires_ext hx lt11 m11 (extends_trans he1 (extends_trans he2 (extends_trans he3 he4)))
    rcases h5 : emitTailStep n g4 bw ft.t11 with ⟨g5, nt11⟩; dsimp only
    have q5 := emitTailStep_spec hg4 hbw4 e11.1 base gen cr cc c vb4 z00 z01 z10 z11 e11.2
    rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hlt5, hm5⟩
    have f00 := tailWires_ext hx hlt2 hm2 (extends_trans he3 (extends_trans he4 he5))
    have f01 := tailWires_ext hx hlt3 hm3 (extends_trans he4 he5)
    have f10 := tailWires_ext hx hlt4 hm4 he5
    have hmul : (58 * m + 94) * (step + 1) = (58 * m + 94) * step + (58 * m + 94) :=
      Nat.mul_succ (58 * m + 94) step
    refine ⟨hg5, extends_trans he0 (extends_trans he1 (extends_trans he2 (extends_trans he3 (extends_trans he4 he5)))),
      by omega, ⟨f00.1, f01.1, f10.1, hlt5⟩, f00.2, f01.2, f10.2, hm5⟩

def emitSeamOne (n k h : Nat) (gs : List Gate) (tw : TailWires) (wt0 wt1 : Nat) : List Gate × Nat :=
  if h = k then
    let (g1, e0) := emitEq n gs tw.b1 wt0
    let (g2, e1) := emitEq n g1 tw.b2 wt1
    let (g3, a0) := emitAnd n g2 tw.ok e0
    emitAnd n g3 a0 e1
  else if h + 1 = k then
    let (g1, e1) := emitEq n gs tw.b1 wt1
    emitAnd n g1 tw.ok e1
  else
    (gs, tw.ok)

lemma emitSeamOne_spec {n k h : Nat} {gs : List Gate} {tw : TailWires} {wt0 wt1 : Nat}
    {st : TailState} {t0 t1 : Bool}
    (hg : Good n gs) (htw : tw.lt (n + gs.length))
    (ht0 : wt0 < n + gs.length) (ht1 : wt1 < n + gs.length)
    (x : List Bool) (hx : x.length = n)
    (hmatch : tw.matches gs x st)
    (hvt0 : wireVal gs x wt0 = t0) (hvt1 : wireVal gs x wt1 = t1) :
    let r := emitSeamOne n k h gs tw wt0 wt1
    Good n r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + 12 ∧ r.2 < n + r.1.length ∧
      wireVal r.1 x r.2 =
        (if h = k then st.ok && (st.b1 == t0) && (st.b2 == t1)
         else if h + 1 = k then st.ok && (st.b1 == t1)
         else st.ok) := by
  dsimp only
  rcases htw with ⟨hok_lt, hb1_lt, hb2_lt⟩
  rcases hmatch with ⟨mok, mb1, mb2⟩
  unfold emitSeamOne
  split_ifs with hk1 hk2
  · rcases h1 : emitEq n gs tw.b1 wt0 with ⟨g1, e0⟩; dsimp only
    have q1 := emitEq_spec (a := tw.b1) (b := wt0) hg hb1_lt ht0 x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, he0, hve0⟩
    rcases h2 : emitEq n g1 tw.b2 wt1 with ⟨g2, e1⟩; dsimp only
    have q2 := emitEq_spec (a := tw.b2) (b := wt1) hg1 (by omega) (by omega) x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, he1', hve1⟩
    rcases h3 : emitAnd n g2 tw.ok e0 with ⟨g3, a0⟩; dsimp only
    have q3 := emitAnd_spec (a := tw.ok) (b := e0) hg2 (by omega) (by omega) x hx; rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, ha0, hva0⟩
    rcases h4 : emitAnd n g3 a0 e1 with ⟨g4, wr⟩; dsimp only
    have q4 := emitAnd_spec (a := a0) (b := e1) hg3 ha0 (by omega) x hx; rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hwr, hvr⟩
    refine ⟨hg4, extends_trans he1 (extends_trans he2 (extends_trans he3 he4)), by omega, hwr, ?_⟩
    rw [hvr, hva0, wireVal_of_ext hx (extends_trans he1 he2) hok_lt mok,
        wireVal_of_ext hx he2 he0 hve0, mb1, hvt0,
        wireVal_of_ext hx he3 he1' hve1,
        wireVal_of_ext hx he1 hb2_lt mb2, wireVal_of_ext hx he1 ht1 hvt1]
  · rcases h1 : emitEq n gs tw.b1 wt1 with ⟨g1, e1⟩; dsimp only
    have q1 := emitEq_spec (a := tw.b1) (b := wt1) hg hb1_lt ht1 x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, he1', hve1⟩
    rcases h2 : emitAnd n g1 tw.ok e1 with ⟨g2, wr⟩; dsimp only
    have q2 := emitAnd_spec (a := tw.ok) (b := e1) hg1 (by omega) he1' x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwr, hvr⟩
    refine ⟨hg2, extends_trans he1 he2, by omega, hwr, ?_⟩
    rw [hvr, wireVal_of_ext hx he1 hok_lt mok, hve1, mb1, hvt1]
  · dsimp only
    exact ⟨hg, extends_refl gs, by omega, hok_lt, mok⟩

def emitSide (k m h d s t cOff wFalse wTrue : Nat) (gs : List Gate) :
    List Gate × Nat × Nat × Nat × Nat :=
  let n := (m + 3) * k
  let (g0, ft) := emitBackLoop k m d s t cOff wFalse wTrue gs h
  let (g1, v00) := emitSeamOne n k h g0 ft.t00 wFalse wFalse
  let (g2, v01) := emitSeamOne n k h g1 ft.t01 wFalse wTrue
  let (g3, v10) := emitSeamOne n k h g2 ft.t10 wTrue wFalse
  let (g4, v11) := emitSeamOne n k h g3 ft.t11 wTrue wTrue
  (g4, v00, v01, v10, v11)

lemma emitSide_spec {k m h d s t cOff wFalse wTrue : Nat} (hk : 0 < k) (hh : h ≤ k)
    (hcOff : cOff + k ≤ (m + 3) * k)
    {gs : List Gate} (hg : Good ((m + 3) * k) gs)
    (hwf : wFalse < (m + 3) * k + gs.length) (hwt : wTrue < (m + 3) * k + gs.length)
    (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc c : Fin (2 ^ k))
    (hc_in : ∀ i, i < k → (inputVec base gen cr cc).getD (cOff + i) false = c.val.testBit i)
    (hwf_val : wireVal gs (inputVec base gen cr cc) wFalse = false)
    (hwt_val : wireVal gs (inputVec base gen cr cc) wTrue = true) :
    let x := inputVec base gen cr cc
    let r := emitSide k m h d s t cOff wFalse wTrue gs
    Good ((m + 3) * k) r.1 ∧ Extends gs r.1 ∧ r.1.length ≤ gs.length + (58 * m + 94) * k + 48 ∧
      r.2.1 < (m + 3) * k + r.1.length ∧
      r.2.2.1 < (m + 3) * k + r.1.length ∧
      r.2.2.2.1 < (m + 3) * k + r.1.length ∧
      r.2.2.2.2 < (m + 3) * k + r.1.length ∧
      wireVal r.1 x r.2.1 = validTail h d s t base gen c false false ∧
      wireVal r.1 x r.2.2.1 = validTail h d s t base gen c false true ∧
      wireVal r.1 x r.2.2.2.1 = validTail h d s t base gen c true false ∧
      wireVal r.1 x r.2.2.2.2 = validTail h d s t base gen c true true := by
  dsimp only
  set n := (m + 3) * k with hn_def
  set x := inputVec base gen cr cc
  have hx : x.length = n := inputVec_len base gen cr cc
  unfold emitSide
  rcases h0 : emitBackLoop k m d s t cOff wFalse wTrue gs h with ⟨g0, ft⟩; dsimp only
  have q0 := emitBackLoop_spec (d := d) (s := s) (t := t) hk hcOff hg hwf hwt base gen cr cc c hc_in hwf_val hwt_val h hh
  rw [h0] at q0; dsimp only at q0; rcases q0 with ⟨hg0, he0, hl0, ⟨lt00, lt01, lt10, lt11⟩, m00, m01, m10, m11⟩
  have hwf0 := wireVal_of_ext hx he0 hwf hwf_val
  have hwt0 := wireVal_of_ext hx he0 hwt hwt_val
  rcases h1 : emitSeamOne n k h g0 ft.t00 wFalse wFalse with ⟨g1, v00⟩; dsimp only
  have q1 := emitSeamOne_spec (k := k) (h := h) hg0 lt00 (by omega) (by omega) x hx m00 hwf0 hwf0
  rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hv00_lt, hv00⟩
  have h01l := ext_len he1
  have e01 := tailWires_ext hx lt01 m01 he1
  have hwf1 := wireVal_of_ext hx (extends_trans he0 he1) hwf hwf_val
  have hwt1 := wireVal_of_ext hx (extends_trans he0 he1) hwt hwt_val
  rcases h2 : emitSeamOne n k h g1 ft.t01 wFalse wTrue with ⟨g2, v01⟩; dsimp only
  have q2 := emitSeamOne_spec (k := k) (h := h) hg1 e01.1 (by omega) (by omega) x hx e01.2 hwf1 hwt1
  rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hv01_lt, hv01⟩
  have h12l := ext_len he2
  have e10 := tailWires_ext hx lt10 m10 (extends_trans he1 he2)
  have hwf2 := wireVal_of_ext hx (extends_trans he0 (extends_trans he1 he2)) hwf hwf_val
  have hwt2 := wireVal_of_ext hx (extends_trans he0 (extends_trans he1 he2)) hwt hwt_val
  rcases h3 : emitSeamOne n k h g2 ft.t10 wTrue wFalse with ⟨g3, v10⟩; dsimp only
  have q3 := emitSeamOne_spec (k := k) (h := h) hg2 e10.1 (by omega) (by omega) x hx e10.2 hwt2 hwf2
  rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hv10_lt, hv10⟩
  have h23l := ext_len he3
  have e11 := tailWires_ext hx lt11 m11 (extends_trans he1 (extends_trans he2 he3))
  have hwt3 := wireVal_of_ext hx (extends_trans he0 (extends_trans he1 (extends_trans he2 he3))) hwt hwt_val
  rcases h4 : emitSeamOne n k h g3 ft.t11 wTrue wTrue with ⟨g4, v11⟩; dsimp only
  have q4 := emitSeamOne_spec (k := k) (h := h) hg3 e11.1 (by omega) (by omega) x hx e11.2 hwt3 hwt3
  rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hv11_lt, hv11⟩
  have h34l := ext_len he4
  have hhk_mul : (58 * m + 94) * h ≤ (58 * m + 94) * k := Nat.mul_le_mul_left _ hh
  refine ⟨hg4, extends_trans he0 (extends_trans he1 (extends_trans he2 (extends_trans he3 he4))),
    by omega, by omega, by omega, by omega, hv11_lt,
    wireVal_of_ext hx (extends_trans he2 (extends_trans he3 he4)) hv00_lt hv00,
    wireVal_of_ext hx (extends_trans he3 he4) hv01_lt hv01,
    wireVal_of_ext hx he4 hv10_lt hv10, hv11⟩

def buildCircuit (k m hr hc : Nat) : List Gate × (Fin 5 → Nat) :=
  let n := (m + 3) * k
  let (g1, wFalse) := emitFalse n []
  let (g2, wTrue) := emitTrue n g1
  let (g3, r00, r01, r10, r11) := emitSide k m hr 1 1 0 ((m + 1) * k) wFalse wTrue g2
  let (g4, c00, c01, c10, c11) := emitSide k m hc 2 3 4 ((m + 2) * k) wFalse wTrue g3
  let (g5, ra0, ra1, ra2) := emitPop4 n g4 r00 r01 r10 r11
  let (g6, ca0, ca1, ca2) := emitPop4 n g5 c00 c01 c10 c11
  emitMul3 n g6 ra0 ra1 ra2 ca0 ca1 ca2

lemma buildCircuit_spec {k m hr hc : Nat} (hk : 0 < k) (hhr : hr ≤ k) (hhc : hc ≤ k) :
    let n := (m + 3) * k
    let res := buildCircuit k m hr hc
    Good n res.1 ∧ res.1.length ≤ 512 * (k + 1) * (m + 1) ∧
      (∀ i : Fin 5, res.2 i < n + res.1.length) ∧
      ∀ (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k)),
        let z := sideCount hr 1 1 0 base gen cr * sideCount hc 2 3 4 base gen cc
        ∀ i : Fin 5, wireVal res.1 (inputVec base gen cr cc) (res.2 i) = z.testBit i.val := by
  set n := (m + 3) * k with hn_def
  have hgood0 : Good n [] := ⟨(fun g hg => nomatch hg), (fun j hj => nomatch hj)⟩
  have hcr_off : (m + 1) * k + k ≤ n := by
    have h1 : (m + 1) * k = m * k + k := Nat.succ_mul m k
    have h2 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
    omega
  have hcc_off : (m + 2) * k + k ≤ n := by
    have h1 : (m + 2) * k = m * k + 2 * k := Nat.add_mul m 2 k
    have h2 : (m + 3) * k = m * k + 3 * k := Nat.add_mul m 3 k
    omega
  have hmain : ∀ (base : Fin (2 ^ k)) (gen : Fin m → Fin (2 ^ k)) (cr cc : Fin (2 ^ k)),
      let x := inputVec base gen cr cc
      let res := buildCircuit k m hr hc
      Good n res.1 ∧ res.1.length ≤ 512 * (k + 1) * (m + 1) ∧
        (∀ i : Fin 5, res.2 i < n + res.1.length) ∧
        ∀ i : Fin 5, wireVal res.1 x (res.2 i) =
          (sideCount hr 1 1 0 base gen cr * sideCount hc 2 3 4 base gen cc).testBit i.val := by
    intro base gen cr cc
    dsimp only
    set x := inputVec base gen cr cc
    have hx : x.length = n := inputVec_len base gen cr cc
    unfold buildCircuit
    dsimp only
    simp only [← hn_def]
    rcases h1 : emitFalse n [] with ⟨g1, wFalse⟩; dsimp only
    have q1 := emitFalse_spec hgood0 x hx; rw [h1] at q1; dsimp only at q1; rcases q1 with ⟨hg1, he1, hl1, hwf, hvf⟩
    rcases h2 : emitTrue n g1 with ⟨g2, wTrue⟩; dsimp only
    have q2 := emitTrue_spec hg1 x hx; rw [h2] at q2; dsimp only at q2; rcases q2 with ⟨hg2, he2, hl2, hwt, hvt⟩
    have hwf2 := wireVal_of_ext hx he2 hwf hvf
    rcases h3 : emitSide k m hr 1 1 0 ((m + 1) * k) wFalse wTrue g2 with ⟨g3, r00, r01, r10, r11⟩; dsimp only
    have q3 := emitSide_spec (h := hr) (d := 1) (s := 1) (t := 0) hk hhr hcr_off hg2 (by omega) hwt base gen cr cc cr
      (fun i hi => inputVec_cr base gen cr cc hi) hwf2 hvt
    rw [h3] at q3; dsimp only at q3; rcases q3 with ⟨hg3, he3, hl3, hr00, hr01, hr10, hr11, hvr00, hvr01, hvr10, hvr11⟩
    have h23 := ext_len he3
    have hwf3 := wireVal_of_ext hx (extends_trans he2 he3) hwf hvf
    have hwt3 := wireVal_of_ext hx he3 hwt hvt
    rcases h4 : emitSide k m hc 2 3 4 ((m + 2) * k) wFalse wTrue g3 with ⟨g4, c00, c01, c10, c11⟩; dsimp only
    have q4 := emitSide_spec (h := hc) (d := 2) (s := 3) (t := 4) hk hhc hcc_off hg3 (by omega) (by omega) base gen cr cc cc
      (fun i hi => inputVec_cc base gen cr cc hi) hwf3 hwt3
    rw [h4] at q4; dsimp only at q4; rcases q4 with ⟨hg4, he4, hl4, hc00, hc01, hc10, hc11, hvc00, hvc01, hvc10, hvc11⟩
    have h34 := ext_len he4
    rcases h5 : emitPop4 n g4 r00 r01 r10 r11 with ⟨g5, ra0, ra1, ra2⟩; dsimp only
    have q5 := emitPop4_spec (b0 := r00) (b1 := r01) (b2 := r10) (b3 := r11) hg4 (by omega) (by omega) (by omega) (by omega) x hx
    rw [h5] at q5; dsimp only at q5; rcases q5 with ⟨hg5, he5, hl5, hra0, hra1, hra2, hvra0, hvra1, hvra2⟩
    rcases h6 : emitPop4 n g5 c00 c01 c10 c11 with ⟨g6, ca0, ca1, ca2⟩; dsimp only
    have q6 := emitPop4_spec (b0 := c00) (b1 := c01) (b2 := c10) (b3 := c11) hg5 (by omega) (by omega) (by omega) (by omega) x hx
    rw [h6] at q6; dsimp only at q6; rcases q6 with ⟨hg6, he6, hl6, hca0, hca1, hca2, hvca0, hvca1, hvca2⟩
    rcases h7 : emitMul3 n g6 ra0 ra1 ra2 ca0 ca1 ca2 with ⟨g7, ans⟩; dsimp only
    have q7 := emitMul3_spec (r0 := ra0) (r1 := ra1) (r2 := ra2) (c0 := ca0) (c1 := ca1) (c2 := ca2) hg6 (by omega) (by omega) (by omega) hca0 hca1 hca2 x hx
    rw [h7] at q7; dsimp only at q7; rcases q7 with ⟨hg7, _, hl7, hans_lt, hans_val⟩
    have hsz : g7.length ≤ 512 * (k + 1) * (m + 1) := by
      have hprod : 512 * (k + 1) * (m + 1) = 512 * (k * m) + 512 * k + 512 * m + 512 := by ring
      have hstep : (58 * m + 94) * k = 58 * (k * m) + 94 * k := by ring
      have hl0 : ([] : List Gate).length = 0 := rfl
      rw [hstep] at hl3 hl4
      rw [hprod]
      omega
    refine ⟨hg7, hsz, hans_lt, ?_⟩
    intro i
    rw [hans_val i]
    have r00_4 := wireVal_of_ext hx he4 hr00 hvr00
    have r01_4 := wireVal_of_ext hx he4 hr01 hvr01
    have r10_4 := wireVal_of_ext hx he4 hr10 hvr10
    have r11_4 := wireVal_of_ext hx he4 hr11 hvr11
    have c00_5 := wireVal_of_ext hx he5 hc00 hvc00
    have c01_5 := wireVal_of_ext hx he5 hc01 hvc01
    have c10_5 := wireVal_of_ext hx he5 hc10 hvc10
    have c11_5 := wireVal_of_ext hx he5 hc11 hvc11
    rw [wireVal_of_ext hx he6 hra0 hvra0, wireVal_of_ext hx he6 hra1 hvra1, wireVal_of_ext hx he6 hra2 hvra2,
        hvca0, hvca1, hvca2, r00_4, r01_4, r10_4, r11_4, c00_5, c01_5, c10_5, c11_5]
    set pr := pop4Spec (validTail hr 1 1 0 base gen cr false false)
      (validTail hr 1 1 0 base gen cr false true) (validTail hr 1 1 0 base gen cr true false)
      (validTail hr 1 1 0 base gen cr true true)
    set pc := pop4Spec (validTail hc 2 3 4 base gen cc false false)
      (validTail hc 2 3 4 base gen cc false true) (validTail hc 2 3 4 base gen cc true false)
      (validTail hc 2 3 4 base gen cc true true)
    have hpr : pr.1.toNat + 2 * pr.2.1.toNat + 4 * pr.2.2.toNat = sideCount hr 1 1 0 base gen cr :=
      pop4Spec_val _ _ _ _
    have hpc : pc.1.toNat + 2 * pc.2.1.toNat + 4 * pc.2.2.toNat = sideCount hc 2 3 4 base gen cc :=
      pop4Spec_val _ _ _ _
    have hlr := sideCount_le_four hr 1 1 0 base gen cr
    have hlc := sideCount_le_four hc 2 3 4 base gen cc
    rw [mul3Spec_testBit pr.1 pr.2.1 pr.2.2 pc.1 pc.2.1 pc.2.2 (by omega) (by omega) i, hpr, hpc]
  have hz0 : Fin (2 ^ k) := ⟨0, Nat.two_pow_pos k⟩
  have h0 := hmain hz0 (fun _ => hz0) hz0 hz0
  exact ⟨h0.1, h0.2.1, h0.2.2.1, fun base gen cr cc => (hmain base gen cr cc).2.2.2⟩

end PEqualNP.Outside.L_meta_25640_aux

theorem PEqualNP.Outside.L_meta_25640 :
∀ (k m hr hc : Nat), 0 < k → k % 3 ≠ 0 → hr ≤ k → hc ≤ k →
  let W := Fin (2 ^ k)
  let rot := fun (s x : Nat) => ((x <<< (s % k)) ||| (x >>> (k - s % k))) % 2 ^ k
  let chi := fun (x : Nat) => (List.range k).foldl (fun acc i =>
    acc ||| ((xor (x.testBit i) (!(x.testBit ((i+1)%k)) && x.testBit ((i+2)%k))).toNat <<< i)) 0
  let run := fun (d s t key name c : Nat) =>
    let z := rot s key ^^^ name
    chi (z ^^^ rot d z ^^^ rot (k - d%k) z) ^^^ rot t key ^^^ c
  let pack := fun (w : W) => (List.range k).map (fun pos => w.val.testBit pos)
  let inputs := (m+3)*k
  ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (ans : Fin 5 → Fin (inputs+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
    C.size ≤ 512*(k+1)*(m+1) ∧
    ∀ (base : W) (gen : Fin m → W) (cr cc : W),
      let key := fun (mask : Fin (2^m)) =>
        (List.ofFn (fun genIndex : Fin m => if mask.val.testBit genIndex.val then (gen genIndex).val else 0)).foldl Nat.xor base.val
      let shared := Nat.card { uv : W × W // ∀ mask : Fin (2^m),
        run 1 1 0 (key mask) uv.1.val cr.val < 2^(k-hr) ∧
        run 2 3 4 (key mask) uv.2.val cc.val < 2^(k-hc) }
      let x := pack base ++ (List.ofFn (fun inputIndex : Fin m => pack (gen inputIndex))).flatten ++ pack cr ++ pack cc
      ∃ z : Nat, z ≤ 16 ∧ shared = 2^((k-(hr+2))+(k-(hc+2)))*z ∧
        ∀ i : Fin 5, (C.wires x).getD (ans i).val false = z.testBit i.val := by
  intro k m hr hc hk hk3 hhr hhc
  dsimp only
  have hspec := PEqualNP.Outside.L_meta_25640_aux.buildCircuit_spec (m := m) hk hhr hhc
  set res := PEqualNP.Outside.L_meta_25640_aux.buildCircuit k m hr hc
  refine ⟨⟨res.1, 0⟩, fun i => ⟨res.2 i, hspec.2.2.1 i⟩, hspec.1.1, hspec.1.2, hspec.2.1, ?_⟩
  intro base gen cr cc
  dsimp only
  set zr := PEqualNP.Outside.L_meta_25640_aux.sideCount hr 1 1 0 base gen cr
  set zc := PEqualNP.Outside.L_meta_25640_aux.sideCount hc 2 3 4 base gen cc
  have hzr : zr ≤ 4 := PEqualNP.Outside.L_meta_25640_aux.sideCount_le_four hr 1 1 0 base gen cr
  have hzc : zc ≤ 4 := PEqualNP.Outside.L_meta_25640_aux.sideCount_le_four hc 2 3 4 base gen cc
  refine ⟨zr * zc, by nlinarith, ?_, hspec.2.2.2 base gen cr cc⟩
  have hprod_eq : { uv : Fin (2 ^ k) × Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
      PEqualNP.Outside.L_meta_25640_aux.run k 1 1 0
        (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) uv.1.val cr.val < 2 ^ (k - hr) ∧
      PEqualNP.Outside.L_meta_25640_aux.run k 2 3 4
        (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) uv.2.val cc.val < 2 ^ (k - hc) } ≃
      { u : Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
        PEqualNP.Outside.L_meta_25640_aux.run k 1 1 0
          (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) u.val cr.val < 2 ^ (k - hr) } ×
      { v : Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
        PEqualNP.Outside.L_meta_25640_aux.run k 2 3 4
          (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) v.val cc.val < 2 ^ (k - hc) } :=
    { toFun := fun ⟨⟨u, v⟩, h⟩ => (⟨u, fun mask => (h mask).1⟩, ⟨v, fun mask => (h mask).2⟩)
      invFun := fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => ⟨(u, v), fun mask => ⟨hu mask, hv mask⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
  change Nat.card { uv : Fin (2 ^ k) × Fin (2 ^ k) // ∀ mask : Fin (2 ^ m),
      PEqualNP.Outside.L_meta_25640_aux.run k 1 1 0
        (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) uv.1.val cr.val < 2 ^ (k - hr) ∧
      PEqualNP.Outside.L_meta_25640_aux.run k 2 3 4
        (PEqualNP.Outside.L_meta_25640_aux.keyVal base gen mask) uv.2.val cc.val < 2 ^ (k - hc) } = _
  rw [Nat.card_congr hprod_eq, Nat.card_prod,
      PEqualNP.Outside.L_meta_25640_aux.side_card_eq hk hk3 hhr 1 1 0 base gen cr,
      PEqualNP.Outside.L_meta_25640_aux.side_card_eq hk hk3 hhc 2 3 4 base gen cc,
      Nat.pow_add]
  ring
