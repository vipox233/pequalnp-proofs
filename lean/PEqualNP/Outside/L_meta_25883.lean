import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25883_aux

def rot (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k-s%k))) % 2^k

lemma rotBit {k j s w : Nat} (h : j<k) (hs : s<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit (if j<s then k-s+j else j-s) := by
  simp only [rot,Nat.mod_eq_of_lt hs,Nat.testBit_mod_two_pow,h,decide_true,Bool.true_and,
    Nat.testBit_or,Nat.testBit_shiftLeft,Nat.testBit_shiftRight]
  by_cases hj : j<s
  · simp [hj,Nat.not_le.mpr hj]
  · have big : w.testBit (k-s+j) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hj,Nat.le_of_not_gt hj,big]

lemma modspec {x k : Nat} (h : x < 2*k) :
    (x % k = x ∧ x < k) ∨ (x % k + k = x ∧ k ≤ x) := by
  by_cases hx : x < k
  · left; exact ⟨Nat.mod_eq_of_lt hx, hx⟩
  · right; refine ⟨?_, by omega⟩
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

lemma rotBit' {k j w : Nat} (s : Nat) (h : j<k) (hw : w<2^k) :
    (rot k s w).testBit j = w.testBit ((j+k-s%k)%k) := by
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  have e : rot k s w = rot k (s%k) w := by simp [rot]
  rw [e, rotBit h hs hw]
  congr 1
  rcases modspec (x := j+k-s%k) (k:=k) (by omega) with h1 | h1 <;> split_ifs <;> omega

lemma rot_lt (k s w : Nat) : rot k s w < 2^k := Nat.mod_lt _ (by positivity)

def mix (k d z : Nat) := z ^^^ rot k d z ^^^ rot k (k-d) z

lemma mix_lt {k z : Nat} (d : Nat) (hz : z < 2^k) : mix k d z < 2^k :=
  Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hz (rot_lt _ _ _)) (rot_lt _ _ _)

lemma mixBit {k d j z : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hz : z<2^k) :
    (mix k d z).testBit j
      = xor (xor (z.testBit j) (z.testBit ((j+k-d)%k))) (z.testBit ((j+d)%k)) := by
  have e : j+k-(k-d) = j+d := by omega
  simp only [mix, Nat.testBit_xor]
  rw [rotBit' d h hz, rotBit' (k-d) h hz, Nat.mod_eq_of_lt hdk,
    Nat.mod_eq_of_lt (show k-d<k by omega), e]

lemma flipBit (z q i : Nat) :
    (z ^^^ 2^q).testBit i = xor (z.testBit i) (decide (q = i)) := by
  simp [Nat.testBit_xor, Nat.testBit_two_pow]

lemma flip_lt {k z q : Nat} (hz : z < 2^k) (hq : q < k) : z ^^^ 2^q < 2^k :=
  Nat.xor_lt_two_pow hz (Nat.pow_lt_pow_right (by decide) hq)

lemma flip_flip (z q : Nat) : (z ^^^ 2^q) ^^^ 2^q = z := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

def ind (k d q j : Nat) : Bool :=
  xor (xor (decide (q = j)) (decide (q = (j+k-d)%k))) (decide (q = (j+d)%k))

lemma x6 : ∀ a b c d e f : Bool,
    xor (xor (xor a d) (xor b e)) (xor c f) = xor (xor (xor a b) c) (xor (xor d e) f) := by
  decide

lemma mixFlip {k d j z q : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hz : z<2^k) (hq : q<k) :
    (mix k d (z ^^^ 2^q)).testBit j = xor ((mix k d z).testBit j) (ind k d q j) := by
  rw [mixBit hd hdk h (flip_lt hz hq), mixBit hd hdk h hz]
  simp only [flipBit, ind]
  exact x6 _ _ _ _ _ _

lemma mixLin {k d j r u : Nat} (hd : 0<d) (hdk : d<k) (h : j<k) (hr : r<2^k) (hu : u<2^k) :
    (mix k d (r ^^^ u)).testBit j = xor ((mix k d r).testBit j) ((mix k d u).testBit j) := by
  rw [mixBit hd hdk h (Nat.xor_lt_two_pow hr hu), mixBit hd hdk h hr, mixBit hd hdk h hu]
  simp only [Nat.testBit_xor]
  exact x6 _ _ _ _ _ _

lemma rotFlip {k j q key : Nat} (i : Nat) (h : j<k) (hq : q<k) (hkey : key<2^k) :
    (rot k i (key ^^^ 2^((q+k-i%k)%k))).testBit j
      = xor ((rot k i key).testBit j) (decide (q = j)) := by
  have hi : i % k < k := Nat.mod_lt _ (by omega)
  have hq' : (q+k-i%k)%k < k := Nat.mod_lt _ (by omega)
  rw [rotBit' i h (flip_lt hkey hq'), rotBit' i h hkey, flipBit]
  congr 1
  have : ((q+k-i%k)%k = (j+k-i%k)%k) ↔ (q = j) := by
    rcases modspec (x := q+k-i%k) (k:=k) (by omega) with h1 | h1 <;>
    rcases modspec (x := j+k-i%k) (k:=k) (by omega) with h2 | h2 <;> omega
  simp [this]

lemma keyFlip {k d j q key u : Nat} (i : Nat) (hd : 0<d) (hdk : d<k) (h : j<k) (hq : q<k)
    (hkey : key<2^k) (hu : u<2^k) :
    (mix k d (rot k i (key ^^^ 2^((q+k-i%k)%k)) ^^^ u)).testBit j
      = xor ((mix k d (rot k i key ^^^ u)).testBit j) (ind k d q j) := by
  have h1 : (j+k-d)%k < k := Nat.mod_lt _ (by omega)
  have h2 : (j+d)%k < k := Nat.mod_lt _ (by omega)
  rw [mixLin hd hdk h (rot_lt _ _ _) hu, mixLin hd hdk h (rot_lt _ _ _) hu,
    mixBit hd hdk h (rot_lt _ _ _), mixBit hd hdk h (rot_lt _ _ _),
    rotFlip i h hq hkey, rotFlip i h1 hq hkey, rotFlip i h2 hq hkey]
  simp only [ind]
  generalize (rot k i key).testBit j = A
  generalize (rot k i key).testBit ((j+k-d)%k) = B
  generalize (rot k i key).testBit ((j+d)%k) = C
  generalize (mix k d u).testBit j = U
  generalize decide (q = j) = D
  generalize decide (q = (j+k-d)%k) = E
  generalize decide (q = (j+d)%k) = F
  revert A B C U D E F; decide

lemma ind_iff {k d q j : Nat} (hd : 0<d) (hdk : 2*d<k) (hq : q<k) (hj : j<k) :
    ind k d q j = true ↔ (q = j ∨ q + d = j ∨ q + d = j + k ∨ q = j + d ∨ q + k = j + d) := by
  rcases modspec (x := j+k-d) (k:=k) (by omega) with h1 | h1 <;>
  rcases modspec (x := j+d) (k:=k) (by omega) with h2 | h2 <;>
  by_cases e1 : q = j <;> by_cases e2 : q = (j+k-d)%k <;> by_cases e3 : q = (j+d)%k <;>
  simp only [ind, e1, e2, e3, decide_true, decide_false] <;> simp <;> omega

lemma siteSpec {k t : Nat} (start : Nat) (ht : t < k) :
    start % k < k ∧ (((start+t)%k = start % k+t ∧ start % k+t < k) ∨
      ((start+t)%k + k = start % k+t ∧ k ≤ start % k+t)) := by
  have hs : start % k < k := Nat.mod_lt _ (by omega)
  refine ⟨hs, ?_⟩
  rw [← Nat.mod_add_mod]
  exact modspec (by omega)

lemma halving (S : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ S, f x ∈ S) (inv : ∀ x ∈ S, f (f x) = x)
    (p : ℕ → Bool) (hp : ∀ x ∈ S, p (f x) = !p x) (b : Bool) :
    2 * (S.filter (fun x => p x = b)).card = S.card := by
  have e : (S.filter (fun x => p x = b)).card = (S.filter (fun x => ¬ p x = b)).card := by
    apply Finset.card_nbij' f f
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hf x hx.1, ?_⟩
      rw [hp x hx.1, hx.2]; cases b <;> simp
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
      refine ⟨hf x hx.1, ?_⟩
      have := hx.2
      rw [hp x hx.1]; revert this; cases b <;> cases p x <;> simp
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      exact inv x hx.1
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx
      exact inv x hx.1
  have := Finset.card_filter_add_card_filter_not (s := S) (fun x => p x = b)
  omega

lemma count (k : ℕ) (g : ℕ → ℕ → Bool) (q : ℕ → ℕ) (τ : ℕ → Bool) :
    ∀ n, n ≤ k → (∀ t < n, q t < k) →
    (∀ t < n, ∀ u < 2^k, g (u ^^^ 2^(q t)) t = !g u t) →
    (∀ t < n, ∀ t' < t, ∀ u < 2^k, g (u ^^^ 2^(q t)) t' = g u t') →
    ((Finset.range (2^k)).filter (fun u => ∀ t < n, g u t = τ t)).card = 2^(k-n) := by
  intro n
  induction n with
  | zero => intro _ _ _ _; simp
  | succ n ih =>
    intro hn hq ht hk'
    have ih' := ih (by omega) (fun t h => hq t (by omega)) (fun t h => ht t (by omega))
      (fun t h => hk' t (by omega))
    have e : (Finset.range (2^k)).filter (fun u => ∀ t < n+1, g u t = τ t)
        = ((Finset.range (2^k)).filter (fun u => ∀ t < n, g u t = τ t)).filter
            (fun u => g u n = τ n) := by
      ext u
      simp only [Finset.mem_filter, Nat.forall_lt_succ_right, and_assoc]
    rw [e]
    have h2 := halving ((Finset.range (2^k)).filter (fun u => ∀ t < n, g u t = τ t))
      (fun u => u ^^^ 2^(q n))
      (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
        refine ⟨flip_lt hx.1 (hq n (by omega)), ?_⟩
        intro t htn
        rw [hk' n (by omega) t htn x hx.1]; exact hx.2 t htn)
      (fun x _ => flip_flip x _) (fun u => g u n)
      (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        exact ht n (by omega) x hx.1) (τ n)
    rw [ih'] at h2
    have : 2^(k-n) = 2 * 2^(k-(n+1)) := by
      rw [← pow_succ']; congr 1; omega
    omega

lemma changeAbs (k : ℕ) (hk : 0 < k) (p1 p2 : ℕ → Bool) (m0 m1 m2 : Bool) (f1 f2 : ℕ → ℕ)
    (h1 : ∀ x < 2^k, f1 x < 2^k ∧ f1 (f1 x) = x ∧ p1 (f1 x) = !p1 x ∧ p2 (f1 x) = p2 x)
    (h2 : ∀ x < 2^k, f2 x < 2^k ∧ f2 (f2 x) = x ∧ p1 (f2 x) = p1 x ∧ p2 (f2 x) = !p2 x) :
    ((Finset.range (2^k)).filter (fun x =>
        xor m0 (xor (!p1 x && p2 x) (!(xor (p1 x) m1) && xor (p2 x) m2)) = true)).card
      = if m1 || m2 then 2^(k-1) else if m0 then 2^k else 0 := by
  have pw : 2^k = 2 * 2^(k-1) := by
    rw [← pow_succ']; congr 1; omega
  have key : ∀ f : ℕ → ℕ, (∀ x < 2^k, f x < 2^k ∧ f (f x) = x ∧
      (xor m0 (xor (!p1 (f x) && p2 (f x)) (!(xor (p1 (f x)) m1) && xor (p2 (f x)) m2)))
        = !(xor m0 (xor (!p1 x && p2 x) (!(xor (p1 x) m1) && xor (p2 x) m2)))) →
      ((Finset.range (2^k)).filter (fun x =>
        xor m0 (xor (!p1 x && p2 x) (!(xor (p1 x) m1) && xor (p2 x) m2)) = true)).card
        = 2^(k-1) := by
    intro f hf
    have := halving (Finset.range (2^k)) f
      (fun x hx => Finset.mem_range.mpr (hf x (Finset.mem_range.mp hx)).1)
      (fun x hx => (hf x (Finset.mem_range.mp hx)).2.1)
      (fun x => xor m0 (xor (!p1 x && p2 x) (!(xor (p1 x) m1) && xor (p2 x) m2)))
      (fun x hx => (hf x (Finset.mem_range.mp hx)).2.2) true
    rw [Finset.card_range] at this
    omega
  cases m1 <;> cases m2
  · cases m0 <;> simp
  · rw [key f1]
    · simp
    · intro x hx
      obtain ⟨a, b, c, d⟩ := h1 x hx
      refine ⟨a, b, ?_⟩
      rw [c, d]; cases m0 <;> cases p1 x <;> cases p2 x <;> rfl
  · rw [key f2]
    · simp
    · intro x hx
      obtain ⟨a, b, c, d⟩ := h2 x hx
      refine ⟨a, b, ?_⟩
      rw [c, d]; cases m0 <;> cases p1 x <;> cases p2 x <;> rfl
  · rw [key f1]
    · simp
    · intro x hx
      obtain ⟨a, b, c, d⟩ := h1 x hx
      refine ⟨a, b, ?_⟩
      rw [c, d]; cases m0 <;> cases p1 x <;> cases p2 x <;> rfl

def site (k start t : Nat) := (start+t)%k

lemma site_lt {k : Nat} (hk : 0<k) (start t : Nat) : site k start t < k := Nat.mod_lt _ hk

lemma indName {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t < a+2) :
    ind k d ((site k start t + d)%k) (site k start t) = true := by
  have hs := site_lt (k:=k) (by omega) start t
  rw [ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs]
  rcases modspec (x := site k start t + d) (k:=k) (by omega) with h|h <;> omega

lemma indName' {k d a t t' : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t < a+2)
    (ht' : t' < t) :
    ind k d ((site k start t + d)%k) (site k start t') = false := by
  have hs := site_lt (k:=k) (by omega) start t
  have hs' := site_lt (k:=k) (by omega) start t'
  rw [Bool.eq_false_iff, Ne, ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs']
  obtain ⟨h0, h1⟩ := siteSpec (k:=k) (t:=t) start (by omega)
  obtain ⟨_, h2⟩ := siteSpec (k:=k) (t:=t') start (by omega)
  unfold site at *
  rcases modspec (x := (start+t)%k + d) (k:=k) (by omega) with h|h <;>
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> omega

lemma indKey {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t+1 < a+2) :
    ind k d ((site k start t + k - d)%k) (site k start t) = true := by
  have hs := site_lt (k:=k) (by omega) start t
  rw [ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs]
  rcases modspec (x := site k start t + k - d) (k:=k) (by omega) with h|h <;> omega

lemma indKey' {k d a t : Nat} (start : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k) (ht : t+1 < a+2) :
    ind k d ((site k start t + k - d)%k) (site k start (t+1)) = false := by
  have hs := site_lt (k:=k) (by omega) start t
  have hs' := site_lt (k:=k) (by omega) start (t+1)
  rw [Bool.eq_false_iff, Ne, ind_iff hd (by omega) (Nat.mod_lt _ (by omega)) hs']
  obtain ⟨h0, h1⟩ := siteSpec (k:=k) (t:=t) start (by omega)
  obtain ⟨_, h2⟩ := siteSpec (k:=k) (t:=t+1) start (by omega)
  unfold site at *
  rcases modspec (x := (start+t)%k + k - d) (k:=k) (by omega) with h|h <;>
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> omega

def label (k d start init last c u x j : Nat) : Bool :=
  xor (xor ((mix k d (rot k init x ^^^ u)).testBit (site k start j))
      (!((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1))) &&
        (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2))))
    (xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j)))

def mixed (k d start u v j : Nat) : Bool :=
  ((mix k d u).testBit (site k start j) != (mix k d v).testBit (site k start j))

lemma yv {k d u v : Nat} (start init x j : Nat) (hd : 0<d) (hdk : d<k) (hu : u<2^k)
    (hv : v<2^k) :
    (mix k d (rot k init x ^^^ v)).testBit (site k start j)
      = xor ((mix k d (rot k init x ^^^ u)).testBit (site k start j)) (mixed k d start u v j) := by
  have hs := site_lt (k:=k) (by omega) start j
  rw [mixLin hd hdk hs (rot_lt _ _ _) hv, mixLin hd hdk hs (rot_lt _ _ _) hu]
  unfold mixed
  generalize (mix k d (rot k init x)).testBit (site k start j) = A
  generalize (mix k d u).testBit (site k start j) = B
  generalize (mix k d v).testBit (site k start j) = C
  revert A B C; decide

lemma labelDiff {k d u v : Nat} (start init last c x j : Nat) (hd : 0<d) (hdk : d<k)
    (hu : u<2^k) (hv : v<2^k) :
    (label k d start init last c u x j ≠ label k d start init last c v x j) ↔
      xor (mixed k d start u v j)
        (xor (!((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1))) &&
            (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)))
          (!(xor ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)))
              (mixed k d start u v (j+1))) &&
            xor ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)))
              (mixed k d start u v (j+2)))) = true := by
  unfold label
  rw [yv start init x j hd hdk hu hv, yv start init x (j+1) hd hdk hu hv,
    yv start init x (j+2) hd hdk hu hv]
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start j) = P0
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)) = P1
  generalize (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2)) = P2
  generalize mixed k d start u v j = M0
  generalize mixed k d start u v (j+1) = M1
  generalize mixed k d start u v (j+2) = M2
  generalize xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j)) = L
  revert P0 P1 P2 M0 M1 M2 L; decide

lemma change {k d a u v j : Nat} (start init last c : Nat) (hd : 0<d) (hk : a+2+2*d ≤ k)
    (hu : u<2^k) (hv : v<2^k) (hj : j < a) :
    ((Finset.range (2^k)).filter (fun key =>
        label k d start init last c u key j ≠ label k d start init last c v key j)).card =
      if mixed k d start u v (j+1) || mixed k d start u v (j+2) then 2^(k-1)
      else if mixed k d start u v j then 2^k else 0 := by
  have hk0 : 0 < k := by omega
  have hdk : d < k := by omega
  rw [Finset.filter_congr (fun key _ => labelDiff start init last c key j hd hdk hu hv)]
  refine changeAbs k hk0
    (fun x => (mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)))
    (fun x => (mix k d (rot k init x ^^^ u)).testBit (site k start (j+2))) _ _ _
    (fun x => x ^^^ 2^(((site k start (j+1) + k - d)%k + k - init % k)%k))
    (fun x => x ^^^ 2^(((site k start (j+2) + d)%k + k - init % k)%k)) ?_ ?_
  · intro x hx
    refine ⟨flip_lt hx (Nat.mod_lt _ hk0), flip_flip _ _, ?_, ?_⟩
    · show (mix k d (rot k init (x ^^^ 2^(((site k start (j+1) + k - d)%k + k - init % k)%k))
          ^^^ u)).testBit (site k start (j+1)) = _
      rw [keyFlip init hd hdk (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hx hu,
        indKey start hd hk (by omega)]
      simp
    · show (mix k d (rot k init (x ^^^ 2^(((site k start (j+1) + k - d)%k + k - init % k)%k))
          ^^^ u)).testBit (site k start (j+1+1)) = _
      rw [keyFlip init hd hdk (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hx hu,
        indKey' start hd hk (by omega)]
      simp
  · intro x hx
    refine ⟨flip_lt hx (Nat.mod_lt _ hk0), flip_flip _ _, ?_, ?_⟩
    · show (mix k d (rot k init (x ^^^ 2^(((site k start (j+2) + d)%k + k - init % k)%k))
          ^^^ u)).testBit (site k start (j+1)) = _
      rw [keyFlip init hd hdk (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hx hu,
        indName' start hd hk (show j+2 < a+2 by omega) (by omega)]
      simp
    · show (mix k d (rot k init (x ^^^ 2^(((site k start (j+2) + d)%k + k - init % k)%k))
          ^^^ u)).testBit (site k start (j+2)) = _
      rw [keyFlip init hd hdk (site_lt hk0 _ _) (Nat.mod_lt _ hk0) hx hu,
        indName start hd hk (show j+2 < a+2 by omega)]
      simp

end PEqualNP.Outside.L_meta_25883_aux

open PEqualNP.Outside.L_meta_25883_aux in
theorem PEqualNP.Outside.L_meta_25883 :
    ∀ (k d a start init last c : Nat), 0 < d → 0 < a → a+2+2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k-s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun t : Nat => (start+t) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  let table := fun name : Nat =>
    ((Finset.range a).product words).filter (fun entry => label name entry.2 entry.1)
  let mixed := fun (u v j : Nat) => ((mix u).testBit (site j) != (mix v).testBit (site j))
  (words.image table).card = 2^(a+2) ∧
  (∀ u ∈ words, (words.filter (fun v => table v = table u)).card = 2^(k-(a+2))) ∧
  ∀ u ∈ words, ∀ v ∈ words,
    (table u = table v ↔ ∀ t < a+2, mixed u v t = false) ∧
    ∀ j < a, (words.filter (fun key => label u key j ≠ label v key j)).card =
      if mixed u v (j+1) || mixed u v (j+2) then 2^(k-1)
      else if mixed u v j then 2^k else 0 := by
  intro k d a start init last c hd ha hk
  have hk0 : 0 < k := by omega
  have hdk : d < k := by omega
  intro words rot' mix' site' label' table mixed'
  have hl : ∀ u x j, label' u x j = label k d start init last c u x j := fun _ _ _ => rfl
  have hm : ∀ u v j, mixed' u v j = mixed k d start u v j := fun _ _ _ => rfl
  have C4 : ∀ u ∈ words, ∀ v ∈ words, ∀ j < a,
      (words.filter (fun key => label' u key j ≠ label' v key j)).card =
        if mixed' u v (j+1) || mixed' u v (j+2) then 2^(k-1)
        else if mixed' u v j then 2^k else 0 := by
    intro u hu v hv j hj
    simp only [hl, hm]
    exact change start init last c hd hk (Finset.mem_range.mp hu) (Finset.mem_range.mp hv) hj
  have C3 : ∀ u ∈ words, ∀ v ∈ words,
      (table u = table v ↔ ∀ t < a+2, mixed' u v t = false) := by
    intro u hu v hv
    constructor
    · intro h
      have eq : ∀ j < a, ∀ key ∈ words, label' u key j = label' v key j := by
        intro j hj key hkey
        have m : (j, key) ∈ table u ↔ (j, key) ∈ table v := by rw [h]
        simp only [table, Finset.mem_filter] at m
        have hmem : (j, key) ∈ (Finset.range a).product words :=
          Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, hkey⟩
        rw [Bool.eq_iff_iff]
        exact ⟨fun h1 => (m.mp ⟨hmem, h1⟩).2, fun h1 => (m.mpr ⟨hmem, h1⟩).2⟩
      have zz : ∀ j < a, mixed' u v j = false ∧ mixed' u v (j+1) = false ∧
          mixed' u v (j+2) = false := by
        intro j hj
        have z := C4 u hu v hv j hj
        have z0 : (words.filter (fun key => label' u key j ≠ label' v key j)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro key hkey
          simp [eq j hj key hkey]
        rw [z0] at z
        have p1 : 2^(k-1) ≠ 0 := by positivity
        have p2 : 2^k ≠ 0 := by positivity
        cases h0 : mixed' u v j <;> cases h1 : mixed' u v (j+1) <;>
          cases h2 : mixed' u v (j+2) <;> simp [h0, h1, h2] at z ⊢ <;> omega
      obtain ⟨j, rfl⟩ : ∃ j, a = j+1 := ⟨a-1, by omega⟩
      intro t ht
      have ht' : t < j+1 ∨ t = j+1 ∨ t = j+2 := by omega
      rcases ht' with h1 | rfl | rfl
      · exact (zz t h1).1
      · exact (zz j (by omega)).2.1
      · exact (zz j (by omega)).2.2
    · intro h
      apply Finset.filter_congr
      intro e he
      have he' := Finset.mem_product.mp he
      have hj := Finset.mem_range.mp he'.1
      have : label' u e.2 e.1 = label' v e.2 e.1 := by
        by_contra hne
        rw [hl, hl] at hne
        have := (labelDiff start init last c e.2 e.1 hd hdk (Finset.mem_range.mp hu)
          (Finset.mem_range.mp hv)).mp hne
        rw [← hm, ← hm, ← hm, h _ (by omega), h _ (by omega), h _ (by omega)] at this
        simp at this
      rw [this]
  have C2 : ∀ u ∈ words, (words.filter (fun v => table v = table u)).card = 2^(k-(a+2)) := by
    intro u hu
    have e : words.filter (fun v => table v = table u)
        = words.filter (fun v => ∀ t < a+2,
            (mix k d v).testBit (site k start t) = (mix k d u).testBit (site k start t)) := by
      apply Finset.filter_congr
      intro v hv
      rw [C3 v hv u hu]
      simp [hm, mixed]
    rw [e]
    refine count k (fun v t => (mix k d v).testBit (site k start t))
      (fun t => (site k start t + d)%k) (fun t => (mix k d u).testBit (site k start t))
      (a+2) (by omega) (fun t _ => Nat.mod_lt _ hk0) ?_ ?_
    · intro t ht w hw
      show (mix k d (w ^^^ 2^((site k start t + d)%k))).testBit (site k start t) = _
      rw [mixFlip hd hdk (site_lt hk0 _ _) hw (Nat.mod_lt _ hk0), indName start hd hk ht]
      simp
    · intro t ht t' ht' w hw
      show (mix k d (w ^^^ 2^((site k start t + d)%k))).testBit (site k start t') = _
      rw [mixFlip hd hdk (site_lt hk0 _ _) hw (Nat.mod_lt _ hk0), indName' start hd hk ht ht']
      simp
  have C1 : (words.image table).card = 2^(a+2) := by
    have maps : (words : Set ℕ).MapsTo table (words.image table) :=
      fun x hx => Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hx))
    have s := Finset.card_eq_sum_card_fiberwise maps
    rw [Finset.sum_congr rfl (g := fun _ => 2^(k-(a+2))) (by
        intro b hb
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
        exact C2 u hu), Finset.sum_const, smul_eq_mul, Finset.card_range] at s
    have e : 2^k = 2^(a+2) * 2^(k-(a+2)) := by
      rw [← pow_add]; congr 1; omega
    rw [e] at s
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) s).symm
  exact ⟨C1, C2, fun u hu v hv => ⟨C3 u hu v hv, C4 u hu v hv⟩⟩
