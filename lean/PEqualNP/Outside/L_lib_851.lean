import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_851

namespace Layers851

variable {q : ℕ}

def fl (D : ℕ) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) := 2^b * A j / D

def tot (D : ℕ) (A : Fin q → ℕ) (b : ℕ) := ∑ j, fl D A b j

def width (E D : ℕ) (A : Fin q → ℕ) (b : ℕ) := 2^b - tot D A b / E

def carry (D : ℕ) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) :=
  fl D A (b+1) j - 2*fl D A b j

theorem scaled (D E : ℕ) (A : Fin q → ℕ) (hs : ∑ j, A j = D*E) (b : ℕ) :
    tot D A b * D ≤ (2^b*E)*D := by
  calc
    _ = ∑ j, fl D A b j * D := Finset.sum_mul ..
    _ ≤ ∑ j, 2^b * A j := Finset.sum_le_sum fun j _ => Nat.div_mul_le_self _ _
    _ = _ := by rw [← Finset.mul_sum, hs]; ring

theorem scaled' {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (b : ℕ) : tot D A b / E ≤ 2^b := by
  have t := scaled D E A hs b
  have hh := Nat.div_mul_le_self (tot D A b) E
  have h : tot D A b ≤ 2^b*E := Nat.le_of_mul_le_mul_right t hd
  exact Nat.le_of_mul_le_mul_right (hh.trans h) he

theorem zero_width {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (hn : ∃ j, A j % D ≠ 0) : width E D A 0 = 1 := by
  obtain ⟨j0,hj⟩ := hn
  have hlt : tot D A 0 * D < ∑ j, A j := by
    rw [tot, Finset.sum_mul]
    apply Finset.sum_lt_sum
    · intro j _
      simpa [fl] using Nat.div_mul_le_self (A j) D
    · refine ⟨j0,Finset.mem_univ _, ?_⟩
      simp only [fl, pow_zero, one_mul]
      have h := Nat.mod_add_div (A j0) D
      rw [mul_comm D] at h
      omega
  rw [hs, mul_comm D E] at hlt
  have small : tot D A 0 < E := by
    by_contra! h
    exact (not_lt_of_ge (Nat.mul_le_mul_right D h)) hlt
  simp [width, Nat.div_eq_of_lt small]

theorem floor_step {D : ℕ} (hd : 0 < D) (A : Fin q → ℕ) (b : ℕ) (j : Fin q) :
    2*fl D A b j ≤ fl D A (b+1) j := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := Nat.div_mul_le_self (2^b*A j) D
  dsimp [fl]
  rw [pow_succ]
  nlinarith

theorem width_step {D E : ℕ} (hd : 0 < D) (he : 0 < E) (A : Fin q → ℕ)
    (hs : ∑ j, A j = D*E) (b : ℕ) : width E D A (b+1) ≤ 2*width E D A b := by
  have h : 2*tot D A b ≤ tot D A (b+1) := by
    unfold tot
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => floor_step hd A b j
  have hh : 2*(tot D A b/E) ≤ tot D A (b+1)/E := by
    apply (Nat.le_div_iff_mul_le he).mpr
    have h0 := Nat.div_mul_le_self (tot D A b) E
    nlinarith
  have hb := scaled' hd he A hs b
  have hb' := scaled' hd he A hs (b+1)
  unfold width
  rw [pow_succ] at *
  omega

theorem period_lift {D h p b : ℕ} (hdv : D ∣ 2^h*(2^p-1)) (hb : h ≤ b) :
    ∃ m, 2^(b+p) = 2^b + m*D := by
  obtain ⟨t,ht⟩ := hdv
  refine ⟨2^(b-h)*t, ?_⟩
  have hx : b-h+h=b := by omega
  have ha : 2^(b-h)*2^h = 2^b := by rw [←pow_add, hx]
  have hp0 : 0 < (2:ℕ)^p := by positivity
  have hp : 2^p-1+1=2^p := by omega
  rw [pow_add, ←ha, ←hp]
  nlinarith [congrArg (2^(b-h) * ·) ht]

theorem floor_shift {D : ℕ} (hd : 0<D) (A : Fin q → ℕ) (b p m : ℕ)
    (hp : 2^(b+p)=2^b+m*D) (j : Fin q) :
    fl D A (b+p) j = fl D A b j + m*A j := by
  unfold fl
  rw [hp, show (2^b + m*D)*A j = 2^b*A j+(m*A j)*D by ring,
    Nat.add_mul_div_right _ _ hd]

theorem periods {D E h p : ℕ} (hd : 0<D) (he : 0<E)
    (hdv : D ∣ 2^h*(2^p-1)) (A : Fin q → ℕ) (hs : ∑ j, A j = D*E)
    (b : ℕ) (hb : h ≤ b) :
    width E D A (b+p) = width E D A b ∧
    tot D A (b+p) % E = tot D A b % E ∧
    ∀ j, carry D A (b+p) j = carry D A b j := by
  obtain ⟨m,hm⟩ := period_lift hdv hb
  have ht : tot D A (b+p) = tot D A b + (m*D)*E := by
    simp only [tot, floor_shift hd A b p m hm, Finset.sum_add_distrib, ← Finset.mul_sum, hs]
    ring
  refine ⟨?_, ?_, ?_⟩
  · unfold width
    rw [hm, ht, Nat.add_mul_div_right _ _ he]
    omega
  · simp [ht]
  · intro j
    have h1 : 2^(b+1+p)=2^(b+1)+(2*m)*D := by
      rw [show b+1+p=b+p+1 by omega, pow_succ, hm, pow_succ]
      ring
    unfold carry
    rw [show b+p+1=b+1+p by omega, floor_shift hd A (b+1) p (2*m) h1,
      floor_shift hd A b p m hm]
    ring_nf
    omega

end Layers851

namespace Reserves851

variable {q : ℕ}

def extN (a : Fin q → ℕ) (i : ℕ) := if h : i < q then a ⟨i,h⟩ else 0

def pref (a : Fin q → ℕ) (k : ℕ) := ∑ i ∈ Finset.range k, extN a i

theorem pref_full (a : Fin q → ℕ) : pref a q = ∑ j, a j := by
  unfold pref
  rw [←Fin.sum_univ_eq_sum_range]
  simp [extN]

theorem pref_step (a : Fin q → ℕ) (i : Fin q) : pref a (i.val+1) = pref a i + a i := by
  simp [pref, Finset.sum_range_succ, extN, i.isLt]

def reserve (cap : ℕ → ℕ) (c : ℕ → Fin q → ℕ) (init : Fin q → ℕ) : ℕ → ℕ → ℕ
  | 0,k => pref init k
  | b+1,k => min (cap (b+1)) (2*reserve cap c init b k + pref (c b) k)

variable (cap : ℕ → ℕ) (c : ℕ → Fin q → ℕ) (init : Fin q → ℕ)

def row (b : ℕ) (j : Fin q) := reserve cap c init b (j.val+1) - reserve cap c init b j.val

theorem bottom (b : ℕ) : reserve cap c init b 0 = 0 := by
  induction b with
  | zero => simp [reserve,pref]
  | succ b ih => simp [reserve,pref,ih]

theorem full (hc0 : (∑ j, init j) = cap 0) (hc : ∀ b, cap (b+1) ≤ 2*cap b + ∑ j, c b j)
    (b : ℕ) : reserve cap c init b q = cap b := by
  induction b with
  | zero => simpa [reserve, pref_full] using hc0
  | succ b ih => simp [reserve, ih, pref_full, min_eq_left (hc b)]

theorem mono (b : ℕ) (j : Fin q) :
    reserve cap c init b j.val ≤ reserve cap c init b (j.val+1) := by
  induction b with
  | zero => simp [reserve, pref_step]
  | succ b ih =>
    simp only [reserve, pref_step]
    omega

theorem prefix_row (b k : ℕ) (hk : k ≤ q) : pref (row cap c init b) k = reserve cap c init b k := by
  induction k with
  | zero => simp [pref, bottom]
  | succ k ih =>
    let j : Fin q := ⟨k, by omega⟩
    change pref (row cap c init b) (j.val+1) = _
    rw [pref_step, show j.val=k by rfl, ih (by omega)]
    have h := mono cap c init b j
    unfold row
    change reserve cap c init b j.val + (reserve cap c init b (j.val+1) - reserve cap c init b j.val) =
      reserve cap c init b (j.val+1)
    omega

theorem row_zero (j : Fin q) : row cap c init 0 j = init j := by
  simp [row,reserve,pref_step]

theorem row_le (b : ℕ) (j : Fin q) : row cap c init (b+1) j ≤ 2*row cap c init b j + c b j := by
  have h := mono cap c init b j
  simp only [row, reserve, pref_step]
  omega

def pay (b : ℕ) (j : Fin q) := 2*row cap c init b j + c b j - row cap c init (b+1) j

theorem balance (b : ℕ) (j : Fin q) :
    pay cap c init b j + row cap c init (b+1) j = 2*row cap c init b j + c b j :=
  Nat.sub_add_cancel (row_le ..)

theorem pay_total (hc0 : (∑ j, init j) = cap 0) (hc : ∀ b, cap (b+1) ≤ 2*cap b + ∑ j, c b j)
    (b : ℕ) : (∑ j, pay cap c init b j) + cap (b+1) = 2*cap b + ∑ j, c b j := by
  have h (d : ℕ) : (∑ j, row cap c init d j) = cap d := by
    rw [←pref_full, prefix_row _ _ _ _ _ le_rfl, full _ _ _ hc0 hc]
  have t := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin q))) rfl
    (fun j _ => balance cap c init b j)
  simpa only [Finset.sum_add_distrib, ←Finset.mul_sum, h] using t

end Reserves851

namespace Clock851

def clock (B p b : ℕ) : ℕ := if b < B then b else B+(b-B)%p

theorem clock_lt (B b : ℕ) {p : ℕ} (hp : 0<p) : clock B p b < B+p := by
  unfold clock
  split_ifs <;> have h := Nat.mod_lt (b-B) hp <;> omega

theorem clock_early (B p b : ℕ) (h : b < B+p) : clock B p b = b := by
  unfold clock
  split_ifs with hb
  · rfl
  · rw [Nat.mod_eq_of_lt (by omega : b-B < p)]
    omega

theorem clock_period (B p b : ℕ) (hb : B ≤ b) : clock B p (b+p) = clock B p b := by
  simp only [clock, if_neg (by omega : ¬b+p<B), if_neg (by omega : ¬b<B)]
  rw [show b+p-B=b-B+p by omega, Nat.add_mod_right]

theorem clock_eq {α : Type} (f : ℕ → α) (B p : ℕ) (hp : 0<p)
    (hf : ∀ b ≥ B, f (b+p) = f b) (b : ℕ) : f (clock B p b) = f b := by
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    by_cases hb : b<B+p
    · rw [clock_early _ _ _ hb]
    · have he : b-p+p=b := by omega
      have hc := clock_period B p (b-p) (by omega)
      have hprev := ih (b-p) (by omega)
      have hnext := hf (b-p) (by omega)
      rw [he] at hc hnext
      rw [hc,hprev,hnext]

theorem clock_next (B p b : ℕ) (hp : 0<p) :
    clock B p ((clock B p b)+1) = clock B p (b+1) := by
  apply clock_eq (fun x => clock B p (x+1)) B p hp
  intro d hd
  rw [show d+p+1=d+1+p by omega, clock_period _ _ _ (by omega)]

theorem eventual {α : Type} (f : ℕ → α) (step : ℕ → α → α) (h p : ℕ)
    (hs : ∀ b, f (b+1)=step b (f b))
    (hp : ∀ b ≥ h, step (b+p) = step b) (B : ℕ) (hh : h ≤ B)
    (hB : f (B+p)=f B) : ∀ b ≥ B, f (b+p)=f b := by
  intro b hb
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hb
  clear hb
  induction k with
  | zero => simpa using hB
  | succ k ih =>
    rw [show B+(k+1)+p=B+k+p+1 by omega, show B+(k+1)=B+k+1 by omega,
      hs (B+k+p), hs (B+k), hp _ (by omega), ih]

theorem block (cap carry f : ℕ → ℕ) (h p : ℕ) (step : ∀ b, f (b+1)=min (cap b) (2*f b+carry b))
    (hc : ∀ b ≥ h, cap (b+p)=cap b) (hd : ∀ b ≥ h, carry (b+p)=carry b)
    (walk : ℕ → ℕ → ℕ) (w0 : ∀ x, walk 0 x=x)
    (ws : ∀ k x, walk (k+1) x=min (cap (h+k)) (2*walk k x+carry (h+k))) (t : ℕ) :
    f (h+p*t) = (walk p)^[t] (f h) := by
  have shift (g : ℕ → ℕ) (hg : ∀ b ≥ h, g (b+p)=g b) (k d : ℕ) : g (h+p*k+d)=g (h+d) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show h+p*(k+1)+d = (h+p*k+d)+p by ring, hg _ (by omega), ih]
  have chunk (k d : ℕ) : f (h+p*k+d) = walk d (f (h+p*k)) := by
    induction d with
    | zero => simp [w0]
    | succ d ih =>
      rw [show h+p*k+(d+1)=h+p*k+d+1 by omega, step, ih, ws, shift cap hc, shift carry hd]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show h+p*(t+1)=h+p*t+p by ring, chunk, ih, Function.iterate_succ_apply']

end Clock851

namespace ReserveCycle851

def walk (cap carry : ℕ → ℕ) (s : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | k+1, x => min (cap (s+k)) (2*walk cap carry s k x + carry (s+k))

theorem normal (cap carry : ℕ → ℕ) (s k : ℕ) :
    ∃ U C, ∀ x, walk cap carry s (k+1) x = min U (2^(k+1)*x+C) := by
  induction k with
  | zero =>
    exact ⟨cap s, carry s, fun x => by simp [walk]⟩
  | succ k ih =>
    obtain ⟨U,C,h⟩ := ih
    refine ⟨min (cap (s+(k+1))) (2*U+carry (s+(k+1))), 2*C+carry (s+(k+1)), ?_⟩
    intro x
    rw [walk, h, min_assoc]
    congr 1
    rw [pow_succ (2:ℕ) (k+1)]
    by_cases hv : U ≤ 2^(k+1)*x+C
    · rw [min_eq_left hv, min_eq_left]
      nlinarith
    · rw [min_eq_right (by omega : 2^(k+1)*x+C ≤ U), min_eq_right]
      · ring
      · nlinarith

theorem cap_normal (cap carry : ℕ → ℕ) (s k E : ℕ)
    (hc : ∀ b, cap b < E) :
    ∃ U C, U < E ∧ ∀ x, walk cap carry s (k+1) x = min U (2^(k+1)*x+C) := by
  obtain ⟨U,C,H⟩ := normal cap carry s k
  refine ⟨min (cap (s+k)) U, C, lt_of_le_of_lt (min_le_left _ _) (hc _), ?_⟩
  intro x
  rw [min_assoc, ← H, min_eq_right]
  exact min_le_left _ _

theorem stabilizes (M U C E u x : ℕ) (hM : 1 ≤ M) (hU : U < E) (hE : E ≤ M^u) :
    (fun y : ℕ => min U (M*y+C))^[u+2] x =
       (fun y : ℕ => min U (M*y+C))^[u+1] x := by
  let f := fun y : ℕ => min U (M*y+C)
  change f^[u+2] x = f^[u+1] x
  conv_lhs => rw [Function.iterate_succ_apply']
  by_cases hz : f x = 0
  · have h0 : f 0 = 0 := by
      dsimp [f] at *
      rcases le_total U (M*x+C) with h|h
      · rw [min_eq_left h] at hz
        simp [hz]
      · rw [min_eq_right h] at hz
        have : C = 0 := by omega
        simp [this]
    have hh : ∀ t, f^[t+1] x = 0 := by
      intro t
      induction t with
      | zero => simpa using hz
      | succ t ih => rw [Function.iterate_succ_apply', ih, h0]
    rw [hh, h0]
  · have hx : 1 ≤ f x := by omega
    have hh : f^[u+1] x = U := by
      have halt : f U = U := by
        dsimp [f]
        rw [min_eq_left]
        nlinarith [Nat.mul_le_mul_right U hM]
      have grow : ∀ t, f^[t+1] x = U ∨ M^t ≤ f^[t+1] x := by
        intro t
        induction t with
        | zero => right; simpa using hx
        | succ t ih =>
          rw [Function.iterate_succ_apply']
          rcases ih with hi|hi
          · exact Or.inl (by rw [hi, halt])
          · by_cases hc : U ≤ M*(f^[t+1] x)+C
            · exact Or.inl (min_eq_left hc)
            · right
              change M^(t+1) ≤ min U (M*(f^[t+1] x)+C)
              rw [min_eq_right (by omega : M*(f^[t+1] x)+C ≤ U), pow_succ]
              nlinarith [Nat.mul_le_mul_left M hi]
      rcases grow u with h|h
      · exact h
      · have hu : f^[u+1] x ≤ U := by
          rw [Function.iterate_succ_apply']
          exact min_le_left _ _
        omega
    rw [hh]
    dsimp [f]
    rw [min_eq_left]
    nlinarith [Nat.mul_le_mul_right U hM]

end ReserveCycle851

namespace Schedule851
open Layers851 Reserves851 ReserveCycle851 Clock851
variable {q E D h p u : ℕ} (A : Fin q → ℕ)

def cap (b : ℕ) := tot D A b % E
def r (b : ℕ) (j : Fin q) := row (cap (E:=E) (D:=D) A) (carry D A) (fl D A 0) b j
def emit (b : ℕ) (j : Fin q) := pay (cap (E:=E) (D:=D) A) (carry D A) (fl D A 0) b j

theorem layer_id (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (b : ℕ) :
    (2*width E D A b-width E D A (b+1))*E + cap (D:=D) (E:=E) A (b+1)
    = 2*cap (D:=D) (E:=E) A b + ∑ j, carry D A b j := by
  have hf (j) : carry D A b j+2*fl D A b j = fl D A (b+1) j :=
    Nat.sub_add_cancel (floor_step hd ..)
  have hh := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin q))) rfl (fun j _ => hf j)
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum] at hh
  change (∑ j, carry D A b j)+2*tot D A b = tot D A (b+1) at hh
  have hT (x) := Nat.mod_add_div (tot D A x) E
  have hu := scaled' hd he A hs b
  have hv := scaled' hd he A hs (b+1)
  have hw := width_step hd he A hs b
  have hw' := Nat.sub_add_cancel hw
  have hw0 := Nat.sub_add_cancel hu
  have hw1 := Nat.sub_add_cancel hv
  change width E D A b + _ = _ at hw0
  change width E D A (b+1) + _ = _ at hw1
  have H : (2*width E D A b-width E D A (b+1)) + 2*(tot D A b/E) = tot D A (b+1)/E := by
    rw [pow_succ] at hw1
    omega
  unfold cap
  nlinarith [hT b, hT (b+1), congrArg (· * E) H]

theorem cap_init (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (hn : ∃ j, A j%D≠0) :
    (∑ j,fl D A 0 j) = cap (D:=D) (E:=E) A 0 := by
  have h := zero_width hd he A hs hn
  have hu := scaled' hd he A hs 0
  simp only [width, pow_zero] at h hu
  have ht : tot D A 0/E=0 := by omega
  unfold cap
  change tot D A 0 = _
  have hh := Nat.mod_add_div (tot D A 0) E
  simpa [ht] using hh.symm

theorem pay_count (hd : 0<D) (he : 0<E) (hs : ∑ j, A j=D*E) (hn : ∃ j, A j%D≠0) (b : ℕ) :
    (∑ j,emit (D:=D) (E:=E) A b j) = (2*width E D A b-width E D A (b+1))*E := by
  have hi := cap_init A hd he hs hn
  have hc (d : ℕ) : cap (D:=D) (E:=E) A (d+1) ≤ 2*cap (D:=D) (E:=E) A d+∑ j, carry D A d j := by
    have t := layer_id A hd he hs d
    omega
  have h1 := pay_total _ _ _ hi hc b
  have h2 := layer_id A hd he hs b
  change (∑ j, pay _ _ _ _ j) = _
  omega

theorem eventual_row (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) :
    ∀ b ≥ h+p*(u+1), ∀ j, r (D:=D) (E:=E) A (b+p) j = r (D:=D) (E:=E) A b j := by
  let R := reserve (cap (D:=D) (E:=E) A) (carry D A) (fl D A 0)
  have per (k : ℕ) : ∀ b ≥ h+p*(u+1), R (b+p) k=R b k := by
    let a := fun b => cap (D:=D) (E:=E) A (b+1)
    let c := fun b => pref (carry D A b) k
    have ha (b) (hb : h≤b) : a (b+p)=a b := by
      change tot D A (b+p+1)%E = _
      rw [show b+p+1=b+1+p by omega]
      exact (periods hd he hv A hs (b+1) (by omega)).2.1
    have hc (b) (hb : h≤b) : c (b+p)=c b := by
      have e : carry D A (b+p)=carry D A b := funext (periods hd he hv A hs b hb).2.2
      simp [c,e]
    have eq (b) : R (b+1) k = min (a b) (2*R b k+c b) := rfl
    let W := walk a c h
    obtain ⟨U,C,hU,hW⟩ : ∃ U C, U<E ∧ ∀ x, W p x=min U (2^p*x+C) := by
      obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p≠0)
      rw [hl]
      exact cap_normal a c h l E (fun _ => Nat.mod_lt _ he)
    have hblk (t) := block a c (fun b => R b k) h p eq ha hc W (fun _ => rfl) (fun _ _ => rfl) t
    have heq : W p = fun x => min U (2^p*x+C) := funext hW
    have hstab := stabilizes (2^p) U C E u (R h k) (Nat.succ_le_of_lt (by positivity)) hU (by simpa [←pow_mul] using hu)
    apply eventual (fun b => R b k) (fun b x => min (a b) (2*x+c b)) h p eq
    · intro b hb; simp [ha b hb, hc b hb]
    · omega
    · rw [show h+p*(u+1)+p=h+p*(u+2) by ring, hblk, hblk, heq]
      exact hstab
  intro b hb j
  change R (b+p) (j.val+1) - R (b+p) j.val = _
  rw [per _ b hb, per _ b hb]
  rfl

theorem periodic_emit (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) (b) (hb : h+p*(u+1)≤b) (j) :
    emit (D:=D) (E:=E) A (b+p) j = emit (D:=D) (E:=E) A b j := by
  have hper := eventual_row A hd he hp hv hu hs
  change 2*r A (b+p) j + carry D A (b+p) j - r A (b+p+1) j = _
  rw [show b+p+1=b+1+p by omega, hper _ hb, hper _ (by omega : h+p*(u+1)≤b+1),
      (periods hd he hv A hs b (by omega)).2.2]
  rfl

end Schedule851

namespace Schedule851
open Layers851 Reserves851
variable {q E D h p u : ℕ} (A : Fin q → ℕ)

noncomputable def debt (b : ℕ) (j : Fin q) : ℝ :=
  ((2^b*A j : ℕ) : ℝ)/D - (fl D A b j:ℝ) + (r (E:=E) (D:=D) A b j:ℝ)

theorem debt_initial (j) : debt (D:=D) (E:=E) A 0 j=(A j:ℝ)/D := by
  simp [debt, r, row_zero]

theorem debt_period (hd : 0<D) (he : 0<E) (hp : 0<p) (hv : D ∣ 2^h*(2^p-1))
    (hu : E ≤ 2^(p*u)) (hs : ∑ j, A j=D*E) (b) (hb : h+p*(u+1) ≤ b) (j) :
    debt (D:=D) (E:=E) A (b+p) j=debt (D:=D) (E:=E) A b j := by
  obtain ⟨m,hm⟩ := period_lift hv (by omega : h≤b)
  unfold debt
  rw [eventual_row A hd he hp hv hu hs b hb j, floor_shift hd A b p m hm j, hm]
  push_cast
  field_simp
  <;> ring

theorem debt_step (hd : 0<D) (b) (j) : 2*debt (D:=D) (E:=E) A b j =
    debt (D:=D) (E:=E) A (b+1) j + (emit (D:=D) (E:=E) A b j : ℝ) := by
  have H := balance (cap (D:=D) (E:=E) A) (carry D A) (fl D A 0) b j
  change emit A b j + r A (b+1) j = 2*r A b j + carry D A b j at H
  have H' : (emit (E:=E) (D:=D) A b j : ℝ) + r (E:=E) (D:=D) A (b+1) j =
      2*(r (E:=E) (D:=D) A b j:ℝ) + carry D A b j := by exact_mod_cast H
  have hg : (carry D A b j : ℝ)+2*(fl D A b j:ℝ)=fl D A (b+1) j := by
    exact_mod_cast Nat.sub_add_cancel (floor_step hd A b j)
  unfold debt
  push_cast
  rw [pow_succ]
  linarith only [H', hg, show (2:ℝ)^b*2*A j/D=2*(2^b*A j/D) by ring]

theorem same_initial (V W pay : ℕ → ℝ) (B p : ℕ) (hp : 0<p)
    (hs : ∀ b, 2*V b=V (b+1)+pay b) (ht : ∀ b, 2*W b=W (b+1)+pay b)
    (hv : V (B+p)=V B) (hw : W (B+p)=W B) : V 0 = W 0 := by
  have step (b) : V b-W b=2^b*(V 0-W 0) := by
    induction b with
    | zero => simp
    | succ b ih =>
      rw [pow_succ]
      linarith [hs b, ht b, show (2:ℝ)^b*2*(V 0-W 0)=2*(2^b*(V 0-W 0)) by ring]
  have hh := step (B+p)
  rw [hv,hw,step B,pow_add] at hh
  have hn : (2:ℝ)^p>1 := one_lt_pow₀ (by norm_num) (by omega)
  have hB : 0<(2:ℝ)^B := by positivity
  have hzero : (2:ℝ)^B*((2:ℝ)^p-1)*(V 0-W 0)=0 := by nlinarith only [hh]
  rcases mul_eq_zero.mp hzero with h|h
  · have hnz : 0<(2:ℝ)^B*((2:ℝ)^p-1) := mul_pos hB (by linarith)
    linarith
  · linarith

end Schedule851

namespace Address851

def size (K : ℕ → ℕ) (L : ℕ) : ℕ := ∑ i ∈ Finset.range L, K i

abbrev Cell (K : ℕ → ℕ) (L : ℕ) := (d : Fin L) × Fin (K d)

noncomputable def code (K : ℕ → ℕ) (L : ℕ) : Cell K L ≃ Fin (size K L) :=
  Fintype.equivFinOfCardEq (by simp [Cell, Fintype.card_sigma, size, Fin.sum_univ_eq_sum_range])

variable (K : ℕ → ℕ) {L : ℕ}

noncomputable def level (i : Fin (size K L)) : Fin L := ((code K L).symm i).1

noncomputable def idx (i : Fin (size K L)) : ℕ := ((code K L).symm i).2.val

noncomputable def place (b : Fin L) (k : ℕ) : Option (Fin (size K L)) :=
  if h : k < K b then some (code K L ⟨b,⟨k,h⟩⟩) else none

theorem level_code (a : Cell K L) : level K (code K L a) = a.1 :=
  congrArg (fun x : Cell K L => x.1) ((code K L).symm_apply_apply a)

theorem idx_code (a : Cell K L) : idx K (code K L a) = a.2.val :=
  congrArg (fun x : Cell K L => x.2.val) ((code K L).symm_apply_apply a)

theorem code_same (l d : Fin L) (x : Fin (K l)) (y : Fin (K d))
    (hl : l=d) (hx : x.val=y.val) : code K L ⟨l,x⟩=code K L ⟨d,y⟩ := by
  subst d
  exact congrArg (fun z : Fin (K l) => code K L ⟨l,z⟩) (Fin.ext hx)

theorem place_some (b : Fin L) (k : ℕ) (i : Fin (size K L)) :
    place K b k = some i ↔ level K i = b ∧ idx K i = k := by
  obtain ⟨⟨d,t⟩,rfl⟩ := (code K L).surjective i
  rw [level_code, idx_code]
  by_cases h : k < K b
  · simp only [place, dif_pos h, Option.some.injEq, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro he
      exact ⟨(congrArg (fun x : Cell K L => x.1) he).symm,
             (congrArg (fun x : Cell K L => x.2.val) he).symm⟩
    · rintro ⟨rfl,hk⟩
      subst k
      rfl
  · simp only [place, dif_neg h, reduceCtorEq, false_iff]
    rintro ⟨rfl,hk⟩
    exact h (hk ▸ t.isLt)

theorem place_self (i : Fin (size K L)) : place K (level K i) (idx K i) = some i :=
  (place_some ..).mpr ⟨rfl,rfl⟩

theorem rank_lt (i : Fin (size K L)) : idx K i < K (level K i) :=
  ((code K L).symm i).2.isLt

theorem width_le_size (l : Fin L) : K l ≤ size K L :=
  Finset.single_le_sum (fun i _ => Nat.zero_le (K i)) (Finset.mem_range.mpr l.isLt)

private theorem ite_decidable_irrel {R : Type} (p : Prop) (a b : R) (d d' : Decidable p) :
    @ite R p d a b = @ite R p d' a b :=
  congrArg (fun t => @ite R p t a b) (Subsingleton.elim d d')

theorem sum_level {R : Type} [AddCommMonoid R] (l : Fin L)
    (v : Fin (size K L) → R) :
    (∑ i, if level K i=l then v i else 0) =
        ∑ k : Fin (K l), v (code K L ⟨l,k⟩) := by
  classical
  calc
    _ = ∑ a : Cell K L, if a.1=l then v (code K L a) else 0 := by
      refine Fintype.sum_equiv (code K L).symm _ _ ?_
      intro i
      simp only [level, Equiv.apply_symm_apply]
      exact ite_decidable_irrel _ _ _ _ _
    _ = ∑ d : Fin L, ∑ k : Fin (K d), if d=l then v (code K L ⟨d,k⟩) else 0 := by
      rw [← Fintype.sum_sigma']
    _ = _ := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro d _ hd; simp [hd]
      · simp

theorem rank_escape {n : Fin (size K L) → Bool → Option (Fin (size K L))}
    (hinc : ∀ i j, n i true = some j → idx K i < idx K j) (i : Fin (size K L)) :
    (fun x : Option (Fin (size K L)) => x.bind (fun s => n s true))^[size K L] (some i) = none := by
  let step := fun x : Option (Fin (size K L)) => x.bind (fun s => n s true)
  have h : ∀ t j, step^[t] (some i) = some j → t+idx K i ≤ idx K j := by
    intro t
    induction t with
    | zero =>
      intro j hj
      simp at hj
      simp [hj]
    | succ t ih =>
      intro j hj
      rw [Function.iterate_succ_apply'] at hj
      cases he : step^[t] (some i) with
      | none =>
        rw [he] at hj
        cases hj
      | some v =>
        rw [he] at hj
        have h1 := hinc v j hj
        have h2 := ih v he
        omega
  change step^[size K L] (some i) = none
  cases he : step^[size K L] (some i) with
  | none => rfl
  | some v =>
    have h1 := h _ _ he
    have h2 := rank_lt K v
    have h3 := width_le_size K (level K v)
    omega

end Address851

namespace BinaryWords851

def digit : Bool → ℕ
  | false => 0
  | true => 1

def rank : (b : ℕ) → (Fin b → Bool) → ℕ
  | 0, _ => 0
  | b+1, w => 2*rank b (fun j => w j.castSucc) + digit (w (Fin.last b))

theorem rank_lt (b : ℕ) (w : Fin b → Bool) : rank b w < 2^b := by
  induction b with
  | zero => decide +revert
  | succ b ih =>
    have h := ih (fun j => w j.castSucc)
    rw [rank, pow_succ]
    cases w (Fin.last b) <;> simp [digit] <;> omega

theorem rank_inj (b : ℕ) : Function.Injective (rank b) := by
  induction b with
  | zero => intro u w _; exact Subsingleton.elim _ _
  | succ b ih =>
    intro u w huv
    have eqp : rank b (fun j => u j.castSucc) = rank b (fun j => w j.castSucc) ∧
        u (Fin.last b) = w (Fin.last b) := by
      simp only [rank] at huv
      cases ha : u (Fin.last b) <;> cases hb : w (Fin.last b) <;>
        simp [ha, hb, digit] at * <;> omega
    have he := ih eqp.1
    funext i
    exact Fin.lastCases eqp.2 (fun j => congrFun he j) i

theorem rank_onto (b k : ℕ) (hk : k < 2^b) : ∃ w : Fin b → Bool, rank b w = k := by
  induction b generalizing k with
  | zero =>
    have : k = 0 := by simpa using hk
    exact ⟨fun i => i.elim0, by simp [rank, this]⟩
  | succ b ih =>
    rw [pow_succ] at hk
    obtain ⟨v,hv⟩ := ih (k/2) (by omega)
    let bit := decide (k%2=1)
    refine ⟨Fin.lastCases bit v, ?_⟩
    simp [rank, Fin.lastCases_castSucc, Fin.lastCases_last, hv]
    by_cases hb : k%2=1 <;> simp [bit, hb, digit] <;> omega

theorem fold (α : Type) (update : α → Bool → α) (z : α) (state : ℕ → ℕ → α)
    (init : state 0 0 = z)
    (next : ∀ b k bit, k < 2^b → update (state b k) bit = state (b+1) (2*k+digit bit))
    (b : ℕ) (w : Fin b → Bool) :
    (List.ofFn w).foldl update z = state b (rank b w) := by
  induction b with
  | zero => simpa [rank] using init.symm
  | succ b ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih]
    apply next
    apply rank_lt

theorem filter_card {ι : Type} [DecidableEq ι] (state : ℕ → Option ι) (b : ℕ) (i : ι)
    (k : ℕ) (hk : k < 2^b) (hstate : ∀ t, t < 2^b → (state t = some i ↔ t = k)) :
    ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => state (rank b w) = some i)).card = 1 := by
  obtain ⟨v,hv⟩ := rank_onto b k hk
  have he : (Finset.univ : Finset (Fin b → Bool)).filter (fun w => state (rank b w) = some i) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hstate _ (rank_lt ..), ← hv]
    exact (rank_inj b).eq_iff
  simp [he]

end BinaryWords851

namespace Network851
open Address851 Clock851
variable (K : ℕ → ℕ) (B p : ℕ) (hp : 0<p)

abbrev Idx (K : ℕ→ℕ) (B p : ℕ) := Fin (size K (B+p))

def phase (b : ℕ) : Fin (B+p) := ⟨clock B p b, clock_lt B b hp⟩

noncomputable def slot (i : Idx K B p) (bit : Bool) := 2*idx K i + BinaryWords851.digit bit

noncomputable def next (i : Idx K B p) (bit : Bool) : Option (Idx K B p) :=
  place K (phase B p hp ((level K i).val+1)) (slot K B p i bit)

noncomputable def head (h0 : K 0=1) : Idx K B p :=
  code K (B+p) ⟨⟨0,by omega⟩,⟨0, by simpa using (show 0<K 0 by omega)⟩⟩

theorem terminate (i : Idx K B p) :
    (fun x : Option (Idx K B p) => x.bind (fun j => next K B p hp j true))^[size K (B+p)] (some i)=none := by
  apply rank_escape K _ i
  intro a j hj
  obtain ⟨_,hh⟩ := (place_some ..).mp hj
  simp [slot,BinaryWords851.digit] at hh
  omega

variable (kp : ∀ b ≥ B, K (b+p)=K b) (kd : ∀ b, K (b+1) ≤ 2*K b)

include kp in
theorem phase_width (b) : K (phase B p hp b) = K b := clock_eq K B p hp kp b

theorem phase_next (b) : phase B p hp ((phase B p hp b).val+1) = phase B p hp (b+1) :=
  Fin.ext (clock_next B p b hp)

include kp kd in
theorem word_result (h0 : K 0=1) (b) (w : Fin b → Bool) :
    (List.ofFn w).foldl (fun (x : Option (Idx K B p)) bit => x.bind (fun i => next K B p hp i bit))
        (some (head K B p hp h0)) = place K (phase B p hp b) (BinaryWords851.rank b w) := by
  apply BinaryWords851.fold _ _ _ (fun b k => place K (phase B p hp b) k)
  · apply (place_some ..).mpr
    constructor
    · apply Fin.ext
      simp [level_code, head, phase, clock_early B p 0 (by omega : 0<B+p)]
    · simp [idx_code,head]
  · intro b k bit hk
    cases he : place K (phase B p hp b) k with
    | none =>
      change none = place K (phase B p hp (b+1)) (2*k+BinaryWords851.digit bit)
      have hx : K (phase B p hp b) ≤ k := by
        by_contra! h
        simp [place,h] at he
      rw [phase_width K B p hp kp] at hx
      have hh := kd b
      have hm : ¬2*k+BinaryWords851.digit bit<K (phase B p hp (b+1)) := by
        rw [phase_width K B p hp kp]
        omega
      simp [place, hm]
    | some i =>
      obtain ⟨hl,hr⟩ := (place_some ..).mp he
      change place K (phase B p hp ((level K i).val+1)) (2*idx K i+BinaryWords851.digit bit)=_
      rw [hl,hr,phase_next]

noncomputable def cnt (h0 : K 0=1) (b : ℕ) (i : Idx K B p) := by
  classical
  exact ((Finset.univ : Finset (Fin b → Bool)).filter (fun w =>
    (List.ofFn w).foldl (fun (x : Option (Idx K B p)) bit => x.bind (fun j => next K B p hp j bit))
      (some (head K B p hp h0)) = some i)).card

include kd in
theorem width_pow (h0 : K 0=1) (b) : K b ≤ 2^b := by
  induction b with
  | zero => simp [h0]
  | succ b ih => rw [pow_succ]; have h := kd b; omega

include kp kd in
theorem counts (h0 : K 0=1) (b i) :
    cnt K B p hp h0 b i = if level K i = phase B p hp b then 1 else 0 := by
  classical
  unfold cnt
  simp only [word_result K B p hp kp kd h0]
  by_cases h : level K i=phase B p hp b
  · rw [if_pos h]
    apply BinaryWords851.filter_card _ _ _ (idx K i)
    · have hi := rank_lt K i
      rw [h, phase_width K B p hp kp] at hi
      exact hi.trans_le (width_pow K kd h0 b)
    · intro t _
      rw [place_some]
      simp [h, eq_comm]
  · rw [if_neg h]
    simp [place_some, h]

include kp kd in
theorem count_total (h0 : K 0=1) (b) : ∑ i, cnt K B p hp h0 b i = K b := by
  simp only [counts K B p hp kp kd h0]
  have h := sum_level K (phase B p hp b) (fun _ => (1:ℕ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  exact h.trans (phase_width K B p hp kp b)

include kp kd in
theorem count_period (h0 : K 0=1) (b) (hb : B ≤ b) (i) :
    cnt K B p hp h0 (b+p) i = cnt K B p hp h0 b i := by
  simp only [counts K B p hp kp kd h0]
  rw [show phase B p hp (b+p)=phase B p hp b from Fin.ext (clock_period B p b hb)]

end Network851

namespace Flow851
open Address851 Clock851 Network851

theorem pairs_sum (x : ℕ → ℝ) (m : ℕ) :
    (∑ i ∈ Finset.range m, (x (2*i)+x (2*i+1))) = ∑ k ∈ Finset.range (2*m), x k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show 2*(m+1)=2*m+1+1 by omega,
      Finset.sum_range_succ _ (2*m+1), Finset.sum_range_succ _ (2*m)]
    ring

variable (K : ℕ → ℕ) (B p : ℕ) (hp : 0<p)

noncomputable def val (v : Idx K B p → ℝ) (l : Fin (B+p)) (k : ℕ) : ℝ :=
  if h : k<K l then v (code K (B+p) ⟨l,⟨k,h⟩⟩) else 0

noncomputable def mass (v : Idx K B p → ℝ) (l : Fin (B+p)) : ℝ :=
  ∑ k ∈ Finset.range (K l), val K B p v l k

noncomputable def out (bank : ℕ → ℕ → ℝ) (i : Idx K B p) (bit : Bool) : ℝ :=
  bank (level K i).val (slot K B p i bit - K (phase B p hp ((level K i).val+1)))

theorem mass_step (v : Idx K B p → ℝ) (bank : ℕ → ℕ → ℝ)
    (hm : ∀ i, 2*v i = ∑ bit : Bool, (next K B p hp i bit).elim (out K B p hp bank i bit) v)
    (l : Fin (B+p)) (hh : K (phase B p hp (l.val+1)) ≤ 2*K l) :
    2*mass K B p v l = mass K B p v (phase B p hp (l.val+1)) +
      ∑ t ∈ Finset.range (2*K l - K (phase B p hp (l.val+1))), bank l.val t := by
  let d := phase B p hp (l.val+1)
  let X := fun k => if k < K d then val K B p v d k else bank l.val (k-K d)
  have step (k : ℕ) (hk : k<K l) :
      2*val K B p v l k = X (2*k)+X (2*k+1) := by
    let i := code K (B+p) ⟨l,⟨k,hk⟩⟩
    have hi : level K i=l := by exact level_code K _
    have hr : idx K i=k := by exact idx_code K _
    have eb (bit : Bool) : (next K B p hp i bit).elim (out K B p hp bank i bit) v =
        X (2*k+BinaryWords851.digit bit) := by
      unfold next out slot
      rw [hi,hr]
      change (place K d _).elim (bank l.val _) v = _
      unfold X place val
      split_ifs <;> rfl
    have h := hm i
    rw [Fintype.sum_bool] at h
    simp only [eb, BinaryWords851.digit, Nat.add_zero] at h
    simpa [val,hk,i,add_comm] using h
  unfold mass
  rw [Finset.mul_sum]
  calc
    _ = ∑ k ∈ Finset.range (K l), (X (2*k)+X (2*k+1)) :=
      Finset.sum_congr rfl fun k hk => step k (Finset.mem_range.mp hk)
    _ = _ := by
      rw [pairs_sum]
      nth_rw 1 [show 2*K l=K d+(2*K l-K d) by dsimp [d]; omega]
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        simp [X,Finset.mem_range.mp hk,d]
      · apply Finset.sum_congr rfl
        intro k _
        simp [X]

end Flow851

namespace Packing851

theorem slice (q m : ℕ) (c : Fin q → ℕ) (hm : m ≤ ∑ j, c j) :
    ∃ v : Fin q → ℕ, (∀ j, v j ≤ c j) ∧ ∑ j, v j = m := by
  induction q generalizing m with
  | zero =>
    simp at hm
    exact ⟨c, fun _ => le_rfl, by simp [hm]⟩
  | succ q ih =>
    let a := min m (c 0)
    have ha : a ≤ m := min_le_left _ _
    have hb : m-a ≤ ∑ j : Fin q, c j.succ := by
      rw [Fin.sum_univ_succ] at hm
      dsimp [a]
      omega
    obtain ⟨v,hl,hs⟩ := ih (m-a) (fun j => c j.succ) hb
    refine ⟨Fin.cons a v, ?_, ?_⟩
    · intro j
      exact Fin.cases (by simpa [a]) (fun i => by simpa using hl i) j
    · rw [Fin.sum_univ_succ]
      simpa [hs, Nat.add_sub_cancel' ha] using (show a + (m-a) = m by omega)

theorem groups (q m E : ℕ) (c : Fin q → ℕ) (hm : ∑ j, c j = m*E) :
    ∃ g : Fin m → Fin q → ℕ, (∀ i, ∑ j, g i j = E) ∧ ∀ j, ∑ i, g i j = c j := by
  induction m generalizing c with
  | zero =>
    refine ⟨fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro j
    simp at hm
    simp [hm j]
  | succ m ih =>
    have hE : E ≤ ∑ j, c j := by rw [hm, Nat.succ_mul]; omega
    obtain ⟨v,hv,hs⟩ := slice q E c hE
    let w := fun j => c j-v j
    have hw (j) : w j+v j = c j := Nat.sub_add_cancel (hv j)
    have hws : ∑ j, w j = m*E := by
      have h : (∑ j, w j) + ∑ j, v j = ∑ j, c j := by
        rw [←Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => hw j
      rw [hs, hm, Nat.succ_mul] at h
      omega
    obtain ⟨g,hg,hj⟩ := ih w hws
    refine ⟨Fin.cons v g, ?_, ?_⟩
    · intro i
      exact Fin.cases (by simpa using hs) (fun k => by simpa using hg k) i
    · intro j
      rw [Fin.sum_univ_succ]
      simpa [hj, Nat.add_comm] using hw j

end Packing851

namespace Harmonic851

variable {ι : Type} [Fintype ι]

def extend (v : ι → ℝ) (s : Option ι) : ℝ := s.elim 0 v

theorem maximum (n : ι → Bool → Option ι) (c : ι → Bool) (L : ℕ)
    (dies : ∀ i, (fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i) = none)
    (v : ι → ℝ) (harm : ∀ i, 2*v i = extend v (n i false) + extend v (n i true)) :
    ∀ i, v i ≤ 0 := by
  classical
  let f := extend v
  let step := fun x : Option ι => x.bind (fun j => n j (c j))
  obtain ⟨s, _, hm⟩ := Finset.exists_max_image (Finset.univ : Finset (Option ι)) f
    ⟨none, Finset.mem_univ _⟩
  have hub (x : Option ι) : f x ≤ f s := hm x (Finset.mem_univ _)
  have preserve (x : Option ι) (hx : f x = f s) : f (step x) = f s := by
    cases x with
    | none => exact hx
    | some i =>
      have h := harm i
      change 2*f (some i) = f (n i false) + f (n i true) at h
      change f (n i (c i)) = f s
      cases c i <;> linarith [hub (n i false), hub (n i true)]
  have along (k : ℕ) : f (step^[k] s) = f s := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply']; exact preserve _ ih
  have hzero : f s = 0 := by
    cases s with
    | none => rfl
    | some i =>
      have hc := along L
      change f ((fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i)) = f (some i) at hc
      rw [dies] at hc
      exact hc.symm
  intro i
  exact (hub (some i)).trans (le_of_eq hzero)

noncomputable def op (n : ι → Bool → Option ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := 2*v i - extend v (n i false) - extend v (n i true)
  map_add' v w := by
    ext i
    cases h : n i false <;> cases k : n i true <;>
      simp [extend, h, k] <;> ring
  map_smul' a v := by
    ext i
    cases h : n i false <;> cases k : n i true <;>
      simp [extend, h, k] <;> ring

theorem solve (n : ι → Bool → Option ι) (c : ι → Bool) (L : ℕ)
    (dies : ∀ i, (fun x : Option ι => x.bind (fun j => n j (c j)))^[L] (some i) = none)
    (g : ι → Bool → ℝ) :
    ∃ v : ι → ℝ, ∀ i, 2*v i = ∑ bit : Bool, (n i bit).elim (g i bit) (fun k => v k) := by
  classical
  have hz (v : ι → ℝ) (hv : op n v = 0) : v = 0 := by
    have hh (i) : 2*v i = extend v (n i false) + extend v (n i true) := by
      have h := congrFun hv i
      change 2*v i - extend v (n i false) - extend v (n i true) = 0 at h
      linarith
    have hneg (i) : 2*(-v) i = extend (-v) (n i false) + extend (-v) (n i true) := by
      have h := hh i
      cases ha : n i false <;> cases hb : n i true <;>
        simp [extend, ha, hb] at * <;> linarith
    funext i
    have a := maximum n c L dies v hh i
    have b := maximum n c L dies (-v) hneg i
    change -v i ≤ 0 at b
    change v i = 0
    linarith
  have hi : Function.Injective (op n) := by
    intro v w h
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub, h, sub_self]
  have hs : Function.Surjective (op n) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hi
  obtain ⟨v,hv⟩ := hs (fun i => (n i false).elim (g i false) (fun _ => 0) +
      (n i true).elim (g i true) (fun _ => 0))
  refine ⟨v, fun i => ?_⟩
  have h := congrFun hv i
  change 2*v i - extend v (n i false) - extend v (n i true) = _ at h
  cases ha : n i false <;> cases hb : n i true <;>
    simp [Fintype.sum_bool, extend, ha, hb] at * <;> linarith

end Harmonic851

namespace Sampler851
open Layers851 Schedule851 Address851 Network851 Flow851

-- This bank is defined at every offset, including those queried by live transitions.
theorem banks {q E : ℕ} (j0 : Fin q) (N : ℕ → ℕ) (em : ℕ → Fin q → ℕ)
    (h : ∀ b, ∑ j, em b j=N b*E) :
    ∃ bank : ℕ → ℕ → Fin q → ℕ, (∀ b t, ∑ j, bank b t j=E) ∧
      ∀ b j, ∑ t ∈ Finset.range (N b), bank b t j = em b j := by
  classical
  have hg (b) := Packing851.groups q (N b) E (em b) (h b)
  choose g hm he using hg
  let bank (b t : ℕ) (j : Fin q) := if ht : t<N b then g b ⟨t,ht⟩ j else if j=j0 then E else 0
  refine ⟨bank, ?_, ?_⟩
  · intro b t
    by_cases ht : t<N b
    · simpa [bank,ht] using hm b ⟨t,ht⟩
    · simp [bank,ht]
  · intro b j
    rw [←Fin.sum_univ_eq_sum_range]
    simpa [bank] using he b j

end Sampler851

end PEqualNP.Outside.L_lib_851

open PEqualNP.Outside.L_lib_851
open Layers851 Schedule851 Address851 Network851 Flow851

theorem PEqualNP.Outside.L_lib_851 :
∀ (q E D h p u : ℕ), 0 < E → 0 < D → 0 < p →
  D ∣ 2^h*(2^p-1) → E ≤ 2^(p*u) →
  ∀ A : Fin q → ℕ, (∑ j, A j) = D*E → (∃ j, A j % D ≠ 0) →
  let K := fun b : ℕ => 2^b-(∑ j : Fin q, (2^b*A j)/D)/E
  let B := h+p*(u+1)
  let S := ∑ b ∈ Finset.range (B+p), K b
  ∃ (z : Fin S) (n : Fin S → Bool → Option (Fin S))
    (g : Fin S → Bool → Fin q → ℕ) (v : Fin S → Fin q → ℝ),
    let run := fun (b : ℕ) (w : Fin b → Bool) =>
      (List.ofFn w).foldl (fun (x : Option (Fin S)) (bit : Bool) =>
        x.bind (fun i => n i bit)) (some z)
    let count := fun (b : ℕ) (i : Fin S) =>
      ((Finset.univ : Finset (Fin b → Bool)).filter (fun w => run b w = some i)).card
    (∃ c : Fin S → Bool, ∀ i : Fin S,
      (fun x : Option (Fin S) => x.bind (fun j => n j (c j)))^[S] (some i) = none) ∧
    (∀ i bit, (∑ j, g i bit j) = E) ∧
    (∀ i j, 2*v i j = ∑ bit : Bool, (n i bit).elim (g i bit j : ℝ) (fun k => v k j)) ∧
    (∀ j, (D : ℝ)*v z j = A j) ∧ (∀ b, (∑ i, count b i) = K b) ∧
    ∀ b ≥ B, ∀ i, count (b+p) i = count b i := by
  classical
  intro q E D h p u he hd hp hv hu A hs hn
  let K := width E D A
  let B := h+p*(u+1)
  have h0 : K 0=1 := zero_width hd he A hs hn
  have kd : ∀ b, K (b+1)≤2*K b := width_step hd he A hs
  have kp (b) (hb : B≤b) : K (b+p)=K b := (periods hd he hv A hs b (by dsimp [B] at hb; omega)).1
  let em := emit (D:=D) (E:=E) A
  let N := fun b => 2*K b-K (b+1)
  obtain ⟨j0,hj0⟩ := hn
  obtain ⟨bank,hbank,hem⟩ := Sampler851.banks j0 N em (pay_count A hd he hs ⟨j0,hj0⟩)
  let n := next K B p hp
  let z := head K B p hp h0
  let g := fun (i : Idx K B p) bit =>
      bank (level K i).val (slot K B p i bit-K (phase B p hp ((level K i).val+1)))
  have hstop (i : Idx K B p) :
      (fun x : Option (Idx K B p) => x.bind (fun j => n j true))^[size K (B+p)] (some i)=none :=
    terminate K B p hp i
  have hh (j : Fin q) := Harmonic851.solve n (fun _ => true) _ hstop (fun i bit => (g i bit j:ℝ))
  choose v hvv using hh
  refine ⟨z,n,g,(fun i j => v j i),⟨fun _ => true,hstop⟩,?_,?_,?_,?_,?_⟩
  · intro i bit
    apply hbank
  · intro i j
    exact hvv j i
  · intro j
    let V := fun b => mass K B p (v j) (phase B p hp b)
    let W := fun b => debt (D:=D) (E:=E) A b j
    have hh (b : ℕ) : 2*V b = V (b+1) + (em b j:ℝ) := by
      let l := phase B p hp b
      let rbank := fun d t => (bank d t j:ℝ)
      have hnext : phase B p hp (l.val+1) = phase B p hp (b+1) := phase_next B p hp b
      have hw : K (phase B p hp (l.val+1)) = K (l.val+1) := phase_width K B p hp kp _
      have hnode (i : Idx K B p) : 2*v j i =
          ∑ bit : Bool, (next K B p hp i bit).elim (out K B p hp rbank i bit) (v j) := hvv j i
      have hstep := mass_step K B p hp (v j) rbank hnode l (by rw [hw]; exact kd l.val)
      have hpay : (∑ t ∈ Finset.range (N l.val), rbank l.val t) = (em l.val j:ℝ) := by
        dsimp [rbank]
        exact_mod_cast hem l.val j
      have heq : em l.val j=em b j :=
        Clock851.clock_eq (fun d => em d j) B p hp (fun d hd' => periodic_emit A hd he hp hv hu hs d hd' j) b
      change 2*mass K B p (v j) l = mass K B p (v j) (phase B p hp (b+1)) + _
      rw [←hnext, hstep]
      congr 1
      rw [hw]
      exact hpay.trans (by exact_mod_cast heq)
    have hvper : V (B+p)=V B := by
      apply congrArg (mass K B p (v j))
      exact Fin.ext (Clock851.clock_period B p B le_rfl)
    have hwper : W (B+p)=W B := debt_period A hd he hp hv hu hs B le_rfl j
    have hroot := same_initial V W (fun b => (em b j:ℝ)) B p hp hh (fun b => debt_step A hd b j) hvper hwper
    have v0 : V 0=v j z := by
      have l0 : (phase B p hp 0).val = 0 := Clock851.clock_early B p 0 (by omega)
      have hK : K (phase B p hp 0) = 1 := by rw [l0,h0]
      change (∑ k ∈ Finset.range (K (phase B p hp 0)), val K B p (v j) (phase B p hp 0) k)=_
      rw [hK,Finset.sum_range_one]
      unfold val
      rw [dif_pos (by omega : 0<K (phase B p hp 0))]
      apply congrArg (v j)
      have hph : phase B p hp 0 = (⟨0,by omega⟩ : Fin (B+p)) := Fin.ext l0
      unfold z head
      exact code_same K _ _ _ _ hph rfl
    have w0 : W 0=(A j:ℝ)/D := debt_initial A j
    rw [v0,w0] at hroot
    change (D:ℝ)*v j z=(A j:ℝ)
    rw [hroot]
    field_simp
  · exact count_total K B p hp kp kd h0
  · exact count_period K B p hp kp kd h0
