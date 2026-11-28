import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25883

namespace PEqualNP.Outside.L_meta_33643

abbrev W (k : ℕ) := Fin k → Bool

def ix (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k := ⟨i % k, Nat.mod_lt _ hk⟩

def add {k : ℕ} (x y : W k) (p : Fin k) : Bool := xor (x p) (y p)

def mix {k : ℕ} (hk : 0 < k) (gap : ℕ) (x : W k) (p : Fin k) : Bool :=
  xor (xor (x (ix k hk (p.val + k - gap % k))) (x p)) (x (ix k hk (p.val + gap)))

def step {k : ℕ} (hk : 0 < k) (z : W k) (p : Fin k) : Bool :=
  xor (z p) (!(z (ix k hk (p.val + 1))) && z (ix k hk (p.val + 2)))

def rot {k : ℕ} (hk : 0 < k) (s : ℕ) (x : W k) (p : Fin k) : Bool :=
  x (ix k hk (p.val + k - s % k))

def key {k : ℕ} (hk : 0 < k) (raw : W k) (endSite : ℕ) (ab : Bool × Bool) (p : Fin k) : Bool :=
  if p = ix k hk (endSite + 1) then ab.1 else if p = ix k hk (endSite + 2) then ab.2 else raw p

def read {k : ℕ} (hk : 0 < k) (h start gap ini fin : ℕ) (c name x : W k) (j : Fin h) : Bool :=
  xor (step hk (mix hk gap (add (rot hk ini x) name)) (ix k hk (start + j.val)))
    (xor (rot hk fin x (ix k hk (start + j.val))) (c (ix k hk (start + j.val))))

theorem xor_false_iff : ∀ a b : Bool, xor a b = false ↔ a = b := by decide

theorem xor_test : ∀ μ P K T : Bool, xor (xor μ P) K = T ↔ μ = xor (xor T K) P := by decide

theorem xor_not3 : ∀ a b c d e f : Bool,
    xor (xor (xor a (!b)) (xor c d)) (xor e f) = xor (xor (xor (xor a b) (xor c d)) (xor e f)) true := by
  decide

theorem xor9 : ∀ a b c d e f g h i : Bool,
    xor (xor (xor (xor a g) b) (xor (xor c h) d)) (xor (xor e i) f) =
      xor (xor (xor (xor a b) (xor c d)) (xor e f)) (xor (xor g h) i) := by
  decide

abbrev chain (h : ℕ) (τ μ : ℕ → Bool) : Prop := ∀ j < h, μ j = xor (τ j) (!μ (j+1) && μ (j+2))

def extend {r : ℕ} (w : Fin r → Bool) (i : ℕ) : Bool := if hi : i < r then w ⟨i, hi⟩ else false

theorem chain_congr {h : ℕ} {τ τ' μ μ' : ℕ → Bool} (hτ : ∀ j < h, τ j = τ' j)
    (hμ : ∀ j < h, μ j = μ' j ∧ μ (j+1) = μ' (j+1) ∧ μ (j+2) = μ' (j+2)) :
    chain h τ μ ↔ chain h τ' μ' := by
  refine forall₂_congr fun j hj => ?_
  obtain ⟨e0, e1, e2⟩ := hμ j hj
  rw [hτ j hj, e0, e1, e2]

theorem chain_split (m d : ℕ) (τ μ : ℕ → Bool) :
    chain (m + d) τ μ ↔ chain m τ μ ∧ chain d (fun i => τ (m+i)) (fun i => μ (m+i)) := by
  constructor
  · intro H
    exact ⟨fun j hj => H j (by omega), fun i hi => by simpa only [Nat.add_assoc] using H (m+i) (by omega)⟩
  · rintro ⟨H1, H2⟩ j hj
    by_cases hjm : j < m
    · exact H1 j hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
      simpa only [Nat.add_assoc] using H2 i (by omega)

theorem halve {α : Type*} (S : Finset α) (f : α → α) (hS : ∀ u ∈ S, f u ∈ S) (hinv : ∀ u, f (f u) = u)
    (p : α → Bool) (hp : ∀ u, p (f u) = !p u) :
    2 * (S.filter fun u => p u = false).card = S.card := by
  have e : (S.filter fun u => p u = false).card = (S.filter fun u => ¬p u = false).card :=
    Finset.card_nbij' f f (fun u hu => by simp_all) (fun u hu => by simp_all)
      (fun u _ => hinv u) (fun u _ => hinv u)
  have := Finset.card_filter_add_card_filter_not (s := S) (fun u => p u = false)
  omega

section Count

variable {α : Type*} [Fintype α]

theorem triangular (G : α → ℕ → Bool) (f : ℕ → α → α) (N : ℕ)
    (hinv : ∀ q < N, ∀ u, f q (f q u) = u) (htog : ∀ q < N, ∀ u, G (f q u) q = !G u q)
    (hkeep : ∀ q q', q < q' → q' < N → ∀ u, G (f q u) q' = G u q') :
    2^N * (Finset.univ.filter fun u => ∀ q < N, G u q = false).card = Fintype.card α := by
  have top : ∀ d ≤ N, 2^d * (Finset.univ.filter fun u =>
      ∀ q, N - d ≤ q → q < N → G u q = false).card = Fintype.card α := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Finset.filter_true_of_mem fun u _ q h1 h2 => absurd h2 (by omega)]
      simp
    | succ d ih =>
      intro hd
      set S := Finset.univ.filter fun u => ∀ q, N - d ≤ q → q < N → G u q = false
      have hsplit : (Finset.univ.filter fun u => ∀ q, N - (d+1) ≤ q → q < N → G u q = false) =
          S.filter fun u => G u (N - (d+1)) = false := by
        ext u
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro H
          exact ⟨fun q h1 h2 => H q (by omega) h2, H _ le_rfl (by omega)⟩
        · rintro ⟨H, H'⟩ q h1 h2
          by_cases hq : q = N - (d+1)
          · rw [hq]; exact H'
          · exact H q (by omega) h2
      have hS : ∀ u ∈ S, f (N - (d+1)) u ∈ S := by
        intro u hu
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        intro q h1 h2
        rw [hkeep _ _ (by omega) h2]
        exact hu q h1 h2
      rw [hsplit, pow_succ, mul_assoc, halve S _ hS (hinv _ (by omega)) (fun u => G u (N - (d+1)))
        (htog _ (by omega))]
      exact ih (by omega)
  simpa using top N le_rfl

def solve (ν : α → ℕ → Bool) (m : ℕ) (τ w : ℕ → Bool) (u : α) (q : ℕ) : Bool :=
  if q < m then xor (τ q) (!ν u (q+1) && ν u (q+2)) else w (q - m)

theorem fiber (ν : α → ℕ → Bool) (f : ℕ → α → α) (N : ℕ) (hinv : ∀ q < N, ∀ u, f q (f q u) = u)
    (hflip : ∀ q q', q ≤ q' → q' < N → ∀ u, ν (f q u) q' = xor (ν u q') (decide (q' = q)))
    (m r : ℕ) (hmr : m + r = N) (hr : 2 ≤ r) (τ w : ℕ → Bool) :
    2^N * (Finset.univ.filter fun u => chain m τ (ν u) ∧ ∀ i < r, ν u (m+i) = w i).card =
      Fintype.card α := by
  have hF : ∀ q q', q ≤ q' → q' < N → ∀ u, solve ν m τ w (f q u) q' = solve ν m τ w u q' := by
    intro q q' h1 h2 u
    by_cases hq' : q' < m
    · simp only [solve, ite_eq_left hq', hflip q (q'+1) (by omega) (by omega),
        hflip q (q'+2) (by omega) (by omega)]
      simp [show q' + 1 ≠ q by omega, show q' + 2 ≠ q by omega]
    · simp only [solve, ite_eq_right hq']
  rw [← triangular (fun u q => xor (ν u q) (solve ν m τ w u q)) f N hinv
    (fun q hq u => by simp [hflip q q le_rfl hq, hF q q le_rfl hq])
    (fun q q' h1 h2 u => by simp [hflip q q' h1.le h2, hF q q' h1.le h2, show q' ≠ q by omega])]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr fun u _ => ?_)
  simp only [xor_false_iff]
  constructor
  · rintro ⟨H1, H2⟩ q hq
    by_cases hqm : q < m
    · simpa only [solve, ite_eq_left hqm] using H1 q hqm
    · obtain ⟨i, rfl⟩ : ∃ i, q = m + i := ⟨q - m, by omega⟩
      simpa [solve] using H2 i (by omega)
  · intro H
    refine ⟨fun q hq => ?_, fun i hi => ?_⟩
    · simpa [solve, hq] using H q (by omega)
    · simpa [solve] using H (m+i) (by omega)

theorem bankCount (ν : α → ℕ → Bool) (f : ℕ → α → α) (N : ℕ) (hinv : ∀ q < N, ∀ u, f q (f q u) = u)
    (hflip : ∀ q q', q ≤ q' → q' < N → ∀ u, ν (f q u) q' = xor (ν u q') (decide (q' = q)))
    (m r : ℕ) (hmr : m + r = N) (hr : 2 ≤ r) (τ : ℕ → Bool) (P : (Fin r → Bool) → Prop)
    [DecidablePred P] :
    2^N * (Finset.univ.filter fun u => chain m τ (ν u) ∧ P fun i => ν u (m + i)).card =
      (Finset.univ.filter P).card * Fintype.card α := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun u => fun i : Fin r => ν u (m + i))
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)), Finset.mul_sum,
    Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.filter_filter]
  by_cases hw : P w
  · rw [ite_eq_left hw, one_mul, ← fiber ν f N hinv hflip m r hmr hr τ (extend w)]
    congr 1
    refine congrArg Finset.card (Finset.filter_congr fun u _ => ?_)
    constructor
    · rintro ⟨⟨H1, -⟩, H2⟩
      refine ⟨H1, fun i hi => ?_⟩
      rw [← H2]
      simp [extend, hi]
    · rintro ⟨H1, H2⟩
      have e : (fun i : Fin r => ν u (m + i)) = w :=
        funext fun i => by simpa [extend] using H2 i i.isLt
      exact ⟨⟨H1, e ▸ hw⟩, e⟩
  · rw [ite_eq_right hw, zero_mul, Finset.card_eq_zero.mpr, mul_zero]
    apply Finset.filter_false_of_mem
    rintro u - ⟨⟨-, H⟩, e⟩
    exact hw (e ▸ H)

end Count

section Bank

variable {k : ℕ} (hk : 0 < k) (start : ℕ)

def pos (e : ℕ) : Fin k := ix k hk (start + (k - 5) + e)

theorem ix_back (a d : ℕ) : ix k hk ((ix k hk (a + d)).val + k - d % k) = ix k hk a := by
  apply Fin.ext
  change ((a + d) % k + k - d % k) % k = a % k
  have hd : d % k ≤ k := (Nat.mod_lt _ hk).le
  have H : d + (k - d % k) = k * (d / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    have := Nat.mod_add_div d k
    omega
  rw [Nat.add_sub_assoc hd, Nat.mod_add_mod, Nat.add_assoc, H]
  simp

theorem pos_add (e c : ℕ) : ix k hk ((pos hk start e).val + c) = pos hk start (e + c) := by
  apply Fin.ext
  simp only [pos, ix, Nat.mod_add_mod, Nat.add_assoc]

theorem pos_sub (e g : ℕ) (hg : g ≤ e) :
    ix k hk ((pos hk start e).val + k - g % k) = pos hk start (e - g) := by
  have := ix_back hk (start + (k - 5) + (e - g)) g
  rwa [show start + (k - 5) + (e - g) + g = start + (k - 5) + e by omega] at this

theorem site (h5 : 5 ≤ k) (j : ℕ) : ix k hk (start + j) = pos hk start (j + 5) := by
  apply Fin.ext
  simp only [pos, ix]
  rw [show start + (k - 5) + (j + 5) = start + j + k by omega, Nat.add_mod_right]

theorem pos_eq_iff {e e' : ℕ} (h1 : e < e' + k) (h2 : e' < e + k) :
    pos hk start e = pos hk start e' ↔ e = e' := by
  refine ⟨fun H => ?_, fun H => H ▸ rfl⟩
  have hmod : (start + (k - 5) + e) % k = (start + (k - 5) + e') % k := congrArg Fin.val H
  have hc : e % k = e' % k := Nat.ModEq.add_left_cancel' _ hmod
  rcases le_total e e' with hle | hle
  · have := Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' hle).mp hc) (by omega)
    omega
  · have := Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' hle).mp hc.symm) (by omega)
    omega

theorem step_pos (z : W k) (e : ℕ) :
    step hk z (pos hk start e) =
      xor (z (pos hk start e)) (!z (pos hk start (e+1)) && z (pos hk start (e+2))) := by
  simp only [step, pos_add]

theorem rot_pos (s : ℕ) (x : W k) (e : ℕ) (hs : s ≤ e) :
    rot hk s x (pos hk start e) = x (pos hk start (e - s)) := by
  simp only [rot, pos_sub hk start e s hs]

theorem mix_pos (gap : ℕ) (z : W k) (e : ℕ) (hg : gap ≤ e) :
    mix hk gap z (pos hk start e) =
      xor (xor (z (pos hk start (e - gap))) (z (pos hk start e))) (z (pos hk start (e + gap))) := by
  simp only [mix, pos_sub hk start e gap hg, pos_add]

def M (gap ini : ℕ) (x n : W k) (q : ℕ) : Bool := mix hk gap (add (rot hk ini x) n) (pos hk start (q + 5))

theorem M_eq (gap ini : ℕ) (x n : W k) (q : ℕ) (hg : ini + gap ≤ 5) :
    M hk start gap ini x n q =
      xor (xor (xor (x (pos hk start (q+5-gap-ini))) (n (pos hk start (q+5-gap))))
        (xor (x (pos hk start (q+5-ini))) (n (pos hk start (q+5)))))
        (xor (x (pos hk start (q+5+gap-ini))) (n (pos hk start (q+5+gap)))) := by
  simp only [M, mix_pos hk start gap _ _ (by omega : gap ≤ q + 5), add]
  rw [rot_pos hk start ini x (q+5-gap) (by omega), rot_pos hk start ini x (q+5) (by omega),
    rot_pos hk start ini x (q+5+gap) (by omega)]

theorem M_key (gap ini : ℕ) (x x' n : W k) (q : ℕ) (hg : ini + gap ≤ 5) (d : ℕ → Bool)
    (hd : ∀ e ≤ q + 5 + gap - ini, x' (pos hk start e) = xor (x (pos hk start e)) (d e)) :
    M hk start gap ini x' n q =
      xor (M hk start gap ini x n q) (xor (xor (d (q+5-gap-ini)) (d (q+5-ini))) (d (q+5+gap-ini))) := by
  rw [M_eq hk start gap ini x' n q hg, M_eq hk start gap ini x n q hg,
    hd (q+5-gap-ini) (by omega), hd (q+5-ini) (by omega), hd (q+5+gap-ini) (by omega)]
  exact xor9 _ _ _ _ _ _ _ _ _

def flip (e : ℕ) (n : W k) : W k := Function.update n (pos hk start e) (!n (pos hk start e))

theorem flip_flip (e : ℕ) (n : W k) : flip hk start e (flip hk start e n) = n := by
  simp [flip]

theorem flip_same (e : ℕ) (n : W k) : flip hk start e n (pos hk start e) = !n (pos hk start e) := by
  simp [flip]

theorem flip_other {e e' : ℕ} (n : W k) (hne : e' ≠ e) (h1 : e < e' + k) (h2 : e' < e + k) :
    flip hk start e n (pos hk start e') = n (pos hk start e') :=
  Function.update_of_ne (fun H => hne ((pos_eq_iff hk start h2 h1).mp H)) _ _

theorem M_flip (gap ini : ℕ) (x n : W k) (q q' : ℕ) (hg : ini + gap ≤ 5) (hg1 : 1 ≤ gap)
    (hqq : q ≤ q') (hk' : q' + 2 * gap < k) :
    M hk start gap ini x (flip hk start (q + 5 - gap) n) q' =
      xor (M hk start gap ini x n q') (decide (q' = q)) := by
  rw [M_eq hk start gap ini _ _ _ hg, M_eq hk start gap ini _ _ _ hg,
    flip_other hk start n (e := q + 5 - gap) (e' := q' + 5) (by omega) (by omega) (by omega),
    flip_other hk start n (e := q + 5 - gap) (e' := q' + 5 + gap) (by omega) (by omega) (by omega)]
  by_cases h : q' = q
  · subst h
    rw [flip_same, decide_eq_true rfl]
    exact xor_not3 _ _ _ _ _ _
  · rw [flip_other hk start n (e := q + 5 - gap) (e' := q' + 5 - gap) (by omega) (by omega) (by omega)]
    simp [h]

variable (h : ℕ) (raw : W k) (last : ℕ)

def δ (h : ℕ) (c : Bool × Bool) (e : ℕ) : Bool :=
  xor (if e = h + 5 then c.1 else false) (if e = h + 6 then c.2 else false)

theorem key_at (hlast : last + 1 = h) (hhk : h + 7 ≤ k) (c : Bool × Bool) (e : ℕ) (he : e ≤ h + 6) :
    key hk raw (start + last) c (pos hk start e) =
      if e = h + 5 then c.1 else if e = h + 6 then c.2 else raw (pos hk start e) := by
  have h5 : 5 ≤ k := by omega
  rw [key, show start + last + 1 = start + h by omega, show start + last + 2 = start + (h + 1) by omega,
    site hk start h5, site hk start h5]
  simp only [pos_eq_iff hk start (e := e) (e' := h + 5) (by omega) (by omega),
    pos_eq_iff hk start (e := e) (e' := h + 1 + 5) (by omega) (by omega)]

theorem key_shift (hlast : last + 1 = h) (hhk : h + 7 ≤ k) (c : Bool × Bool) (e : ℕ) (he : e ≤ h + 6) :
    key hk raw (start + last) c (pos hk start e) =
      xor (key hk raw (start + last) (false, false) (pos hk start e)) (δ h c e) := by
  rw [key_at hk start h raw last hlast hhk c e he, key_at hk start h raw last hlast hhk _ e he]
  simp only [δ]
  split_ifs <;> first | omega | simp

theorem read_eq (h5 : 5 ≤ k) (gap ini fin : ℕ) (hfin : fin ≤ 5) (cst n x : W k) (j : ℕ) (hj : j < h) :
    read hk h start gap ini fin cst n x ⟨j, hj⟩ =
      xor (xor (M hk start gap ini x n j) (!M hk start gap ini x n (j+1) && M hk start gap ini x n (j+2)))
        (xor (x (pos hk start (j+5-fin))) (cst (pos hk start (j+5)))) := by
  simp only [read, site hk start h5, step_pos, rot_pos hk start fin x (j + 5) (by omega)]
  rfl

theorem test_iff (h5 : 5 ≤ k) (gap ini fin : ℕ) (hfin : fin ≤ 5) (cst n x : W k) (target : Fin h → Bool) :
    read hk h start gap ini fin cst n x = target ↔
      chain h (fun j => xor (extend target j) (xor (x (pos hk start (j+5-fin))) (cst (pos hk start (j+5)))))
        (M hk start gap ini x n) := by
  rw [funext_iff, Fin.forall_iff]
  refine forall₂_congr fun j hj => ?_
  rw [read_eq hk start h h5 gap ini fin hfin cst n x j hj]
  simp only [extend, dite_eq_left hj]
  exact xor_test _ _ _ _

theorem bankCard (hlast : last + 1 = h) (hhk : h + 7 ≤ k) (gap ini fin : ℕ) (hg1 : 1 ≤ gap)
    (hg2 : gap ≤ 2) (hgi : gap ≤ ini) (hg : ini + gap ≤ 5) (hfin : fin ≤ 5) (cst : W k)
    (target : Fin h → Bool) (τ : ℕ → Bool)
    (hτ : ∀ j, τ j = xor (extend target j) (xor (raw (pos hk start (j+5-fin))) (cst (pos hk start (j+5)))))
    (s : Bool × Bool → ℕ → Bool)
    (hs : ∀ c q, q ≤ h + 1 →
      xor (xor (δ h c (q+5-gap-ini)) (δ h c (q+5-ini))) (δ h c (q+5+gap-ini)) = s c q)
    (hs0 : ∀ c q, q < h → s c q = false)
    (m d : ℕ) (hmd : m + d = h) (hd : d ≤ 2) (hm : ∀ j < m, j + 2 < h)
    (σ : Bool × Bool → ℕ → Bool) (hσ : ∀ c i, s c (m + i) = σ c i)
    (J : Finset (Bool × Bool)) (hJ : J.Nonempty) :
    2^(h+2) * (Finset.univ.filter fun n =>
        ∀ c ∈ J, read hk h start gap ini fin cst n (key hk raw (start + last) c) = target).card =
      (Finset.univ.filter fun w : Fin (d+2) → Bool => ∀ c ∈ J,
        chain d (fun i => if i = 0 then τ m else τ (m+1)) (fun i => xor (extend w i) (σ c i))).card * 2^k := by
  have h5 : 5 ≤ k := by omega
  let x0 := key hk raw (start + last) (false, false)
  have count := bankCount (fun n q => M hk start gap ini x0 n q) (fun q => flip hk start (q + 5 - gap))
    (h+2) (fun q _ n => flip_flip hk start _ n)
    (fun q q' h1 h2 n => M_flip hk start gap ini x0 n q q' hg hg1 h1 (by omega)) m (d+2) (by omega)
    (by omega) τ (fun w => ∀ c ∈ J,
      chain d (fun i => if i = 0 then τ m else τ (m+1)) (fun i => xor (extend w i) (σ c i)))
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at count
  rw [← count]
  congr 1
  refine congrArg Finset.card (Finset.filter_congr fun n _ => ?_)
  have hbank : ∀ c, read hk h start gap ini fin cst n (key hk raw (start + last) c) = target ↔
      chain h τ (fun q => xor (M hk start gap ini x0 n q) (s c q)) := by
    intro c
    rw [test_iff hk start h h5 gap ini fin hfin cst n _ target]
    have hM : ∀ q ≤ h + 1,
        M hk start gap ini (key hk raw (start + last) c) n q = xor (M hk start gap ini x0 n q) (s c q) := by
      intro q hq
      rw [M_key hk start gap ini x0 _ n q hg (δ h c)
        (fun e he => key_shift hk start h raw last hlast hhk c e (by omega)), hs c q hq]
    refine chain_congr (fun j hj => ?_) (fun j hj => ⟨hM j (by omega), hM (j+1) (by omega), hM (j+2) (by omega)⟩)
    rw [hτ, key_at hk start h raw last hlast hhk c _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  have hsplit : ∀ μ, chain h τ μ ↔ chain m τ μ ∧ chain d (fun i => τ (m+i)) (fun i => μ (m+i)) := by
    intro μ
    subst hmd
    exact chain_split m d τ μ
  have hlow : ∀ c, chain m τ (fun q => xor (M hk start gap ini x0 n q) (s c q)) ↔
      chain m τ (fun q => M hk start gap ini x0 n q) := fun c =>
    chain_congr (fun _ _ => rfl) fun j hj => by
      have := hm j hj
      simp [hs0 c j (by omega), hs0 c (j+1) (by omega), hs0 c (j+2) (by omega)]
  have htop : ∀ c, chain d (fun i => τ (m+i)) (fun i => xor (M hk start gap ini x0 n (m+i)) (s c (m+i))) ↔
      chain d (fun i => if i = 0 then τ m else τ (m+1))
        (fun i => xor (extend (fun i : Fin (d+2) => M hk start gap ini x0 n (m + i)) i) (σ c i)) := fun c =>
    chain_congr (fun i hi => by rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl <;> simp)
      fun i hi => by
        simp [extend, hσ, show i < d + 2 by omega, show i + 1 < d + 2 by omega,
          show i + 2 < d + 2 by omega]
  simp only [hbank, hsplit, hlow, htop]
  obtain ⟨c0, hc0⟩ := hJ
  exact ⟨fun H => ⟨(H c0 hc0).1, fun c hc => (H c hc).2⟩, fun H c hc => ⟨H.1, H.2 c hc⟩⟩

end Bank

def sR (h : ℕ) (c : Bool × Bool) (q : ℕ) : Bool :=
  xor (if q = h then c.1 else false) (if q = h + 1 then xor c.1 c.2 else false)

def sC (h : ℕ) (c : Bool × Bool) (q : ℕ) : Bool := if q = h + 1 then c.1 else false

def coef (J : Finset (Bool × Bool)) (rich : Bool) : ℕ :=
  if J.card = 1 then 8 else if J.card = 4 then 0 else if (J.image Prod.fst).card = 1 then 4
  else if rich then 4 - J.card else 0

theorem window1 : ∀ J : Finset (Bool × Bool), J.Nonempty → ∀ t0 t1 s0 s1 : Bool,
    8 * (Finset.univ.filter fun w : Fin (1+2) → Bool => ∀ c ∈ J,
        chain 1 (fun i => if i = 0 then t0 else t1) (fun i => xor (extend w i) (sR 1 c i))).card *
      (Finset.univ.filter fun w : Fin (1+2) → Bool => ∀ c ∈ J,
        chain 1 (fun i => if i = 0 then s0 else s1) (fun i => xor (extend w i) (sC 1 c i))).card =
    16 * coef J true := by
  decide

theorem window2 : ∀ J : Finset (Bool × Bool), J.Nonempty → ∀ t0 t1 s0 s1 : Bool,
    8 * (Finset.univ.filter fun w : Fin (2+2) → Bool => ∀ c ∈ J,
        chain 2 (fun i => if i = 0 then t0 else t1) (fun i => xor (extend w i) (sR 2 c i))).card *
      (Finset.univ.filter fun w : Fin (2+2) → Bool => ∀ c ∈ J,
        chain 2 (fun i => if i = 0 then s0 else s1) (fun i => xor (extend w i) (sC 2 c i))).card =
    16 * coef J t1 := by
  decide

theorem sR_shift (m d : ℕ) (c : Bool × Bool) (i : ℕ) : sR (m + d) c (m + i) = sR d c i := by
  simp only [sR, Nat.add_assoc, Nat.add_left_cancel_iff]

theorem sC_shift (m d : ℕ) (c : Bool × Bool) (i : ℕ) : sC (m + d) c (m + i) = sC d c i := by
  simp only [sC, Nat.add_assoc, Nat.add_left_cancel_iff]

theorem target_eq (J : Finset (Bool × Bool)) (rich : Prop) [Decidable rich] (b : Bool)
    (hb : rich ↔ b = true) (F : ℕ) :
    (if J.card = 1 then 8 * F else if J.card = 4 then 0 else if (J.image Prod.fst).card = 1 then 4 * F
      else if rich then (4 - J.card) * F else 0) = coef J b * F := by
  simp only [coef, hb]
  split_ifs <;> simp

theorem arith (k h a b A B X : ℕ) (hkh : h ≤ k) (hR : 2^(h+2) * a = A * 2^k)
    (hC : 2^(h+2) * b = B * 2^k) (hW : 8 * A * B = 16 * X) : 8 * (a * b) = X * 2^(2*(k-h)) := by
  apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^(h+2) * 2^(h+2))
  have hF : 2^(2*(k-h)) * (2^(h+2) * 2^(h+2)) = 16 * (2^k * 2^k) := by
    rw [← pow_add, ← pow_add, show (16 : ℕ) = 2^4 by norm_num, ← pow_add, ← pow_add]
    congr 1
    omega
  calc 8 * (a * b) * (2^(h+2) * 2^(h+2)) = 8 * (2^(h+2) * a) * (2^(h+2) * b) := by ring
    _ = 8 * A * B * (2^k * 2^k) := by rw [hR, hC]; ring
    _ = X * 2^(2*(k-h)) * (2^(h+2) * 2^(h+2)) := by rw [hW, mul_assoc X, hF]; ring

theorem main (k h start : ℕ) (hk : 0 < k) (hh : 0 < h) (hhk : h + 7 ≤ k) (rc cc raw : W k)
    (rt ct : Fin h → Bool) (last : Fin h) (hlast : last.val + 1 = h) (J : Finset (Bool × Bool))
    (hJ : J.Nonempty) :
    8 * (Finset.univ.filter fun pair : W k × W k => ∀ corner ∈ J,
        read hk h start 1 1 0 rc pair.1 (key hk raw (start + last.val) corner) = rt ∧
        read hk h start 2 3 4 cc pair.2 (key hk raw (start + last.val) corner) = ct).card =
      if J.card = 1 then 8 * 2^(2*(k-h)) else if J.card = 4 then 0
      else if (J.image Prod.fst).card = 1 then 4 * 2^(2*(k-h))
      else if (h = 1 ∨ xor (rt last) (xor (raw (ix k hk (start + last.val)))
        (rc (ix k hk (start + last.val)))) = true) then (4 - J.card) * 2^(2*(k-h)) else 0 := by
  have h5 : 5 ≤ k := by omega
  have hprod : (Finset.univ.filter fun pair : W k × W k => ∀ corner ∈ J,
      read hk h start 1 1 0 rc pair.1 (key hk raw (start + last.val) corner) = rt ∧
      read hk h start 2 3 4 cc pair.2 (key hk raw (start + last.val) corner) = ct) =
      (Finset.univ.filter fun n => ∀ c ∈ J, read hk h start 1 1 0 rc n (key hk raw (start + last.val) c) = rt) ×ˢ
      (Finset.univ.filter fun n => ∀ c ∈ J, read hk h start 2 3 4 cc n (key hk raw (start + last.val) c) = ct) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    exact ⟨fun H => ⟨fun c hc => (H c hc).1, fun c hc => (H c hc).2⟩, fun H c hc => ⟨H.1 c hc, H.2 c hc⟩⟩
  obtain ⟨τR, hτR⟩ : ∃ τ : ℕ → Bool, ∀ j, τ j = xor (extend rt j)
      (xor (raw (pos hk start (j+5-0))) (rc (pos hk start (j+5)))) := ⟨_, fun _ => rfl⟩
  obtain ⟨τC, hτC⟩ : ∃ τ : ℕ → Bool, ∀ j, τ j = xor (extend ct j)
      (xor (raw (pos hk start (j+5-4))) (cc (pos hk start (j+5)))) := ⟨_, fun _ => rfl⟩
  have hsR : ∀ c q, q ≤ h + 1 →
      xor (xor (δ h c (q+5-1-1)) (δ h c (q+5-1))) (δ h c (q+5+1-1)) = sR h c q := by
    intro c q hq
    rcases (show q < h ∨ q = h ∨ q = h + 1 by omega) with hq' | rfl | rfl <;>
      simp (disch := omega) only [δ, sR, ite_eq_left, ite_eq_right, Bool.xor_false, Bool.false_xor, ↓reduceIte]
  have hsC : ∀ c q, q ≤ h + 1 →
      xor (xor (δ h c (q+5-2-3)) (δ h c (q+5-3))) (δ h c (q+5+2-3)) = sC h c q := by
    intro c q hq
    rcases (show q < h ∨ q = h ∨ q = h + 1 by omega) with hq' | rfl | rfl <;>
      simp (disch := omega) only [δ, sC, ite_eq_left, ite_eq_right, Bool.xor_false, Bool.false_xor, ↓reduceIte]
  have hsR0 : ∀ c q, q < h → sR h c q = false := by
    intro c q hq
    simp (disch := omega) only [sR, ite_eq_right, Bool.xor_false]
  have hsC0 : ∀ c q, q < h → sC h c q = false := by
    intro c q hq
    simp (disch := omega) only [sC, ite_eq_right]
  rw [hprod, Finset.card_product]
  rcases (show h = 1 ∨ 2 ≤ h by omega) with rfl | h2
  · have hR := bankCard hk start 1 raw last.val hlast hhk 1 1 0 le_rfl (by norm_num) le_rfl
      (by norm_num) (by norm_num) rc rt τR hτR (sR 1) hsR hsR0 0 1 rfl (by norm_num) (fun _ h => absurd h (by omega))
      (sR 1) (fun c i => by rw [Nat.zero_add]) J hJ
    have hC := bankCard hk start 1 raw last.val hlast hhk 2 3 4 (by norm_num) le_rfl (by norm_num)
      (by norm_num) (by norm_num) cc ct τC hτC (sC 1) hsC hsC0 0 1 rfl (by norm_num) (fun _ h => absurd h (by omega))
      (sC 1) (fun c i => by rw [Nat.zero_add]) J hJ
    rw [target_eq J _ true (by simp)]
    exact arith k 1 _ _ _ _ _ (by omega) hR hC (window1 J hJ _ _ _ _)
  · obtain ⟨m, rfl⟩ : ∃ m, h = m + 2 := ⟨h - 2, by omega⟩
    have hR := bankCard hk start (m+2) raw last.val hlast hhk 1 1 0 le_rfl (by norm_num) le_rfl
      (by norm_num) (by norm_num) rc rt τR hτR (sR (m+2)) hsR hsR0 m 2 rfl le_rfl (fun _ h => by omega)
      (sR 2) (sR_shift m 2) J hJ
    have hC := bankCard hk start (m+2) raw last.val hlast hhk 2 3 4 (by norm_num) le_rfl (by norm_num)
      (by norm_num) (by norm_num) cc ct τC hτC (sC (m+2)) hsC hsC0 m 2 rfl le_rfl (fun _ h => by omega)
      (sC 2) (sC_shift m 2) J hJ
    have hl : last.val = m + 1 := by omega
    have hrich : (m + 2 = 1 ∨ xor (rt last) (xor (raw (ix k hk (start + last.val)))
        (rc (ix k hk (start + last.val)))) = true) ↔ τR (m + 1) = true := by
      have hrt : extend rt (m + 1) = rt last := by
        simp only [extend, dite_eq_left (show m + 1 < m + 2 by omega)]
        exact congrArg rt (Fin.ext hl.symm)
      rw [hτR, hrt, hl, site hk start h5]
      simp
    rw [target_eq J _ (τR (m+1)) hrich]
    exact arith k (m+2) _ _ _ _ _ (by omega) hR hC (window2 J hJ _ _ _ _)

end PEqualNP.Outside.L_meta_33643

open PEqualNP.Outside.L_meta_33643 in
theorem PEqualNP.Outside.L_meta_33643 :
(
∀ (k h start : Nat) (hk : 0 < k), 0 < h → h+7 ≤ k →
  let W := Fin k → Bool
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let add := fun (x y : W) (p : Fin k) => xor (x p) (y p)
  let mix := fun (gap : Nat) (x : W) (p : Fin k) =>
    xor (xor (x (ix (p.val + k - gap % k))) (x p)) (x (ix (p.val + gap)))
  let step := fun (z : W) (p : Fin k) =>
    xor (z p) (!(z (ix (p.val+1))) && z (ix (p.val+2)))
  let rot := fun (s : Nat) (x : W) (p : Fin k) => x (ix (p.val + k - s % k))
  ∀ (rc cc raw : W) (rt ct : Fin h → Bool) (last : Fin h), last.val+1 = h →
    let endSite := start+last.val
    let key := fun (ab : Bool × Bool) (p : Fin k) =>
      if p = ix (endSite+1) then ab.1 else if p = ix (endSite+2) then ab.2 else raw p
    let read := fun (gap ini fin : Nat) (c name x : W) (j : Fin h) =>
      let p := ix (start+j.val)
      xor (step (mix gap (add (rot ini x) name)) p) (xor (rot fin x p) (c p))
    let full := 2^(2*(k-h))
    let rich := h = 1 ∨ xor (rt last) (xor (raw (ix endSite)) (rc (ix endSite))) = true
    ∀ J : Finset (Bool × Bool), J.Nonempty →
      let common := Finset.univ.filter (fun pair : W × W => ∀ corner ∈ J,
        read 1 1 0 rc pair.1 (key corner) = rt ∧ read 2 3 4 cc pair.2 (key corner) = ct)
      8*common.card =
        if J.card = 1 then 8*full else if J.card = 4 then 0
        else if (J.image Prod.fst).card = 1 then 4*full
        else if rich then (4-J.card)*full else 0
) := by
  intro k h start hk hh hhk W ix add mix step rot rc cc raw rt ct last hlast endSite key read full rich J hJ
    common
  exact main k h start hk hh hhk rc cc raw rt ct last hlast J hJ
