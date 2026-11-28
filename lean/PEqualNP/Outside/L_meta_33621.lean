import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25883

namespace PEqualNP.Outside.L_meta_33621_aux

open PEqualNP.Outside.L_meta_25883_aux

def Hq (m0 m1 m2 y1 y2 : Bool) : Bool := xor m0 (xor (!y1 && y2) (!(xor y1 m1) && xor y2 m2))

theorem Hq_ff (b y1 y2 : Bool) : Hq b false false y1 y2 = b := by
  cases b <;> cases y1 <;> cases y2 <;> rfl

theorem tail3 : ∀ A1 A2 A3 A4 m0 m1 m2 m3 m4 dm cb : Bool,
    dm = xor (xor A2 (!A3 && A4)) cb →
    Hq m0 m1 m2 A1 A2 = false → Hq m1 m2 m3 A2 A3 = false → Hq m2 m3 m4 A3 A4 = false →
    Hq m0 m1 m2 (xor (xor dm cb) A1) (xor true A2) = false →
    Hq m1 m2 m3 (xor true A2) (xor true A3) = false →
    Hq m2 m3 m4 (xor true A3) (xor false A4) = false →
    m3 = false ∧ m4 = false := by decide

theorem tail2 : ∀ A1 A2 A3 m0 m1 m2 m3 : Bool,
    Hq m0 m1 m2 A1 A2 = false → Hq m1 m2 m3 A2 A3 = false →
    Hq m0 m1 m2 (xor true A1) (xor true A2) = false →
    Hq m1 m2 m3 (xor true A2) (xor false A3) = false →
    ¬ (A2 = true ∧ A3 = true) → ¬ (xor A2 m2 = true ∧ xor A3 m3 = true) →
    m2 = false ∧ m3 = false := by decide

theorem tail1 : ∀ A1 A2 m0 m1 m2 : Bool,
    Hq m0 m1 m2 A1 A2 = false → Hq m0 m1 m2 (xor true A1) (xor false A2) = false →
    A1 = false → xor A1 m1 = false → m1 = false ∧ m2 = false := by decide

theorem miss2 : ∀ r0 r1 D0 D1 D2 D3 : Bool, ∃ m0 m1 : Bool, ∀ Y0 Y1 Y2 Y3 : Bool,
    xor Y0 (!Y1 && Y2) = r0 → xor Y1 (!Y2 && Y3) = r1 →
    xor (xor Y0 D0) (!(xor Y1 D1) && xor Y2 D2) = m0 →
    xor (xor Y1 D1) (!(xor Y2 D2) && xor Y3 D3) = m1 → False := by decide

theorem xx (e L : Bool) : xor (xor e L) L = e := by cases e <;> cases L <;> rfl

theorem xmn (M W N : Bool) : xor (xor M W) (xor M N) = xor N W := by
  cases M <;> cases W <;> cases N <;> rfl

theorem xcancel {m e L : Bool} (h : xor m L = xor e L) : m = e := by
  revert h; cases m <;> cases e <;> cases L <;> decide

theorem missF (M N L K : ℕ → Bool) (ρ0 ρ1 : Bool) : ∃ m0 m1 : Bool, ∀ W : ℕ → Bool,
    ρ0 = xor (xor (xor (M 0) (W 0)) (!(xor (M 1) (W 1)) && xor (M 2) (W 2))) (L 0) →
    ρ1 = xor (xor (xor (M 1) (W 1)) (!(xor (M 2) (W 2)) && xor (M 3) (W 3))) (L 1) →
    m0 = xor (xor (xor (N 0) (W 0)) (!(xor (N 1) (W 1)) && xor (N 2) (W 2))) (K 0) →
    m1 = xor (xor (xor (N 1) (W 1)) (!(xor (N 2) (W 2)) && xor (N 3) (W 3))) (K 1) → False := by
  obtain ⟨n0, n1, hn⟩ := miss2 (xor ρ0 (L 0)) (xor ρ1 (L 1)) (xor (M 0) (N 0)) (xor (M 1) (N 1))
    (xor (M 2) (N 2)) (xor (M 3) (N 3))
  refine ⟨xor n0 (K 0), xor n1 (K 1), fun W a0 a1 b0 b1 =>
    hn (xor (M 0) (W 0)) (xor (M 1) (W 1)) (xor (M 2) (W 2)) (xor (M 3) (W 3)) ?_ ?_ ?_ ?_⟩
  · rw [a0, xx]
  · rw [a1, xx]
  · rw [xmn, xmn, xmn]; exact (xcancel b0).symm
  · rw [xmn, xmn, xmn]; exact (xcancel b1).symm

theorem cimg {α β : Type} [DecidableEq α] [DecidableEq β] (s : Finset ℕ) (f : ℕ → α) (g : ℕ → β)
    (h : ∀ u ∈ s, ∀ v ∈ s, g u = g v → f u = f v) : (s.image f).card ≤ (s.image g).card := by
  have e1 : (s.image (fun u => (g u, f u))).image Prod.snd = s.image f := Finset.image_image
  have e2 : (s.image (fun u => (g u, f u))).image Prod.fst = s.image g := Finset.image_image
  have inj : Set.InjOn Prod.fst ((s.image (fun u => (g u, f u)) : Finset (β × α)) : Set (β × α)) := by
    intro p hp q hq hpq
    rw [Finset.coe_image] at hp hq
    obtain ⟨u, hu, rfl⟩ := hp
    obtain ⟨v, hv, rfl⟩ := hq
    have h1 : g u = g v := hpq
    exact Prod.ext h1 (h u hu v hv h1)
  rw [← e1, ← e2, Finset.card_image_of_injOn inj]
  exact Finset.card_image_le

theorem imgF {β : Type} [DecidableEq β] (s : Finset ℕ) (f : ℕ → β) (p : β → Prop) [DecidablePred p] :
    (s.filter (fun u => p (f u))).image f = (s.image f).filter p := by
  ext b
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨u, ⟨hu, hp⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, hp⟩
  · rintro ⟨⟨u, hu, rfl⟩, hp⟩
    exact ⟨u, ⟨hu, hp⟩, rfl⟩

def resp (k d a start init last c u x : Nat) : Finset Nat :=
  (Finset.range a).filter (fun j => label k d start init last c u x j)

def prs (k d a start init last c x : Nat) (next : Finset Nat → Nat) (u : Nat) :
    Finset Nat × Finset Nat :=
  (resp k d a start init last c u x,
    resp k d a start init last c u (next (resp k d a start init last c u x)))

def tbl (k d a start init last c name : Nat) : Finset (Nat × Nat) :=
  ((Finset.range a).product (Finset.range (2^k))).filter
    (fun entry => label k d start init last c name entry.2 entry.1)

def enc (k d a start u : Nat) : Finset Nat :=
  (Finset.range (a+2)).filter (fun t => (mix k d u).testBit (site k start t))

def best (a : Nat) : Nat := if a = 1 then 4 else if a = 2 then 12 else 2^(a+2)

theorem base (k d a start init last c : Nat) (hd : 0 < d) (ha : 0 < a) (hk : a+2+2*d ≤ k) :
    ((Finset.range (2^k)).image (tbl k d a start init last c)).card = 2^(a+2) ∧
    ∀ u ∈ Finset.range (2^k), ∀ v ∈ Finset.range (2^k),
      (tbl k d a start init last c u = tbl k d a start init last c v ↔
        ∀ t < a+2, mixed k d start u v t = false) := by
  obtain ⟨h1, -, h3⟩ := PEqualNP.Outside.L_meta_25883 k d a start init last c hd ha hk
  exact ⟨h1, fun u hu v hv => (h3 u hu v hv).1⟩

theorem mem_resp {k d a start init last c u x j : Nat} (hj : j < a) :
    decide (j ∈ resp k d a start init last c u x) = label k d start init last c u x j := by
  simp [resp, hj]

theorem rot0 (k s : Nat) : rot k s 0 = 0 := by simp [rot]

theorem yx {k d u : Nat} (init start : Nat) (hd : 0 < d) (hdk : d < k) (hu : u < 2^k) (x t : Nat) :
    (mix k d (rot k init x ^^^ u)).testBit (site k start t)
      = xor ((mix k d (rot k init x)).testBit (site k start t)) ((mix k d u).testBit (site k start t)) :=
  mixLin hd hdk (site_lt (by omega) start t) (rot_lt _ _ _) hu

theorem rz {k d u : Nat} (init start t : Nat) :
    (mix k d (rot k init 0 ^^^ u)).testBit (site k start t) = (mix k d u).testBit (site k start t) := by
  rw [rot0, Nat.zero_xor]

theorem label0 {k d u : Nat} (start init last c j : Nat) :
    label k d start init last c u 0 j = xor (xor ((mix k d u).testBit (site k start j))
      (!((mix k d u).testBit (site k start (j+1))) && (mix k d u).testBit (site k start (j+2))))
      (c.testBit (site k start j)) := by
  unfold label
  rw [rot0, rot0, Nat.zero_xor, Nat.zero_testBit, Bool.false_xor]

theorem labelMW {k d u : Nat} (start init last c x j : Nat) (hd : 0 < d) (hdk : d < k)
    (hu : u < 2^k) :
    label k d start init last c u x j =
      xor (xor (xor ((mix k d (rot k init x)).testBit (site k start j))
          ((mix k d u).testBit (site k start j)))
        (!(xor ((mix k d (rot k init x)).testBit (site k start (j+1)))
            ((mix k d u).testBit (site k start (j+1)))) &&
          xor ((mix k d (rot k init x)).testBit (site k start (j+2)))
            ((mix k d u).testBit (site k start (j+2)))))
        (xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j))) := by
  unfold label
  rw [yx init start hd hdk hu x j, yx init start hd hdk hu x (j+1), yx init start hd hdk hu x (j+2)]

theorem eqs {k d a start init last c u v x : Nat} (hd : 0 < d) (hdk : d < k) (hu : u < 2^k)
    (hv : v < 2^k) (h : resp k d a start init last c u x = resp k d a start init last c v x) :
    ∀ j < a, Hq (mixed k d start u v j) (mixed k d start u v (j+1)) (mixed k d start u v (j+2))
      ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+1)))
      ((mix k d (rot k init x ^^^ u)).testBit (site k start (j+2))) = false := by
  intro j hj
  have hl : label k d start init last c u x j = label k d start init last c v x j := by
    rw [← mem_resp hj, ← mem_resp hj, h]
  exact Bool.eq_false_iff.mpr (fun h1 => (labelDiff start init last c x j hd hdk hu hv).mpr h1 hl)

theorem wv (k d start u v t : Nat) : (mix k d v).testBit (site k start t) =
    xor ((mix k d u).testBit (site k start t)) (mixed k d start u v t) := by
  unfold mixed
  generalize (mix k d u).testBit (site k start t) = A
  generalize (mix k d v).testBit (site k start t) = B
  cases A <;> cases B <;> rfl

theorem back (a : Nat) (m A : Nat → Bool)
    (H : ∀ j < a, Hq (m j) (m (j+1)) (m (j+2)) (A (j+1)) (A (j+2)) = false)
    (t1 : m a = false) (t2 : m (a+1) = false) : ∀ t < a+2, m t = false := by
  have key : ∀ n, (∀ t, a + 1 = t + n → m t = false) ∧ (∀ t, a + 1 = t + (n+1) → m t = false) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun t ht => ?_, fun t ht => ?_⟩
      · rw [show t = a + 1 by omega]; exact t2
      · rw [show t = a by omega]; exact t1
    | succ n ih =>
      refine ⟨ih.2, fun t ht => ?_⟩
      have h1 := ih.2 (t+1) (by omega)
      have h2 := ih.1 (t+2) (by omega)
      have h3 := H t (by omega)
      rw [h1, h2, Hq_ff] at h3
      exact h3
  intro t ht
  exact (key (a + 1 - t)).1 t (by omega)

theorem fwd {k d a start init : Nat} (hd : 0 < d) (hk : a+2+2*d ≤ k) (τ : ℕ → Bool) :
    ∀ n, n ≤ a+2 → ∃ x < 2^k, ∀ t < n,
      (mix k d (rot k init x)).testBit (site k start t) = τ t := by
  have hk0 : 0 < k := by omega
  have hdk : d < k := by omega
  intro n
  induction n with
  | zero => intro _; exact ⟨0, by positivity, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro hn
    obtain ⟨x, hx, hxt⟩ := ih (by omega)
    by_cases hb : (mix k d (rot k init x)).testBit (site k start n) = τ n
    · refine ⟨x, hx, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t n with h | h
      · exact hxt t h
      · rw [show t = n by omega]; exact hb
    · refine ⟨x ^^^ 2^(((site k start n + d) % k + k - init % k) % k),
        flip_lt hx (Nat.mod_lt _ hk0), ?_⟩
      intro t ht
      have e := keyFlip (d := d) (j := site k start t) (q := (site k start n + d) % k) (u := 0)
        init hd hdk (site_lt hk0 start t) (Nat.mod_lt _ hk0) hx (by positivity)
      rw [Nat.xor_zero, Nat.xor_zero] at e
      rw [e]
      rcases Nat.lt_or_ge t n with h | h
      · rw [indName' start hd hk (show n < a+2 by omega) h, hxt t h]
        simp
      · rw [show t = n by omega, indName start hd hk (show n < a+2 by omega)]
        cases hA : (mix k d (rot k init x)).testBit (site k start n) <;>
          cases hB : τ n <;> simp_all

theorem tailA (b : Nat) (m W M : Nat → Bool) (dm cb : Bool)
    (H1 : ∀ j < b+3, Hq (m j) (m (j+1)) (m (j+2)) (W (j+1)) (W (j+2)) = false)
    (H2 : ∀ j < b+3, Hq (m j) (m (j+1)) (m (j+2)) (xor (M (j+1)) (W (j+1)))
      (xor (M (j+2)) (W (j+2))) = false)
    (hl : dm = xor (xor (W (b+2)) (!(W (b+3)) && W (b+4))) cb)
    (M1 : M (b+1) = xor dm cb) (M2 : M (b+2) = true) (M3 : M (b+3) = true)
    (M4 : M (b+4) = false) :
    m (b+3) = false ∧ m (b+4) = false := by
  have e1 : Hq (m b) (m (b+1)) (m (b+2)) (W (b+1)) (W (b+2)) = false := H1 b (by omega)
  have e2 : Hq (m (b+1)) (m (b+2)) (m (b+3)) (W (b+2)) (W (b+3)) = false := H1 (b+1) (by omega)
  have e3 : Hq (m (b+2)) (m (b+3)) (m (b+4)) (W (b+3)) (W (b+4)) = false := H1 (b+2) (by omega)
  have f1 : Hq (m b) (m (b+1)) (m (b+2)) (xor (M (b+1)) (W (b+1))) (xor (M (b+2)) (W (b+2)))
      = false := H2 b (by omega)
  have f2 : Hq (m (b+1)) (m (b+2)) (m (b+3)) (xor (M (b+2)) (W (b+2))) (xor (M (b+3)) (W (b+3)))
      = false := H2 (b+1) (by omega)
  have f3 : Hq (m (b+2)) (m (b+3)) (m (b+4)) (xor (M (b+3)) (W (b+3))) (xor (M (b+4)) (W (b+4)))
      = false := H2 (b+2) (by omega)
  rw [M1, M2] at f1
  rw [M2, M3] at f2
  rw [M3, M4] at f3
  exact tail3 _ _ _ _ _ _ _ _ _ _ _ hl e1 e2 e3 f1 f2 f3

theorem tailB (m W M : Nat → Bool)
    (H1 : ∀ j < 2, Hq (m j) (m (j+1)) (m (j+2)) (W (j+1)) (W (j+2)) = false)
    (H2 : ∀ j < 2, Hq (m j) (m (j+1)) (m (j+2)) (xor (M (j+1)) (W (j+1)))
      (xor (M (j+2)) (W (j+2))) = false)
    (M1 : M 1 = true) (M2 : M 2 = true) (M3 : M 3 = false)
    (hU : ¬ (W 2 = true ∧ W 3 = true)) (hV : ¬ (xor (W 2) (m 2) = true ∧ xor (W 3) (m 3) = true)) :
    m 2 = false ∧ m 3 = false := by
  have e1 : Hq (m 0) (m 1) (m 2) (W 1) (W 2) = false := H1 0 (by omega)
  have e2 : Hq (m 1) (m 2) (m 3) (W 2) (W 3) = false := H1 1 (by omega)
  have f1 : Hq (m 0) (m 1) (m 2) (xor (M 1) (W 1)) (xor (M 2) (W 2)) = false := H2 0 (by omega)
  have f2 : Hq (m 1) (m 2) (m 3) (xor (M 2) (W 2)) (xor (M 3) (W 3)) = false := H2 1 (by omega)
  rw [M1, M2] at f1
  rw [M2, M3] at f2
  exact tail2 _ _ _ _ _ _ _ e1 e2 f1 f2 hU hV

theorem tailC (m W M : Nat → Bool)
    (H1 : ∀ j < 1, Hq (m j) (m (j+1)) (m (j+2)) (W (j+1)) (W (j+2)) = false)
    (H2 : ∀ j < 1, Hq (m j) (m (j+1)) (m (j+2)) (xor (M (j+1)) (W (j+1)))
      (xor (M (j+2)) (W (j+2))) = false)
    (M1 : M 1 = true) (M2 : M 2 = false)
    (hU : W 1 = false) (hV : xor (W 1) (m 1) = false) :
    m 1 = false ∧ m 2 = false := by
  have e1 : Hq (m 0) (m 1) (m 2) (W 1) (W 2) = false := H1 0 (by omega)
  have f1 : Hq (m 0) (m 1) (m 2) (xor (M 1) (W 1)) (xor (M 2) (W 2)) = false := H2 0 (by omega)
  rw [M1, M2] at f1
  exact tail1 _ _ _ _ _ e1 f1 hU hV

theorem inj3 {k d b start init last c y z u v : Nat} (hd : 0 < d) (hk : b+3+2+2*d ≤ k)
    (hu : u < 2^k) (hv : v < 2^k)
    (hyM : ∀ t < b+3+2, (mix k d (rot k init y)).testBit (site k start t) =
      if t = b+1 then xor true (c.testBit (site k start (b+2))) else if t = b+2 then true
      else if t = b+3 then true else false)
    (hzM : ∀ t < b+3+2, (mix k d (rot k init z)).testBit (site k start t) =
      if t = b+1 then xor false (c.testBit (site k start (b+2))) else if t = b+2 then true
      else if t = b+3 then true else false)
    (h : prs k d (b+3) start init last c 0 (fun r => if (b+3-1) ∈ r then y else z) u =
      prs k d (b+3) start init last c 0 (fun r => if (b+3-1) ∈ r then y else z) v) :
    ∀ t < b+3+2, mixed k d start u v t = false := by
  have hdk : d < k := by omega
  have h1 : resp k d (b+3) start init last c u 0 = resp k d (b+3) start init last c v 0 :=
    congrArg Prod.fst h
  have h2 : resp k d (b+3) start init last c u
        (if (b+3-1) ∈ resp k d (b+3) start init last c u 0 then y else z) =
      resp k d (b+3) start init last c v
        (if (b+3-1) ∈ resp k d (b+3) start init last c v 0 then y else z) :=
    congrArg Prod.snd h
  rw [← h1] at h2
  have H1 := eqs hd hdk hu hv h1
  simp only [rz init start] at H1
  have hl : decide ((b+3-1) ∈ resp k d (b+3) start init last c u 0) =
      xor (xor ((mix k d u).testBit (site k start (b+2)))
        (!((mix k d u).testBit (site k start (b+2+1))) && (mix k d u).testBit (site k start (b+2+2))))
        (c.testBit (site k start (b+2))) := by
    rw [show b+3-1 = b+2 by omega, mem_resp (show b+2 < b+3 by omega), label0]
  have tl : mixed k d start u v (b+3) = false ∧ mixed k d start u v (b+4) = false := by
    by_cases hmem : (b+3-1) ∈ resp k d (b+3) start init last c u 0
    · rw [if_pos hmem] at h2
      have H2 := eqs hd hdk hu hv h2
      simp only [yx init start hd hdk hu] at H2
      rw [decide_eq_true hmem] at hl
      exact tailA b (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t))
        (fun t => (mix k d (rot k init y)).testBit (site k start t)) true
        (c.testBit (site k start (b+2))) H1 H2 hl
        ((hyM (b+1) (by omega)).trans (if_pos rfl))
        ((hyM (b+2) (by omega)).trans ((if_neg (by omega)).trans (if_pos rfl)))
        ((hyM (b+3) (by omega)).trans ((if_neg (by omega)).trans ((if_neg (by omega)).trans
          (if_pos rfl))))
        ((hyM (b+4) (by omega)).trans ((if_neg (by omega)).trans ((if_neg (by omega)).trans
          (if_neg (by omega)))))
    · rw [if_neg hmem] at h2
      have H2 := eqs hd hdk hu hv h2
      simp only [yx init start hd hdk hu] at H2
      rw [decide_eq_false hmem] at hl
      exact tailA b (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t))
        (fun t => (mix k d (rot k init z)).testBit (site k start t)) false
        (c.testBit (site k start (b+2))) H1 H2 hl
        ((hzM (b+1) (by omega)).trans (if_pos rfl))
        ((hzM (b+2) (by omega)).trans ((if_neg (by omega)).trans (if_pos rfl)))
        ((hzM (b+3) (by omega)).trans ((if_neg (by omega)).trans ((if_neg (by omega)).trans
          (if_pos rfl))))
        ((hzM (b+4) (by omega)).trans ((if_neg (by omega)).trans ((if_neg (by omega)).trans
          (if_neg (by omega)))))
  exact back (b+3) (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t)) H1
    tl.1 tl.2

theorem inj2 {k d start init last c w u v : Nat} (hd : 0 < d) (hk : 2+2+2*d ≤ k)
    (hu : u < 2^k) (hv : v < 2^k)
    (hwM : ∀ t < 2+2, (mix k d (rot k init w)).testBit (site k start t) =
      if t = 1 then true else if t = 2 then true else false)
    (hU : ¬ ((mix k d u).testBit (site k start 2) = true ∧
      (mix k d u).testBit (site k start 3) = true))
    (hV : ¬ ((mix k d v).testBit (site k start 2) = true ∧
      (mix k d v).testBit (site k start 3) = true))
    (h : prs k d 2 start init last c 0 (fun r => if (2-1) ∈ r then w else w) u =
      prs k d 2 start init last c 0 (fun r => if (2-1) ∈ r then w else w) v) :
    ∀ t < 2+2, mixed k d start u v t = false := by
  have hdk : d < k := by omega
  have h1 : resp k d 2 start init last c u 0 = resp k d 2 start init last c v 0 :=
    congrArg Prod.fst h
  have h3 : resp k d 2 start init last c u
        (if (2-1) ∈ resp k d 2 start init last c u 0 then w else w) =
      resp k d 2 start init last c v
        (if (2-1) ∈ resp k d 2 start init last c v 0 then w else w) :=
    congrArg Prod.snd h
  simp only [ite_self] at h3
  have H1 := eqs hd hdk hu hv h1
  have H2 := eqs hd hdk hu hv h3
  simp only [rz init start] at H1
  simp only [yx init start hd hdk hu] at H2
  rw [wv k d start u v 2, wv k d start u v 3] at hV
  have tl := tailB (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t))
    (fun t => (mix k d (rot k init w)).testBit (site k start t)) H1 H2
    ((hwM 1 (by omega)).trans (if_pos rfl))
    ((hwM 2 (by omega)).trans ((if_neg (by omega)).trans (if_pos rfl)))
    ((hwM 3 (by omega)).trans ((if_neg (by omega)).trans (if_neg (by omega)))) hU hV
  exact back 2 (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t)) H1
    tl.1 tl.2

theorem inj1 {k d start init last c w u v : Nat} (hd : 0 < d) (hk : 1+2+2*d ≤ k)
    (hu : u < 2^k) (hv : v < 2^k)
    (hwM : ∀ t < 1+2, (mix k d (rot k init w)).testBit (site k start t) =
      if t = 1 then true else false)
    (hU : (mix k d u).testBit (site k start 1) = false)
    (hV : (mix k d v).testBit (site k start 1) = false)
    (h : prs k d 1 start init last c 0 (fun r => if (1-1) ∈ r then w else w) u =
      prs k d 1 start init last c 0 (fun r => if (1-1) ∈ r then w else w) v) :
    ∀ t < 1+2, mixed k d start u v t = false := by
  have hdk : d < k := by omega
  have h1 : resp k d 1 start init last c u 0 = resp k d 1 start init last c v 0 :=
    congrArg Prod.fst h
  have h3 : resp k d 1 start init last c u
        (if (1-1) ∈ resp k d 1 start init last c u 0 then w else w) =
      resp k d 1 start init last c v
        (if (1-1) ∈ resp k d 1 start init last c v 0 then w else w) :=
    congrArg Prod.snd h
  simp only [ite_self] at h3
  have H1 := eqs hd hdk hu hv h1
  have H2 := eqs hd hdk hu hv h3
  simp only [rz init start] at H1
  simp only [yx init start hd hdk hu] at H2
  rw [wv k d start u v 1] at hV
  have tl := tailC (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t))
    (fun t => (mix k d (rot k init w)).testBit (site k start t)) H1 H2
    ((hwM 1 (by omega)).trans (if_pos rfl))
    ((hwM 2 (by omega)).trans (if_neg (by omega))) hU hV
  exact back 1 (mixed k d start u v) (fun t => (mix k d u).testBit (site k start t)) H1
    tl.1 tl.2

theorem memE {k d a start u t : Nat} (ht : t < a+2) :
    t ∈ enc k d a start u ↔ (mix k d u).testBit (site k start t) = true := by
  simp [enc, ht]

theorem enc_eq {k d a start u v : Nat} (h : ∀ t < a+2, mixed k d start u v t = false) :
    enc k d a start u = enc k d a start v := by
  ext t
  by_cases ht : t < a+2
  · rw [memE ht, memE ht, wv k d start u v t, h t ht, Bool.xor_false]
  · simp [enc, ht]

theorem enc_surj {k d a start : Nat} (hd : 0 < d) (ha : 0 < a) (hk : a+2+2*d ≤ k) :
    (Finset.range (2^k)).image (enc k d a start) = (Finset.range (a+2)).powerset := by
  have hb := base k d a start 0 0 0 hd ha hk
  apply Finset.eq_of_subset_of_card_le
  · intro S hS
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  · rw [Finset.card_powerset, Finset.card_range, ← hb.1]
    apply cimg
    intro u hu v hv h
    apply (hb.2 u hu v hv).mpr
    intro t ht
    have e := Finset.ext_iff.mp h t
    rw [memE ht, memE ht] at e
    unfold mixed
    rw [Bool.eq_iff_iff.mpr e]
    simp

theorem resp_sub (k d a start init last c u x : Nat) :
    resp k d a start init last c u x ∈ (Finset.range a).powerset :=
  Finset.mem_powerset.mpr (Finset.filter_subset _ _)

theorem upper1 {k d start init last c x : Nat} (next : Finset ℕ → ℕ) :
    ((Finset.range (2^k)).image (prs k d 1 start init last c x next)).card ≤ 4 := by
  have sub : (Finset.range (2^k)).image (prs k d 1 start init last c x next) ⊆
      (Finset.range 1).powerset ×ˢ (Finset.range 1).powerset := by
    intro p hp
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨resp_sub k d 1 start init last c u x,
      resp_sub k d 1 start init last c u (next (resp k d 1 start init last c u x))⟩
  calc _ ≤ _ := Finset.card_le_card sub
    _ = 4 := by simp

theorem mem20 (B0 B1 : Bool) :
    decide (0 ∈ (Finset.range 2).filter (fun i => (if i = 0 then B0 else B1) = true)) = B0 := by
  cases B0 <;> cases B1 <;> decide

theorem mem21 (B0 B1 : Bool) :
    decide (1 ∈ (Finset.range 2).filter (fun i => (if i = 0 then B0 else B1) = true)) = B1 := by
  cases B0 <;> cases B1 <;> decide

theorem upper2 {k d start init last c x : Nat} (next : Finset ℕ → ℕ) (hd : 0 < d)
    (hk : 2+2+2*d ≤ k) (hx : x < 2^k) (hn : ∀ r, next r < 2^k) :
    ((Finset.range (2^k)).image (prs k d 2 start init last c x next)).card ≤ 12 := by
  have hdk : d < k := by omega
  have hmiss : ∀ ρ : Finset ℕ, ∃ μ ∈ (Finset.range 2).powerset, ∀ u < 2^k,
      resp k d 2 start init last c u x = ρ → resp k d 2 start init last c u (next ρ) ≠ μ := by
    intro ρ
    obtain ⟨m0, m1, hm⟩ := missF (fun t => (mix k d (rot k init x)).testBit (site k start t))
      (fun t => (mix k d (rot k init (next ρ))).testBit (site k start t))
      (fun j => xor ((rot k last x).testBit (site k start j)) (c.testBit (site k start j)))
      (fun j => xor ((rot k last (next ρ)).testBit (site k start j)) (c.testBit (site k start j)))
      (decide (0 ∈ ρ)) (decide (1 ∈ ρ))
    refine ⟨(Finset.range 2).filter (fun i => (if i = 0 then m0 else m1) = true),
      Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
    intro u hu hρ heq
    apply hm (fun t => (mix k d u).testBit (site k start t))
    · have e1 : decide (0 ∈ ρ) = label k d start init last c u x 0 := by
        rw [← hρ]; exact mem_resp (by decide)
      exact e1.trans (labelMW start init last c x 0 hd hdk hu)
    · have e1 : decide (1 ∈ ρ) = label k d start init last c u x 1 := by
        rw [← hρ]; exact mem_resp (by decide)
      exact e1.trans (labelMW start init last c x 1 hd hdk hu)
    · have e1 : decide (0 ∈ (Finset.range 2).filter (fun i => (if i = 0 then m0 else m1) = true)) =
          label k d start init last c u (next ρ) 0 := by
        rw [← heq]; exact mem_resp (by decide)
      exact ((mem20 m0 m1).symm.trans e1).trans (labelMW start init last c (next ρ) 0 hd hdk hu)
    · have e1 : decide (1 ∈ (Finset.range 2).filter (fun i => (if i = 0 then m0 else m1) = true)) =
          label k d start init last c u (next ρ) 1 := by
        rw [← heq]; exact mem_resp (by decide)
      exact ((mem21 m0 m1).symm.trans e1).trans (labelMW start init last c (next ρ) 1 hd hdk hu)
  have hmiss' : ∃ μ : Finset ℕ → Finset ℕ, ∀ ρ, μ ρ ∈ (Finset.range 2).powerset ∧ ∀ u < 2^k,
      resp k d 2 start init last c u x = ρ → resp k d 2 start init last c u (next ρ) ≠ μ ρ :=
    ⟨fun ρ => Classical.choose (hmiss ρ), fun ρ => Classical.choose_spec (hmiss ρ)⟩
  obtain ⟨μ, hμ⟩ := hmiss'
  have sub : (Finset.range (2^k)).image (prs k d 2 start init last c x next) ⊆
      ((Finset.range 2).powerset).biUnion
        (fun ρ => (((Finset.range 2).powerset).erase (μ ρ)).image (fun r => (ρ, r))) := by
    intro p hp
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_biUnion.mpr ⟨resp k d 2 start init last c u x,
      resp_sub k d 2 start init last c u x, ?_⟩
    refine Finset.mem_image.mpr ⟨resp k d 2 start init last c u
      (next (resp k d 2 start init last c u x)), ?_, rfl⟩
    exact Finset.mem_erase.mpr ⟨(hμ _).2 u (Finset.mem_range.mp hu) rfl,
      resp_sub k d 2 start init last c u (next (resp k d 2 start init last c u x))⟩
  calc ((Finset.range (2^k)).image (prs k d 2 start init last c x next)).card
      ≤ (((Finset.range 2).powerset).biUnion
        (fun ρ => (((Finset.range 2).powerset).erase (μ ρ)).image (fun r => (ρ, r)))).card :=
        Finset.card_le_card sub
    _ ≤ Finset.sum (Finset.range 2).powerset
        (fun ρ => ((((Finset.range 2).powerset).erase (μ ρ)).image (fun r => (ρ, r))).card) :=
        Finset.card_biUnion_le
    _ ≤ Finset.sum (Finset.range 2).powerset (fun _ => 3) := by
        apply Finset.sum_le_sum
        intro ρ _
        calc _ ≤ (((Finset.range 2).powerset).erase (μ ρ)).card := Finset.card_image_le
          _ = 3 := by rw [Finset.card_erase_of_mem (hμ ρ).1]; simp
    _ = 12 := by simp

theorem resp_tbl {k d a start init last c u v : Nat}
    (h : tbl k d a start init last c u = tbl k d a start init last c v) {x : Nat} (hx : x < 2^k) :
    resp k d a start init last c u x = resp k d a start init last c v x := by
  ext j
  simp only [resp, Finset.mem_filter, Finset.mem_range]
  have m := Finset.ext_iff.mp h (j, x)
  simp only [tbl, Finset.mem_filter] at m
  constructor
  · rintro ⟨hj, hl⟩
    exact ⟨hj, (m.mp ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hx⟩,
      hl⟩).2⟩
  · rintro ⟨hj, hl⟩
    exact ⟨hj, (m.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hx⟩,
      hl⟩).2⟩

theorem upper3 {k d a start init last c x : Nat} (next : Finset ℕ → ℕ) (hd : 0 < d) (ha : 0 < a)
    (hk : a+2+2*d ≤ k) (hx : x < 2^k) (hn : ∀ r, next r < 2^k) :
    ((Finset.range (2^k)).image (prs k d a start init last c x next)).card ≤ 2^(a+2) := by
  rw [← (base k d a start init last c hd ha hk).1]
  apply cimg
  intro u _ v _ h
  have e : ∀ x' < 2^k, resp k d a start init last c u x' = resp k d a start init last c v x' :=
    fun x' hx' => resp_tbl h hx'
  unfold prs
  rw [e x hx, e _ (hn _)]

theorem upper {k d a start init last c x : Nat} (next : Finset ℕ → ℕ) (hd : 0 < d) (ha : 0 < a)
    (hk : a+2+2*d ≤ k) (hx : x < 2^k) (hn : ∀ r, next r < 2^k) :
    ((Finset.range (2^k)).image (prs k d a start init last c x next)).card ≤ best a := by
  unfold best
  split_ifs with h1 h2
  · subst h1; exact upper1 next
  · subst h2; exact upper2 next hd hk hx hn
  · exact upper3 next hd ha hk hx hn

theorem lower {k d a start init last c : Nat} (hd : 0 < d) (ha : 0 < a) (hk : a+2+2*d ≤ k) :
    ∃ y ∈ Finset.range (2^k), ∃ z ∈ Finset.range (2^k),
      ((Finset.range (2^k)).image
        (prs k d a start init last c 0 (fun r => if (a-1) ∈ r then y else z))).card = best a := by
  have up : ∀ y z, y < 2^k → z < 2^k → ((Finset.range (2^k)).image
      (prs k d a start init last c 0 (fun r => if (a-1) ∈ r then y else z))).card ≤ best a := by
    intro y z hy hz
    exact upper _ hd ha hk (by positivity) (fun r => by
      show (if (a-1) ∈ r then y else z) < 2^k
      split_ifs <;> assumption)
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with h1 | h2 | h3
  · subst h1
    obtain ⟨w, hw, hwM⟩ := fwd (a := 1) (start := start) (init := init) hd hk
      (fun t => if t = 1 then true else false) (1+2) le_rfl
    refine ⟨w, Finset.mem_range.mpr hw, w, Finset.mem_range.mpr hw, le_antisymm (up w w hw hw) ?_⟩
    have hb1 : best 1 = 4 := rfl
    rw [hb1]
    have hUE : ((Finset.range (2^k)).filter (fun u => ¬ (1 ∈ enc k d 1 start u))).image
        (enc k d 1 start) = ((Finset.range (1+2)).powerset).filter (fun S => ¬ (1 ∈ S)) := by
      rw [← enc_surj hd ha hk]
      exact imgF _ _ (fun S : Finset ℕ => ¬ (1 ∈ S))
    have hc : (((Finset.range (1+2)).powerset).filter (fun S => ¬ (1 ∈ S))).card = 4 := by
      decide
    calc 4 = (((Finset.range (2^k)).filter (fun u => ¬ (1 ∈ enc k d 1 start u))).image
          (enc k d 1 start)).card := by rw [hUE, hc]
      _ ≤ (((Finset.range (2^k)).filter (fun u => ¬ (1 ∈ enc k d 1 start u))).image
          (prs k d 1 start init last c 0 (fun r => if (1-1) ∈ r then w else w))).card := by
          apply cimg
          intro u hu v hv h
          have hu' := Finset.mem_filter.mp hu
          have hv' := Finset.mem_filter.mp hv
          rw [memE (u := u) (show 1 < 1+2 by omega)] at hu'
          rw [memE (u := v) (show 1 < 1+2 by omega)] at hv'
          exact enc_eq (inj1 hd hk (Finset.mem_range.mp hu'.1) (Finset.mem_range.mp hv'.1) hwM
            (Bool.eq_false_iff.mpr hu'.2) (Bool.eq_false_iff.mpr hv'.2) h)
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  · subst h2
    obtain ⟨w, hw, hwM⟩ := fwd (a := 2) (start := start) (init := init) hd hk
      (fun t => if t = 1 then true else if t = 2 then true else false) (2+2) le_rfl
    refine ⟨w, Finset.mem_range.mpr hw, w, Finset.mem_range.mpr hw, le_antisymm (up w w hw hw) ?_⟩
    have hb2 : best 2 = 12 := rfl
    rw [hb2]
    have hUE : ((Finset.range (2^k)).filter
        (fun u => ¬ (2 ∈ enc k d 2 start u ∧ 3 ∈ enc k d 2 start u))).image (enc k d 2 start)
        = ((Finset.range (2+2)).powerset).filter (fun S => ¬ (2 ∈ S ∧ 3 ∈ S)) := by
      rw [← enc_surj hd ha hk]
      exact imgF _ _ (fun S : Finset ℕ => ¬ (2 ∈ S ∧ 3 ∈ S))
    have hc : (((Finset.range (2+2)).powerset).filter (fun S => ¬ (2 ∈ S ∧ 3 ∈ S))).card = 12 := by
      decide
    calc 12 = (((Finset.range (2^k)).filter
          (fun u => ¬ (2 ∈ enc k d 2 start u ∧ 3 ∈ enc k d 2 start u))).image
          (enc k d 2 start)).card := by rw [hUE, hc]
      _ ≤ (((Finset.range (2^k)).filter
          (fun u => ¬ (2 ∈ enc k d 2 start u ∧ 3 ∈ enc k d 2 start u))).image
          (prs k d 2 start init last c 0 (fun r => if (2-1) ∈ r then w else w))).card := by
          apply cimg
          intro u hu v hv h
          have hu' := Finset.mem_filter.mp hu
          have hv' := Finset.mem_filter.mp hv
          rw [memE (u := u) (show 2 < 2+2 by omega), memE (u := u) (show 3 < 2+2 by omega)] at hu'
          rw [memE (u := v) (show 2 < 2+2 by omega), memE (u := v) (show 3 < 2+2 by omega)] at hv'
          exact enc_eq (inj2 hd hk (Finset.mem_range.mp hu'.1) (Finset.mem_range.mp hv'.1) hwM
            hu'.2 hv'.2 h)
      _ ≤ _ := Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
  · obtain ⟨b, rfl⟩ : ∃ b, a = b + 3 := ⟨a - 3, by omega⟩
    obtain ⟨y, hy, hyM⟩ := fwd (a := b+3) (start := start) (init := init) hd hk
      (fun t => if t = b+1 then xor true (c.testBit (site k start (b+2))) else if t = b+2 then true
        else if t = b+3 then true else false) (b+3+2) le_rfl
    obtain ⟨z, hz, hzM⟩ := fwd (a := b+3) (start := start) (init := init) hd hk
      (fun t => if t = b+1 then xor false (c.testBit (site k start (b+2))) else if t = b+2 then true
        else if t = b+3 then true else false) (b+3+2) le_rfl
    refine ⟨y, Finset.mem_range.mpr hy, z, Finset.mem_range.mpr hz, le_antisymm (up y z hy hz) ?_⟩
    have hb3 : best (b+3) = 2^(b+3+2) := by
      unfold best
      rw [if_neg (show b+3 ≠ 1 by omega), if_neg (show b+3 ≠ 2 by omega)]
    rw [hb3, ← (base k d (b+3) start init last c hd ha hk).1]
    apply cimg
    intro u hu v hv h
    exact ((base k d (b+3) start init last c hd ha hk).2 u hu v hv).mpr
      (inj3 hd hk (Finset.mem_range.mp hu) (Finset.mem_range.mp hv) hyM hzM h)

theorem main {k d a start init last c : Nat} (hd : 0 < d) (ha : 0 < a) (hk : a+2+2*d ≤ k) :
    (∀ x ∈ Finset.range (2^k), ∀ next : Finset Nat → Nat, (∀ r, next r ∈ Finset.range (2^k)) →
      ((Finset.range (2^k)).image (prs k d a start init last c x next)).card ≤ best a) ∧
    ∃ y ∈ Finset.range (2^k), ∃ z ∈ Finset.range (2^k),
      ((Finset.range (2^k)).image
        (prs k d a start init last c 0 (fun r => if (a-1) ∈ r then y else z))).card = best a :=
  ⟨fun x hx next hn => upper next hd ha hk (Finset.mem_range.mp hx)
    (fun r => Finset.mem_range.mp (hn r)), lower hd ha hk⟩

end PEqualNP.Outside.L_meta_33621_aux

theorem PEqualNP.Outside.L_meta_33621 : ∀ (k d a start init last c : Nat), 0 < d → 0 < a → a + 2 + 2*d ≤ k →
  let words := Finset.range (2^k)
  let rot := fun (s z : Nat) =>
    ((z <<< (s % k)) ||| (z >>> (k - s % k))) % 2^k
  let mix := fun z : Nat => z ^^^ rot d z ^^^ rot (k-d) z
  let site := fun j : Nat => (start+j) % k
  let label := fun (u x j : Nat) =>
    let y := mix (rot init x ^^^ u)
    xor (xor (y.testBit (site j))
      (!(y.testBit (site (j+1))) && y.testBit (site (j+2))))
      (xor ((rot last x).testBit (site j)) (c.testBit (site j)))
  let response := fun (u x : Nat) => (Finset.range a).filter (fun j => label u x j)
  let count := fun (x : Nat) (next : Finset Nat → Nat) =>
    (words.image (fun u =>
      let r := response u x
      (r, response u (next r)))).card
  let best := if a = 1 then 4 else if a = 2 then 12 else 2^(a+2)
  (∀ x ∈ words, ∀ next : Finset Nat → Nat,
    (∀ r, next r ∈ words) → count x next ≤ best) ∧
  ∃ y ∈ words, ∃ z ∈ words,
    count 0 (fun r => if (a-1) ∈ r then y else z) = best := by
  intro k d a start init last c hd ha hk
  exact PEqualNP.Outside.L_meta_33621_aux.main (start := start) (init := init) (last := last)
    (c := c) hd ha hk
