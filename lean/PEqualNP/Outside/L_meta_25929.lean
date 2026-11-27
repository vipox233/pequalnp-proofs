import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25929_aux

def run (n d : ℕ) (ask : Fin d → ℕ → ((Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2))) (x : Fin n → (ZMod 2)) : ℕ :=
  (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)

def Adm (h n : ℕ) (target : (Fin n → (ZMod 2)) → Bool → Fin h → (ZMod 2)) (d : ℕ) : Prop :=
  ∃ (ask : Fin d → ℕ → ((Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)))
    (readout : ℕ → Bool → Fin h → ((Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)))
    (bias : ℕ → Bool → Fin h → (ZMod 2)),
    ∀ x b i, target x b i = readout (run n d ask x) b i x + bias (run n d ask x) b i

theorem transfer {h n m d : ℕ} (T : (Fin n → (ZMod 2)) → Bool → Fin h → (ZMod 2))
    (L : (Fin m → (ZMod 2)) → Bool → Fin h → (ZMod 2))
    (N : (Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (Fin m → (ZMod 2))) (hs : Function.Surjective N)
    (hk : ∀ b i, ∃ (l : (Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) (c : (ZMod 2)), ∀ x, T x b i = L (N x) b i + l x + c) :
    Adm h n T d ↔ Adm h m L d := by
  choose lam kap hT using hk
  obtain ⟨M, hM⟩ := N.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hs)
  have hM' : ∀ y, N (M y) = y := fun y => LinearMap.congr_fun hM y
  constructor
  · rintro ⟨ask, ro, bias, hh⟩
    refine ⟨fun j t => (ask j t).comp M, fun t b i => (ro t b i).comp M - (lam b i).comp M,
      fun t b i => bias t b i - kap b i, ?_⟩
    intro y b i
    have e1 := hT b i (M y)
    rw [hM'] at e1
    have e2 := hh (M y) b i
    have hr : run m d (fun j t => (ask j t).comp M) y = run n d ask (M y) := rfl
    rw [hr]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    linear_combination e2 - e1
  · rintro ⟨ask, ro, bias, hh⟩
    refine ⟨fun j t => (ask j t).comp N, fun t b i => (ro t b i).comp N + lam b i,
      fun t b i => bias t b i + kap b i, ?_⟩
    intro x b i
    have hr : run n d (fun j t => (ask j t).comp N) x = run m d ask (N x) := rfl
    rw [hr, hT b i x, hh (N x) b i]
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    ring

def IsAff {n : ℕ} (f : (Fin n → (ZMod 2)) → (ZMod 2)) : Prop :=
  ∃ (l : (Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) (c : (ZMod 2)), ∀ x, f x = l x + c

theorem IsAff.coord {n : ℕ} (j : Fin n) : IsAff (fun x : Fin n → (ZMod 2) => x j) :=
  ⟨LinearMap.proj j, 0, fun x => by simp⟩

theorem IsAff.const {n : ℕ} (c : (ZMod 2)) : IsAff (fun _ : Fin n → (ZMod 2) => c) :=
  ⟨0, c, fun x => by simp⟩

theorem IsAff.add {n : ℕ} {f g : (Fin n → (ZMod 2)) → (ZMod 2)} (hf : IsAff f) (hg : IsAff g) :
    IsAff (fun x => f x + g x) := by
  obtain ⟨l1, c1, h1⟩ := hf
  obtain ⟨l2, c2, h2⟩ := hg
  exact ⟨l1 + l2, c1 + c2, fun x => by simp only [h1, h2, LinearMap.add_apply]; ring⟩

theorem IsAff.const_mul {n : ℕ} (c : (ZMod 2)) {f : (Fin n → (ZMod 2)) → (ZMod 2)} (hf : IsAff f) :
    IsAff (fun x => c * f x) := by
  obtain ⟨l1, c1, h1⟩ := hf
  exact ⟨c • l1, c * c1, fun x => by
    simp only [h1, LinearMap.smul_apply, smul_eq_mul]; ring⟩

theorem IsAff.mul_const {n : ℕ} (c : (ZMod 2)) {f : (Fin n → (ZMod 2)) → (ZMod 2)} (hf : IsAff f) :
    IsAff (fun x => f x * c) := by
  obtain ⟨l1, c1, h1⟩ := hf
  exact ⟨c • l1, c * c1, fun x => by
    simp only [h1, LinearMap.smul_apply, smul_eq_mul]; ring⟩

theorem IsAff.of_eq {n : ℕ} {f : (Fin n → (ZMod 2)) → (ZMod 2)} (g : (Fin n → (ZMod 2)) → (ZMod 2)) (hg : IsAff g)
    (h : ∀ x, f x = g x) : IsAff f := by
  obtain ⟨l, c, hl⟩ := hg
  exact ⟨l, c, fun x => by rw [h, hl]⟩

theorem aff_to_ex {n : ℕ} (f p : (Fin n → (ZMod 2)) → (ZMod 2)) (hA : IsAff (fun x => f x - p x)) :
    ∃ (l : (Fin n → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) (c : (ZMod 2)), ∀ x, f x = p x + l x + c := by
  obtain ⟨l, c, hl⟩ := hA
  exact ⟨l, c, fun x => by linear_combination hl x⟩

def ix (k : ℕ) (hk : 0 < k) (j : ℕ) : Fin k := ⟨j % k, Nat.mod_lt _ hk⟩

theorem ix_val_add (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    ix k hk ((ix k hk a).val + b) = ix k hk (a + b) := by
  apply Fin.ext
  simp [ix, Nat.mod_add_mod]

theorem ix_add_k (k : ℕ) (hk : 0 < k) (a : ℕ) : ix k hk (a + k) = ix k hk a := by
  apply Fin.ext
  simp [ix]

theorem ix_val_sub (k : ℕ) (hk : 0 < k) (a c : ℕ) (hc : c ≤ k) :
    ix k hk ((ix k hk a).val + k - c) = ix k hk (a + (k - c)) := by
  have : (ix k hk a).val + k - c = (ix k hk a).val + (k - c) := by omega
  rw [this, ix_val_add]

def rot (k : ℕ) (hk : 0 < k) (s : ℕ) (x : Fin k → (ZMod 2)) (i : Fin k) : (ZMod 2) :=
  x (ix k hk (i.val+k-s % k))
def mix (k : ℕ) (hk : 0 < k) (g : ℕ) (x : Fin k → (ZMod 2)) (i : Fin k) : (ZMod 2) :=
  x i + x (ix k hk (i.val+g)) + x (ix k hk (i.val+k-g % k))
def step (k : ℕ) (hk : 0 < k) (x : Fin k → (ZMod 2)) (i : Fin k) : (ZMod 2) :=
  x i + (1+x (ix k hk (i.val+1))) * x (ix k hk (i.val+2))

def Lin (k : ℕ) (hk : 0 < k) (g q : ℕ) (x : Fin k → (ZMod 2)) (a : ℕ) : (ZMod 2) :=
  x (ix k hk (a+(k-q))) + x (ix k hk (a+g+(k-q))) + x (ix k hk (a+(k-g)+(k-q)))
def Rr (k : ℕ) (hk : 0 < k) (g : ℕ) (r : Fin k → (ZMod 2)) (a : ℕ) : (ZMod 2) :=
  r (ix k hk a) + r (ix k hk (a+g)) + r (ix k hk (a+(k-g)))

theorem IsAff.lin (k : ℕ) (hk : 0 < k) (g q a : ℕ) :
    IsAff (fun x : Fin k → (ZMod 2) => Lin k hk g q x a) := by
  unfold Lin
  exact (IsAff.add (IsAff.add (IsAff.coord _) (IsAff.coord _)) (IsAff.coord _))

theorem rot_ix (k : ℕ) (hk : 0 < k) (q : ℕ) (hq : q < k) (x : Fin k → (ZMod 2)) (a : ℕ) :
    rot k hk q x (ix k hk a) = x (ix k hk (a + (k - q))) := by
  simp only [rot, Nat.mod_eq_of_lt hq, ix_val_sub k hk _ _ hq.le]

theorem mixrot (k : ℕ) (hk : 0 < k) (g q : ℕ) (hg : g < k) (hq : q < k)
    (x r : Fin k → (ZMod 2)) (a : ℕ) :
    mix k hk g (rot k hk q x + r) (ix k hk a) = Lin k hk g q x a + Rr k hk g r a := by
  simp only [mix, rot, Pi.add_apply, Nat.mod_eq_of_lt hg, Nat.mod_eq_of_lt hq, ix_val_add,
    ix_val_sub k hk _ _ hg.le, ix_val_sub k hk _ _ hq.le, Rr, Lin]
  ring

def Nmap (h k : ℕ) (hk : 0 < k) (start : ℕ) : (Fin k → (ZMod 2)) →ₗ[(ZMod 2)] (Fin (h+4) → (ZMod 2)) where
  toFun x j := x (ix k hk (start + j.val + (k-4))) + x (ix k hk (start + j.val + (k-4) + 1))
    + x (ix k hk (start + j.val + (k-4) + 2))
  map_add' x y := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c x := by
    funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def X (k : ℕ) (hk : 0 < k) (start i : ℕ) (x : Fin k → (ZMod 2)) (e : ℕ) : (ZMod 2) :=
  x (ix k hk (start + i + (k-4) + e))

theorem xX (k : ℕ) (hk : 0 < k) (start i : ℕ) (x : Fin k → (ZMod 2)) (a e : ℕ)
    (h : a = start + i + (k-4) + e ∨ a = start + i + (k-4) + e + k) :
    x (ix k hk a) = X k hk start i x e := by
  rcases h with h | h
  · rw [h]; rfl
  · rw [h, ix_add_k]; rfl

theorem NX (h k : ℕ) (hk : 0 < k) (start i : ℕ) (x : Fin k → (ZMod 2)) (e e1 e2 : ℕ)
    (h1 : e1 = e + 1) (h2 : e2 = e + 2) (hi : i + e < h + 4) :
    Nmap h k hk start x (Fin.ofNat (h+4) (i + e))
      = X k hk start i x e + X k hk start i x e1 + X k hk start i x e2 := by
  have hv : (Fin.ofNat (h+4) (i + e)).val = i + e := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hi]
  show x (ix k hk (start + (Fin.ofNat (h+4) (i + e)).val + (k-4)))
    + x (ix k hk (start + (Fin.ofNat (h+4) (i + e)).val + (k-4) + 1))
    + x (ix k hk (start + (Fin.ofNat (h+4) (i + e)).val + (k-4) + 2)) = _
  rw [hv]
  subst h1 h2
  have e0 : start + (i + e) + (k-4) = start + i + (k-4) + e := by omega
  rw [e0]
  rfl

theorem tlem (k r m : ℕ) (hr : r < k) (hm : m < k) : ((r+m)%k + (k-r))%k = m := by
  rcases Nat.lt_or_ge (r+m) k with h | h
  · rw [Nat.mod_eq_of_lt h]
    have : r+m+(k-r) = m + k := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
  · have h1 : (r+m)%k = r+m-k := by
      rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have : r+m-k+(k-r) = m := by omega
    rw [this, Nat.mod_eq_of_lt hm]

def useq (y : ℕ → (ZMod 2)) : ℕ → (ZMod 2)
  | 0 => 0
  | 1 => 0
  | (j+2) => y j + useq y j + useq y (j+1)

theorem two_add (a : (ZMod 2)) : a + a = 0 := by
  revert a; decide

theorem Nsurj (h k : ℕ) (hk : 0 < k) (hkh : h + 6 ≤ k) (start : ℕ) :
    Function.Surjective (Nmap h k hk start) := by
  intro y
  let yext : ℕ → (ZMod 2) := fun j => if hj : j < h+4 then y ⟨j, hj⟩ else 0
  let x : Fin k → (ZMod 2) := fun p => useq yext ((p.val + (k - (start + (k-4)) % k)) % k)
  have hx : ∀ m, m < k → ∀ a, a = start + (k-4) + m → x (ix k hk a) = useq yext m := by
    intro m hm a ha
    subst ha
    show useq yext (((start + (k-4) + m) % k + (k - (start + (k-4)) % k)) % k) = useq yext m
    congr 1
    rw [← Nat.mod_add_mod (start + (k-4)) k m]
    exact tlem k _ m (Nat.mod_lt _ hk) hm
  refine ⟨x, ?_⟩
  funext j
  have hj := j.isLt
  show x (ix k hk (start + j.val + (k-4))) + x (ix k hk (start + j.val + (k-4) + 1))
    + x (ix k hk (start + j.val + (k-4) + 2)) = y j
  rw [hx j.val (by omega) _ (by omega), hx (j.val+1) (by omega) _ (by omega),
    hx (j.val+2) (by omega) _ (by omega)]
  have hy : yext j.val = y j := by simp [yext, hj]
  show useq yext j.val + useq yext (j.val+1)
    + (yext j.val + useq yext j.val + useq yext (j.val+1)) = y j
  rw [hy]
  linear_combination two_add (useq yext j.val) + two_add (useq yext (j.val+1))

theorem keyF (h k : ℕ) (hk : 0 < k) (hkh : h + 6 ≤ k) (start : ℕ) (row c₁ : Fin k → (ZMod 2))
    (i : Fin h) :
    ∃ (l : (Fin k → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) (c : (ZMod 2)), ∀ x : Fin k → (ZMod 2),
      step k hk (mix k hk 1 (rot k hk 1 x + row)) (ix k hk (start + i.val))
        + x (ix k hk (start + i.val)) + c₁ (ix k hk (start + i.val))
      = Nmap h k hk start x (Fin.ofNat (h+4) (i.val+3))
          * Nmap h k hk start x (Fin.ofNat (h+4) (i.val+4)) + l x + c := by
  have hi := i.isLt
  apply aff_to_ex
  refine IsAff.of_eq (fun x => Lin k hk 1 1 x (start + i.val) + Rr k hk 1 row (start + i.val)
    + (1 + Rr k hk 1 row (start + i.val + 1)) * Lin k hk 1 1 x (start + i.val + 2)
    + Lin k hk 1 1 x (start + i.val + 1) * Rr k hk 1 row (start + i.val + 2)
    + (1 + Rr k hk 1 row (start + i.val + 1)) * Rr k hk 1 row (start + i.val + 2)
    + x (ix k hk (start + i.val)) + c₁ (ix k hk (start + i.val))) ?_ ?_
  · repeat (first
      | (exact IsAff.const _)
      | (exact IsAff.coord _)
      | (exact IsAff.lin _ _ _ _ _)
      | (apply IsAff.add)
      | (apply IsAff.const_mul)
      | (apply IsAff.mul_const))
  · intro x
    have hP : Lin k hk 1 1 x (start + i.val + 1)
        = Nmap h k hk start x (Fin.ofNat (h+4) (i.val+3)) := by
      rw [NX h k hk start i.val x 3 4 5 rfl rfl (by omega)]
      unfold Lin
      rw [xX k hk start i.val x _ 4 (by omega), xX k hk start i.val x _ 5 (by omega),
        xX k hk start i.val x _ 3 (by omega)]
      ring
    have hQ : Lin k hk 1 1 x (start + i.val + 2)
        = Nmap h k hk start x (Fin.ofNat (h+4) (i.val+4)) := by
      rw [NX h k hk start i.val x 4 5 6 rfl rfl (by omega)]
      unfold Lin
      rw [xX k hk start i.val x _ 5 (by omega), xX k hk start i.val x _ 6 (by omega),
        xX k hk start i.val x _ 4 (by omega)]
      ring
    simp only [step, ix_val_add, mixrot k hk 1 1 (by omega) (by omega)]
    rw [← hP, ← hQ]
    ring

theorem keyT (h k : ℕ) (hk : 0 < k) (hkh : h + 6 ≤ k) (start : ℕ) (col c₂ : Fin k → (ZMod 2))
    (i : Fin h) :
    ∃ (l : (Fin k → (ZMod 2)) →ₗ[(ZMod 2)] (ZMod 2)) (c : (ZMod 2)), ∀ x : Fin k → (ZMod 2),
      step k hk (mix k hk 2 (rot k hk 3 x + col)) (ix k hk (start + i.val))
        + rot k hk 4 x (ix k hk (start + i.val)) + c₂ (ix k hk (start + i.val))
      = (Nmap h k hk start x (Fin.ofNat (h+4) (i.val+0))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+1))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+2)))
        * (Nmap h k hk start x (Fin.ofNat (h+4) (i.val+1))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+2))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+3))) + l x + c := by
  have hi := i.isLt
  apply aff_to_ex
  refine IsAff.of_eq (fun x => Lin k hk 2 3 x (start + i.val) + Rr k hk 2 col (start + i.val)
    + (1 + Rr k hk 2 col (start + i.val + 1)) * Lin k hk 2 3 x (start + i.val + 2)
    + Lin k hk 2 3 x (start + i.val + 1) * Rr k hk 2 col (start + i.val + 2)
    + (1 + Rr k hk 2 col (start + i.val + 1)) * Rr k hk 2 col (start + i.val + 2)
    + x (ix k hk (start + i.val + (k - 4))) + c₂ (ix k hk (start + i.val))) ?_ ?_
  · repeat (first
      | (exact IsAff.const _)
      | (exact IsAff.coord _)
      | (exact IsAff.lin _ _ _ _ _)
      | (apply IsAff.add)
      | (apply IsAff.const_mul)
      | (apply IsAff.mul_const))
  · intro x
    have hP : Lin k hk 2 3 x (start + i.val + 1)
        = Nmap h k hk start x (Fin.ofNat (h+4) (i.val+0))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+1))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+2)) := by
      rw [NX h k hk start i.val x 0 1 2 rfl rfl (by omega),
        NX h k hk start i.val x 1 2 3 rfl rfl (by omega),
        NX h k hk start i.val x 2 3 4 rfl rfl (by omega)]
      unfold Lin
      rw [xX k hk start i.val x _ 2 (by omega), xX k hk start i.val x _ 4 (by omega),
        xX k hk start i.val x _ 0 (by omega)]
      linear_combination -(two_add (X k hk start i.val x 1))
        - two_add (X k hk start i.val x 2) - two_add (X k hk start i.val x 3)
    have hQ : Lin k hk 2 3 x (start + i.val + 2)
        = Nmap h k hk start x (Fin.ofNat (h+4) (i.val+1))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+2))
          + Nmap h k hk start x (Fin.ofNat (h+4) (i.val+3)) := by
      rw [NX h k hk start i.val x 1 2 3 rfl rfl (by omega),
        NX h k hk start i.val x 2 3 4 rfl rfl (by omega),
        NX h k hk start i.val x 3 4 5 rfl rfl (by omega)]
      unfold Lin
      rw [xX k hk start i.val x _ 3 (by omega), xX k hk start i.val x _ 5 (by omega),
        xX k hk start i.val x _ 1 (by omega)]
      linear_combination -(two_add (X k hk start i.val x 2))
        - two_add (X k hk start i.val x 3) - two_add (X k hk start i.val x 4)
    rw [rot_ix k hk 4 (by omega)]
    simp only [step, ix_val_add, mixrot k hk 2 3 (by omega) (by omega)]
    rw [← hP, ← hQ]
    ring

end PEqualNP.Outside.L_meta_25929_aux

theorem PEqualNP.Outside.L_meta_25929 : ∀ (h k : ℕ) (hk : 0 < k), h+6 ≤ k →
  let F := ZMod 2
  let admits := fun (n : ℕ) (target : (Fin n → F) → Bool → Fin h → F) (d : ℕ) =>
    let W := Fin n → F
    let D := W →ₗ[F] F
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun t j => 2*t + (if ask j t x = 0 then 0 else 1)) (0 : ℕ)
    ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin h → D)
      (bias : ℕ → Bool → Fin h → F),
      ∀ x b i, target x b i = readout (run ask x) b i x + bias (run ask x) b i
  let line := fun (y : Fin (h+4) → F) (b : Bool) (i : Fin h) =>
    let a := fun j : ℕ => y (Fin.ofNat (h+4) (i.val+j))
    if b then (a 0 + a 1 + a 2) * (a 1 + a 2 + a 3) else a 3 * a 4
  let W := Fin k → F
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val+g)) + x (ix (i.val+k-g % k))
  let step := fun (x : W) (i : Fin k) => x i + (1+x (ix (i.val+1))) * x (ix (i.val+2))
  ∀ (start d : ℕ) (row col c₁ c₂ : W),
    let target := fun (x : W) (b : Bool) (i : Fin h) =>
      let site := ix (start + i.val)
      if b then step (mix 2 (rot 3 x + col)) site + rot 4 x site + c₂ site
      else step (mix 1 (rot 1 x + row)) site + x site + c₁ site
    admits k target d ↔ admits (h+4) line d := by
  intro h k hk hkh F admits line W ix rot mix step start d row col c₁ c₂ target
  exact PEqualNP.Outside.L_meta_25929_aux.transfer target line
    (PEqualNP.Outside.L_meta_25929_aux.Nmap h k hk start)
    (PEqualNP.Outside.L_meta_25929_aux.Nsurj h k hk hkh start) (by
      intro b i
      cases b
      · exact PEqualNP.Outside.L_meta_25929_aux.keyF h k hk hkh start row c₁ i
      · exact PEqualNP.Outside.L_meta_25929_aux.keyT h k hk hkh start col c₂ i)
