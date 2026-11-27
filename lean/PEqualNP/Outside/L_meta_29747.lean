import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29747_aux

private abbrev F := ZMod 2

-- Cyclic indexing and the period-three kernel argument are adapted from
-- PEqualNP.Outside.L_meta_25737_aux.mixLin_injective in L-meta-25737, submission 39443.
private lemma z2_add_self (a : F) : a + a = 0 := by revert a; decide

private lemma z2_add_eq_zero_iff (a b : F) : a + b = 0 ↔ a = b := by revert a b; decide

private lemma z2_three_eq (a b c d : F) (h1 : a + b + c = 0) (h2 : b + d + a = 0) : d = c := by
  revert a b c d h1 h2; decide

private lemma vec_add_self {n : ℕ} (u : Fin n → F) : u + u = 0 :=
  funext fun i => z2_add_self (u i)

private def ix (k : ℕ) (hk : 0 < k) (z : ℕ) : Fin k := ⟨z % k, Nat.mod_lt _ hk⟩

private lemma ix_val_eq (k : ℕ) (hk : 0 < k) (i : Fin k) : ix k hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

private lemma ix_add_ix (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    ix k hk ((ix k hk a).val + b) = ix k hk (a + b) :=
  Fin.ext (by simp [ix, Nat.add_mod])

private lemma ix_add_mul_k (k : ℕ) (hk : 0 < k) (a m : ℕ) :
    ix k hk (a + m * k) = ix k hk a :=
  Fin.ext (by simp [ix, Nat.add_mul_mod_self_right])

private lemma ix_sub_add (k : ℕ) (hk : 0 < k) (i : Fin k) (r : ℕ) :
    ix k hk ((ix k hk (i.val + k - r % k)).val + r) = i := by
  rw [ix_add_ix]
  have hr : r % k < k := Nat.mod_lt r hk
  have hdiv : k * (r / k) + r % k = r := Nat.div_add_mod r k
  have heq : i.val + k - r % k + r = i.val + (1 + r / k) * k := by
    rw [Nat.add_mul, one_mul, mul_comm (r / k) k]
    omega
  rw [heq, ix_add_mul_k, ix_val_eq]

private lemma ix_add_sub (k : ℕ) (hk : 0 < k) (i : Fin k) (r : ℕ) :
    ix k hk ((ix k hk (i.val + r)).val + k - r % k) = i := by
  apply Fin.ext
  dsimp [ix]
  have hi : i.val < k := i.isLt
  have hr : r % k < k := Nat.mod_lt r hk
  have hmod : (i.val + r) % k = (i.val + r % k) % k := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hi]
  rw [hmod]
  by_cases hlt : i.val + r % k < k
  · rw [Nat.mod_eq_of_lt hlt]
    have h1 : i.val + r % k + k - r % k = i.val + 1 * k := by omega
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  · have h2 : (i.val + r % k) % k = i.val + r % k - k := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h2]
    have h3 : i.val + r % k - k + k - r % k = i.val := by omega
    rw [h3, Nat.mod_eq_of_lt hi]

private def mixLin (k : ℕ) (hk : 0 < k) (spacing : ℕ) : (Fin k → F) →ₗ[F] (Fin k → F) where
  toFun z j := z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k))
  map_add' x y := by funext j; simp only [Pi.add_apply]; ring
  map_smul' c x := by funext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma mixLin_ker_zero (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ)
    (z : Fin k → F) (hz : mixLin k hk spacing z = 0) : z = 0 := by
  have hval : ∀ j : Fin k,
      z j + z (ix k hk (j.val + spacing)) + z (ix k hk (j.val + k - spacing % k)) = 0 :=
    fun j => congrFun hz j
  have hper3 : ∀ j : Fin k, z (ix k hk (j.val + 3 * spacing)) = z j := by
    intro j
    let j1 := ix k hk (j.val + spacing)
    let j2 := ix k hk (j.val + 2 * spacing)
    have h1 := hval j1
    have hj1_next : ix k hk (j1.val + spacing) = j2 := by
      dsimp [j1, j2]; rw [ix_add_ix]; congr 1; omega
    have hj1_prev : ix k hk (j1.val + k - spacing % k) = j := ix_add_sub k hk j spacing
    rw [hj1_next, hj1_prev] at h1
    have h2 := hval j2
    have hj2_next : ix k hk (j2.val + spacing) = ix k hk (j.val + 3 * spacing) := by
      dsimp [j2]; rw [ix_add_ix]; congr 1; omega
    have hj2_prev : ix k hk (j2.val + k - spacing % k) = j1 := by
      rw [← hj1_next]; exact ix_add_sub k hk j1 spacing
    rw [hj2_next, hj2_prev] at h2
    exact z2_three_eq (z j1) (z j2) (z j) (z (ix k hk (j.val + 3 * spacing))) h1 h2
  have hperm : ∀ (m : ℕ) (j : Fin k), z (ix k hk (j.val + 3 * m * spacing)) = z j := by
    intro m
    induction m with
    | zero => intro j; simp [ix_val_eq]
    | succ m ih =>
      intro j
      have heq : j.val + 3 * (m + 1) * spacing = (j.val + 3 * m * spacing) + 3 * spacing := by ring
      rw [heq, ← ix_add_ix, hper3, ih]
  have hper1 : ∀ j : Fin k, z (ix k hk (j.val + spacing)) = z j := by
    intro j
    have hmod3 : k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hmod3 with h31 | h32
    · have hm := hperm (k / 3) (ix k hk (j.val + spacing))
      rw [ix_add_ix] at hm
      have heq : j.val + spacing + 3 * (k / 3) * spacing = j.val + spacing * k := by
        have hk' : 3 * (k / 3) + 1 = k := by omega
        calc j.val + spacing + 3 * (k / 3) * spacing
            = j.val + spacing * (3 * (k / 3) + 1) := by ring
          _ = j.val + spacing * k := by rw [hk']
      rw [heq, ix_add_mul_k, ix_val_eq] at hm
      exact hm.symm
    · have hm := hperm (k / 3 + 1) j
      have heq : j.val + 3 * (k / 3 + 1) * spacing = (j.val + spacing) + spacing * k := by
        have hk' : 3 * (k / 3 + 1) = k + 1 := by omega
        calc j.val + 3 * (k / 3 + 1) * spacing
            = j.val + (k + 1) * spacing := by rw [hk']
          _ = (j.val + spacing) + spacing * k := by ring
      rw [heq, ix_add_mul_k] at hm
      exact hm
  funext j
  have hprev : z (ix k hk (j.val + k - spacing % k)) = z j := by
    have hp := hper1 (ix k hk (j.val + k - spacing % k))
    rw [ix_sub_add] at hp
    exact hp.symm
  have hj := hval j
  rw [hper1 j, hprev, z2_add_self, zero_add] at hj
  exact hj

private lemma mixLin_injective (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) (spacing : ℕ) :
    Function.Injective (mixLin k hk spacing) := by
  intro x y h
  have h0 : mixLin k hk spacing (x + y) = 0 := by rw [map_add, h, vec_add_self]
  have hxy : x + y = 0 := mixLin_ker_zero k hk hk3 spacing (x + y) h0
  funext i
  exact (z2_add_eq_zero_iff (x i) (y i)).1 (congrFun hxy i)

private theorem mix_surjective (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0) :
    Function.Surjective (fun (x : Fin k → ZMod 2) (i : Fin k) =>
      x i + x (ix k hk (i.val + 2)) + x (ix k hk (i.val + k - 2 % k))) :=
  Finite.surjective_of_injective (mixLin_injective k hk hk3 2)

private theorem starting_mix_surjective (k : ℕ) (hk : 0 < k) (hk3 : k % 3 ≠ 0)
    (left : Fin k → ZMod 2) :
    let W := Fin k → ZMod 2
    let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-(s % k)))
    let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val+2)) + rot 2 x i
    Function.Surjective (fun name => mix (rot 3 left + name)) := by
  dsimp only
  intro y
  obtain ⟨x, hx⟩ := mix_surjective k hk hk3 y
  let offset : Fin k → ZMod 2 := fun i => left (ix k hk (i.val + k - 3 % k))
  refine ⟨x - offset, ?_⟩
  change mixLin k hk 2 (offset + (x - offset)) = y
  rw [add_comm offset, sub_add_cancel]
  exact hx

private def gate (a b c : F) : F := a + (1+b)*c

private def response (x : Fin 7 → F) (m b1 b2 : F) : F :=
  let u0 := gate (x 0) (x 1) (x 2)
  let u1 := gate (x 1) (x 2) (x 3)
  let u2 := gate (x 2) (x 3) (x 4)
  let u3 := gate (x 3) (x 4) (x 5)
  let u4 := gate (x 4) (x 5) (x 6)
  u0 + u2 + (1+m)*x 0 + (1 + u1 + u3 + m + (1+x 0)*x 1 + b1) * (u2 + u4 + u0 + b2)

private def localDiff (e : Fin 7 → F) (m dm b1 b2 : F) (x : Fin 7 → F) : F :=
  response (x + e) (m+dm) (b1+e 0) (b2+e 1) - response x m b1 b2

private def cube (f : (Fin 7 → F) → F) (x : F → F → F → Fin 7 → F) : F :=
  f (x 1 1 1) - f (x 1 1 0) - f (x 1 0 1) - f (x 0 1 1) +
  f (x 1 0 0) + f (x 0 1 0) + f (x 0 0 1) - f (x 0 0 0)

-- Each cube selects a triple belonging to just one quartic support.
private def probes (i : Fin 7) : F → F → F → Fin 7 → F :=
  ![fun a b c => ![0, a, 0, b, c, 0, 0],
    fun a b c => ![a, 0, 0, b, c, 0, 0],
    fun a b c => ![0, 0, 0, a, 0, b, c],
    fun a b c => ![a, b, 0, 0, c, 0, 0],
    fun a b c => ![a, b, 0, c, 0, 0, 0],
    fun a b c => ![a, b, 0, 0, 0, 0, c],
    fun a b c => ![a, b, 0, 0, 0, c, 0]] i

set_option maxHeartbeats 1600000 in
private theorem cube_coefficient (e : Fin 7 → F) (w dm b1 b2 : F) (i : Fin 7) :
    cube (fun x => localDiff e (w * x 6) dm b1 b2 x) (probes i) = e i := by
  fin_cases i <;> simp [probes, cube, localDiff, response, gate, Pi.add_apply, Matrix.cons_val] <;> ring

private theorem cube_const (f : (Fin 7 → F) → F) (c : F)
    (h : ∀ x, f x = c) (x : F → F → F → Fin 7 → F) : cube f x = 0 := by
  simp only [cube, h]
  ring

private theorem localDiff_zero (m b1 b2 : F) (x : Fin 7 → F) :
    localDiff 0 m 0 b1 b2 x = 0 := by
  simp [localDiff]

private theorem diff_constant_iff (e : Fin 7 → F) (w dm b1 b2 c : F) :
    (∀ x, localDiff e (w * x 6) dm b1 b2 x = c) ↔ e = 0 ∧ dm = 0 ∧ c = 0 := by
  constructor
  · intro h
    have he : e = 0 := funext fun i =>
      (cube_coefficient e w dm b1 b2 i).symm.trans (cube_const _ _ h (probes i))
    subst e
    let x : Fin 7 → F := ![0, 0, 0, 0, 0, 0, 1]
    have hchange : localDiff 0 (w * x 6) dm b1 b2 x -
        localDiff 0 (w * (0 : Fin 7 → F) 6) dm b1 b2 0 = dm := by
      simp [x, localDiff, response, gate, Matrix.cons_val]
      ring
    have hdm : dm = 0 := hchange.symm.trans (by rw [h x, h 0, sub_self])
    subst dm
    exact ⟨rfl, rfl, (h 0).symm.trans (localDiff_zero _ _ _ _)⟩
  · rintro ⟨rfl, rfl, rfl⟩ x
    exact localDiff_zero _ _ _ _

private abbrev Word (k : ℕ) := Fin k → F

private def idx {k : ℕ} (hk : 0 < k) (base t : ℕ) : Fin k :=
  ix k hk (base + t)

private def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word k) (i : Fin k) : F :=
  x (ix k hk (i.val + k - s % k))

private lemma idx_add {k : ℕ} (hk : 0 < k) (base t s : ℕ) :
    ix k hk ((idx hk base t).val + s) = idx hk base (t+s) := by
  unfold idx
  rw [ix_add_ix, Nat.add_assoc]

private lemma rotate_idx {k : ℕ} (hk : 0 < k) (base s t : ℕ) (x : Word k) :
    rotate hk s x (idx hk base (t+s)) = x (idx hk base t) := by
  unfold rotate
  rw [← idx_add, ix_add_sub]

private lemma mix_idx {k : ℕ} (hk : 0 < k) (base t : ℕ) (x : Word k) :
    mixLin k hk 2 x (idx hk base (t+2)) =
      x (idx hk base (t+2)) + x (idx hk base (t+4)) + x (idx hk base t) := by
  change x (idx hk base (t+2)) + x (ix k hk ((idx hk base (t+2)).val + 2)) +
    rotate hk 2 x (idx hk base (t+2)) = _
  rw [idx_add, rotate_idx]

private lemma mix_rotate_idx {k : ℕ} (hk : 0 < k) (base s t : ℕ) (x : Word k) :
    mixLin k hk 2 (rotate hk s x) (idx hk base (t+s+2)) =
      x (idx hk base (t+2)) + x (idx hk base (t+4)) + x (idx hk base t) := by
  rw [mix_idx, show t+s+2 = t+2+s by omega, show t+s+4 = t+4+s by omega]
  simp only [rotate_idx]

private lemma mix_rotate_step {k : ℕ} (hk : 0 < k) (base t : ℕ) (x : Word k) :
    mixLin k hk 2 (rotate hk 4 x) (idx hk base (t+6)) =
      mixLin k hk 2 (rotate hk 3 x) (idx hk base (t+5)) := by
  exact (mix_rotate_idx hk base 4 t x).trans (mix_rotate_idx hk base 3 t x).symm

private def window {k : ℕ} (hk : 0 < k) (base : ℕ) (x : Word k) : Fin 7 → F :=
  fun i => x (idx hk base (7+i.val))

private lemma window_lift {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (base : ℕ) (x : Fin 7 → F) :
    ∃ y : Word k, window hk base y = x ∧
      y (idx hk base 6) = (if k = 7 then 1 else 0) * x 6 := by
  classical
  let f : Fin 7 → Fin k := fun j => idx hk base (7+j.val)
  have hinj : Function.Injective f := by
    intro i j hij
    have h : base + 7 + i.val ≡ base + 7 + j.val [MOD k] := by
      simpa only [Nat.ModEq, f, idx, ix, Nat.add_assoc] using congrArg Fin.val hij
    have h' := Nat.ModEq.add_left_cancel' (base+7) h
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (i.isLt.trans_le h7),
      Nat.mod_eq_of_lt (j.isLt.trans_le h7)] using h'
  let y := Function.extend f x (fun _ => 0)
  refine ⟨y, ?_, ?_⟩
  · funext i
    exact hinj.extend_apply x (fun _ => 0) i
  change Function.extend f x (fun _ => 0) (idx hk base 6) = _
  by_cases he : k = 7
  · subst k
    have hi : f 6 = idx hk base 6 := by
      change ix 7 hk (base+13) = ix 7 hk (base+6)
      exact ix_add_mul_k 7 hk (base+6) 1
    rw [← hi, hinj.extend_apply]
    simp
  · have hn : ¬ ∃ j, f j = idx hk base 6 := by
      rintro ⟨j, hj⟩
      have hb : base + 6 + (1+j.val) ≡ base + 6 + 0 [MOD k] := by
        change (base + 6 + (1+j.val)) % k = (base + 6 + 0) % k
        rw [show base + 6 + (1+j.val) = base + (7+j.val) by omega, Nat.add_zero]
        exact congrArg Fin.val hj
      have hjk : 1 + j.val < k := by have := j.isLt; omega
      have hz := Nat.ModEq.add_left_cancel' (base+6) hb
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hjk, Nat.zero_mod] at hz
      omega
    rw [Function.extend_apply' _ _ _ hn]
    simp [he]

private def gateAt {k : ℕ} (hk : 0 < k) (y : Word k) (i : Fin k) : F :=
  gate (y i) (y (ix k hk (i.val+1))) (y (ix k hk (i.val+2)))

private def update {k : ℕ} (hk : 0 < k) (x : Word k) : Word k :=
  gateAt hk (mixLin k hk 2 x)

private def run {k : ℕ} (hk : 0 < k) (key name c1 c2 : Word k) : Word k :=
  update hk (update hk (rotate hk 3 key + name) + rotate hk 4 key + c1) + rotate hk 7 key + c2

private lemma gateAt_idx {k : ℕ} (hk : 0 < k) (base t : ℕ) (y : Word k) :
    gateAt hk y (idx hk base t) =
      gate (y (idx hk base t)) (y (idx hk base (t+1))) (y (idx hk base (t+2))) := by
  simp only [gateAt, idx_add]

private lemma run_idx {k : ℕ} (hk : 0 < k) (base : ℕ) (key name c1 c2 : Word k) :
    let y := mixLin k hk 2 (rotate hk 3 key + name)
    let b := mixLin k hk 2 (rotate hk 4 key + c1)
    run hk key name c1 c2 (idx hk base 7) =
      response (window hk base y) (y (idx hk base 6)) (b (idx hk base 8)) (b (idx hk base 9)) +
        (y (idx hk base 5) + b (idx hk base 7) + key (idx hk base 0) + c2 (idx hk base 7)) := by
  let y := mixLin k hk 2 (rotate hk 3 key + name)
  let b := mixLin k hk 2 (rotate hk 4 key + c1)
  let q := mixLin k hk 2 (update hk (rotate hk 3 key + name) + rotate hk 4 key + c1)
  have hq : q = mixLin k hk 2 (gateAt hk y) + b := by
    dsimp only [q, update, y, b]
    rw [add_assoc, map_add]
  change gateAt hk q (idx hk base 7) + rotate hk 7 key (idx hk base 7) + c2 (idx hk base 7) =
    response (window hk base y) (y (idx hk base 6)) (b (idx hk base 8)) (b (idx hk base 9)) +
      (y (idx hk base 5) + b (idx hk base 7) + key (idx hk base 0) + c2 (idx hk base 7))
  rw [hq, gateAt_idx, rotate_idx hk base 7 0]
  simp only [Pi.add_apply, mix_idx hk base 5, mix_idx hk base 6, mix_idx hk base 7, gateAt_idx,
    response, window, gate,
    show 7+(0 : Fin 7).val = 7 from rfl,
    show 7+(1 : Fin 7).val = 8 from rfl,
    show 7+(2 : Fin 7).val = 9 from rfl,
    show 7+(3 : Fin 7).val = 10 from rfl,
    show 7+(4 : Fin 7).val = 11 from rfl,
    show 7+(5 : Fin 7).val = 12 from rfl,
    show 7+(6 : Fin 7).val = 13 from rfl]
  ring

private lemma z2_sub_as_add (a b : F) : a - b = a + b := by
  revert a b
  decide

private lemma z2_translate (a b c : F) : a + c = (b+c)+(a+b) := by
  revert a b c
  decide

private lemma rotate_translate {k : ℕ} (hk : 0 < k) (s : ℕ) (left right mask : Word k) :
    rotate hk s left + mask =
      (rotate hk s right + mask) + rotate hk s (left+right) := by
  funext i
  exact z2_translate (rotate hk s left i) (rotate hk s right i) (mask i)

private lemma run_diff_idx {k : ℕ} (hk : 0 < k) (base : ℕ) (left right name c1 c2 : Word k) :
    let d := left+right
    let y := mixLin k hk 2 (rotate hk 3 right + name)
    let e := mixLin k hk 2 (rotate hk 3 d)
    let b := mixLin k hk 2 (rotate hk 4 right + c1)
    run hk left name c1 c2 (idx hk base 7) - run hk right name c1 c2 (idx hk base 7) =
      localDiff (window hk base e) (y (idx hk base 6)) (e (idx hk base 6))
          (b (idx hk base 8)) (b (idx hk base 9)) (window hk base y) +
        (e (idx hk base 5) + e (idx hk base 6) + d (idx hk base 0)) := by
  let d := left+right
  let y := mixLin k hk 2 (rotate hk 3 right + name)
  let e := mixLin k hk 2 (rotate hk 3 d)
  let b := mixLin k hk 2 (rotate hk 4 right + c1)
  let drift := mixLin k hk 2 (rotate hk 4 d)
  have hy : mixLin k hk 2 (rotate hk 3 left + name) = y + e := by
    rw [rotate_translate hk 3 left right name, map_add]
  have hb : mixLin k hk 2 (rotate hk 4 left + c1) = b + drift := by
    rw [rotate_translate hk 4 left right c1, map_add]
  have hd0 : drift (idx hk base 7) = e (idx hk base 6) := mix_rotate_step hk base 1 d
  have hd1 : drift (idx hk base 8) = window hk base e 0 := mix_rotate_step hk base 2 d
  have hd2 : drift (idx hk base 9) = window hk base e 1 := mix_rotate_step hk base 3 d
  have hw : window hk base (y+e) = window hk base y + window hk base e := rfl
  have hkey : left (idx hk base 0) - right (idx hk base 0) = d (idx hk base 0) :=
    z2_sub_as_add _ _
  change _ = localDiff (window hk base e) (y (idx hk base 6)) (e (idx hk base 6))
    (b (idx hk base 8)) (b (idx hk base 9)) (window hk base y) +
      (e (idx hk base 5) + e (idx hk base 6) + d (idx hk base 0))
  simp only [run_idx, hy, hb, hw, Pi.add_apply, hd0, hd1, hd2, localDiff]
  linear_combination hkey

private lemma z2_constant (a b c q : F) : b+a+c = 0 → c+b+q+q = a := by
  revert a b c q
  decide

private lemma constant_idx {k : ℕ} (hk : 0 < k) (base : ℕ) (d : Word k) :
    let e := mixLin k hk 2 (rotate hk 3 d)
    e (idx hk base 6) = 0 → e (idx hk base 7) = 0 →
      e (idx hk base 5) + e (idx hk base 6) + d (idx hk base 0) =
        rotate hk 1 d (idx hk base 7) := by
  dsimp only
  intro hm h0
  rw [hm, add_zero, mix_rotate_idx hk base 3 0, rotate_idx hk base 1 6]
  rw [mix_rotate_idx hk base 3 2] at h0
  exact z2_constant _ _ _ _ h0

private theorem run_constant_iff {k : ℕ} (hk : 0 < k) (h7 : 7 ≤ k) (hk3 : k % 3 ≠ 0)
    (c1 c2 left right : Word k) (site : Fin k) (bit : F) :
    (∀ name : Word k, run hk left name c1 c2 site + run hk right name c1 c2 site = bit) ↔
      (∀ a : Fin 8, mixLin k hk 2 (rotate hk 3 (left+right))
        (ix k hk (site.val+k-1+a.val)) = 0) ∧ bit = rotate hk 1 (left+right) site := by
  let base := site.val + k - 7
  let d := left+right
  let e := mixLin k hk 2 (rotate hk 3 d)
  let b := mixLin k hk 2 (rotate hk 4 right+c1)
  let c := e (idx hk base 5) + e (idx hk base 6) + d (idx hk base 0)
  let y : Word k → Word k := fun name => mixLin k hk 2 (rotate hk 3 right+name)
  have hs : idx hk base 7 = site := by
    have heq : base + 7 = site.val + 1*k := by dsimp [base]; omega
    rw [idx, heq, ix_add_mul_k, ix_val_eq]
  have hoffset (a : Fin 8) :
      ix k hk (site.val+k-1+a.val) = idx hk base (6+a.val) := by
    unfold idx
    congr 1
    dsimp [base]
    omega
  have hwindows : (∀ a : Fin 8, e (idx hk base (6+a.val)) = 0) ↔
      window hk base e = 0 ∧ e (idx hk base 6) = 0 := by
    constructor
    · intro h
      refine ⟨funext ?_, h 0⟩
      intro i
      have hi := i.isLt
      let a : Fin 8 := ⟨i.val+1, by omega⟩
      change e (idx hk base (7+i.val)) = 0
      rw [show 7+i.val = 6+a.val by dsimp [a]; omega]
      exact h a
    · rintro ⟨hw, hm⟩ a
      have ha := a.isLt
      by_cases hz : a.val = 0
      · simpa only [hz, Nat.add_zero] using hm
      · let i : Fin 7 := ⟨a.val-1, by omega⟩
        have hi := congrFun hw i
        change e (idx hk base (7+i.val)) = 0 at hi
        rw [show 6+a.val = 7+i.val by dsimp [i]; omega]
        exact hi
  have hrun (name : Word k) :
      run hk left name c1 c2 (idx hk base 7) + run hk right name c1 c2 (idx hk base 7) =
        localDiff (window hk base e) (y name (idx hk base 6)) (e (idx hk base 6))
          (b (idx hk base 8)) (b (idx hk base 9)) (window hk base (y name)) + c := by
    rw [← z2_sub_as_add]
    exact run_diff_idx hk base left right name c1 c2
  have hy : Function.Surjective y := starting_mix_surjective k hk hk3 right
  change (∀ name, run hk left name c1 c2 site + run hk right name c1 c2 site = bit) ↔
    (∀ a : Fin 8, e (ix k hk (site.val+k-1+a.val)) = 0) ∧ bit = rotate hk 1 d site
  simp only [hoffset, hwindows]
  rw [← hs]
  have hc (he : window hk base e = 0) (hm : e (idx hk base 6) = 0) :
      c = rotate hk 1 d (idx hk base 7) :=
    constant_idx hk base d hm (congrFun he (0 : Fin 7))
  constructor
  · intro h
    let w : F := if k = 7 then 1 else 0
    have hlocal (x : Fin 7 → F) :
        localDiff (window hk base e) (w * x 6) (e (idx hk base 6))
          (b (idx hk base 8)) (b (idx hk base 9)) x = bit - c := by
      obtain ⟨v, hv, hm⟩ := window_lift hk h7 base x
      obtain ⟨name, hn⟩ := hy v
      have hname := h name
      rw [hrun, hn, hv, hm] at hname
      exact eq_sub_of_add_eq hname
    obtain ⟨he, hm, hbit⟩ := (diff_constant_iff _ w _ _ _ _).mp hlocal
    exact ⟨⟨he, hm⟩, (sub_eq_zero.mp hbit).trans (hc he hm)⟩
  · rintro ⟨⟨he, hm⟩, hbit⟩ name
    rw [hrun, he, hm, localDiff_zero, zero_add]
    exact (hc he hm).trans hbit.symm

end PEqualNP.Outside.L_meta_29747_aux

theorem PEqualNP.Outside.L_meta_29747 : ∀ (k : ℕ) (hk : 0 < k), 7 ≤ k → k % 3 ≠ 0 →
  let W := Fin k → ZMod 2
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val+k-(s % k)))
  let mix := fun (x : W) (i : Fin k) => x i + x (ix (i.val+2)) + rot 2 x i
  let upd := fun (x : W) (i : Fin k) =>
    let y := mix x
    y i + (1+y (ix (i.val+1)))*y (ix (i.val+2))
  let run := fun (key name c1 c2 : W) =>
    upd (upd (rot 3 key + name) + rot 4 key + c1) + rot 7 key + c2
  ∀ (c1 c2 left right : W) (site : Fin k) (bit : ZMod 2),
    let d := left+right
    Iff (∀ name : W, run left name c1 c2 site + run right name c1 c2 site = bit)
      ((∀ a : Fin 8, mix (rot 3 d) (ix (site.val+k-1+a.val)) = 0) ∧ bit = rot 1 d site) := by
  intro k hk h7 hk3
  dsimp only
  exact PEqualNP.Outside.L_meta_29747_aux.run_constant_iff hk h7 hk3
