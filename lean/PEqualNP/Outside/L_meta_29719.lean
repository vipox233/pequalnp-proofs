import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29719

section Gen

variable {V : Type*} [AddCommGroup V]

def dif (f : V → ZMod 2) (u : V) : V → ZMod 2 := fun x => f (x + u) - f x

def Van : ℕ → (V → ZMod 2) → Prop
  | 0, f => ∀ x, f x = 0
  | n + 1, f => ∀ u, Van n (dif f u)

theorem van_add : ∀ (n : ℕ) (f g : V → ZMod 2), Van n f → Van n g → Van n (fun x => f x + g x)
  | 0, f, g, hf, hg => fun x => by simp [hf x, hg x]
  | n + 1, f, g, hf, hg => fun u => by
      have h := van_add n _ _ (hf u) (hg u)
      have e : dif (fun x => f x + g x) u = fun x => dif f u x + dif g u x := by
        funext x; simp only [dif]; ring
      rw [e]; exact h

theorem van_zero : ∀ (n : ℕ), Van n (fun _ : V => (0 : ZMod 2))
  | 0 => fun _ => rfl
  | n + 1 => fun u => by
      have e : dif (fun _ : V => (0 : ZMod 2)) u = fun _ => 0 := by funext x; simp [dif]
      rw [e]; exact van_zero n

theorem van_congr {n : ℕ} {f g : V → ZMod 2} (h : ∀ x, f x = g x) (hf : Van n f) : Van n g := by
  have : f = g := funext h
  subst this; exact hf

theorem van_mono : ∀ (n : ℕ) (f : V → ZMod 2), Van n f → Van (n + 1) f
  | 0, f, hf => fun u => fun x => by simp only [dif]; rw [hf, hf]; simp
  | n + 1, f, hf => fun u => van_mono n _ (hf u)

theorem van_mono' {n m : ℕ} (h : n ≤ m) {f : V → ZMod 2} (hf : Van n f) : Van m f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact van_mono _ _ ih

theorem van_cmul : ∀ (n : ℕ) (c : ZMod 2) (f : V → ZMod 2), Van n f → Van n (fun x => c * f x)
  | 0, c, f, hf => fun x => by simp [hf x]
  | n + 1, c, f, hf => fun u => by
      have e : dif (fun x => c * f x) u = fun x => c * dif f u x := by
        funext x; simp only [dif]; ring
      rw [e]; exact van_cmul n c _ (hf u)

theorem van_shift : ∀ (n : ℕ) (a : V) (f : V → ZMod 2), Van n f → Van n (fun x => f (x + a))
  | 0, a, f, hf => fun x => hf _
  | n + 1, a, f, hf => fun u => by
      have e : dif (fun x => f (x + a)) u = fun x => dif f u (x + a) := by
        funext x; simp only [dif]; rw [add_right_comm]
      rw [e]; exact van_shift n a _ (hf u)

theorem van_one_const {f : V → ZMod 2} (hf : Van 1 f) : ∀ x, f x = f 0 := by
  intro x
  have := hf x 0
  simp only [dif, zero_add] at this
  exact sub_eq_zero.mp this

theorem van_mul : ∀ (a b : ℕ) (f g : V → ZMod 2), Van (a + 1) f → Van (b + 1) g →
    Van (a + b + 1) (fun x => f x * g x)
  | 0, b, f, g, hf, hg => by
      have hc := van_one_const hf
      simp only [zero_add]
      exact van_congr (fun x => by rw [hc x]) (van_cmul _ (f 0) g hg)
  | a + 1, 0, f, g, hf, hg => by
      have hc := van_one_const hg
      exact van_congr (fun x => by rw [hc x, mul_comm]) (van_cmul _ (g 0) f hf)
  | a + 1, b + 1, f, g, hf, hg => fun u => by
      have e : dif (fun x => f x * g x) u =
          fun x => dif f u x * g (x + u) + f x * dif g u x := by
        funext x; simp only [dif]; ring
      rw [e]
      apply van_add
      · have h1 := van_mul a (b + 1) (dif f u) (fun x => g (x + u)) (hf u)
          (van_shift _ u g hg)
        have : a + (b + 1) + 1 = a + 1 + b + 1 := by omega
        rw [this] at h1; exact h1
      · exact van_mul (a + 1) b f (dif g u) hf (hg u)

theorem van_const (c : ZMod 2) : Van 1 (fun _ : V => c) := fun u x => by simp [dif]

theorem van_lin (f : V →+ ZMod 2) : Van 2 (fun x => f x) := fun u => by
  have e : dif (fun x => f x) u = fun _ => f u := by funext x; simp [dif, map_add]
  rw [e]; exact van_const _

theorem van_fold : ∀ (l : List V) (n : ℕ) (f : V → ZMod 2), Van (n + l.length) f → Van n (l.foldl dif f)
  | [], n, f, h => h
  | u :: l, n, f, h => by
      simp only [List.foldl_cons]
      apply van_fold l n
      have : n + (u :: l).length = (n + l.length) + 1 := by simp; omega
      rw [this] at h; exact h u

theorem fold_add : ∀ (l : List V) (f g : V → ZMod 2),
    l.foldl dif (fun x => f x + g x) = fun x => l.foldl dif f x + l.foldl dif g x
  | [], f, g => rfl
  | u :: l, f, g => by
      simp only [List.foldl_cons]
      have e : dif (fun x => f x + g x) u = fun x => dif f u x + dif g u x := by
        funext x; simp only [dif]; ring
      rw [e, fold_add l]

variable [Module (ZMod 2) V]

theorem fold_agree (M : Submodule (ZMod 2) V) : ∀ (l : List V) (f g : V → ZMod 2),
    (∀ z ∈ M, f z = g z) → (∀ u ∈ l, u ∈ M) → ∀ z ∈ M, l.foldl dif f z = l.foldl dif g z
  | [], f, g, h, _, z, hz => h z hz
  | u :: l, f, g, h, hl, z, hz => by
      simp only [List.foldl_cons]
      have hu : u ∈ M := hl u (by simp)
      apply fold_agree M l
      · intro y hy
        simp only [dif]
        rw [h _ (M.add_mem hy hu), h _ hy]
      · intro w hw; exact hl w (by simp [hw])
      · exact hz

theorem fold_inv (K : Submodule (ZMod 2) V) : ∀ (n : ℕ) (v u : Fin n → V) (f : V → ZMod 2),
    (∀ x, ∀ kk ∈ K, f (x + kk) = f x) → (∀ j, v j - u j ∈ K) →
    (List.ofFn v).foldl dif f = (List.ofFn u).foldl dif f
  | 0, v, u, f, _, _ => by simp
  | n + 1, v, u, f, hf, hvu => by
      simp only [List.ofFn_succ, List.foldl_cons]
      have e : dif f (v 0) = dif f (u 0) := by
        funext x; simp only [dif]
        have : x + v 0 = (x + u 0) + (v 0 - u 0) := by abel
        rw [this, hf _ _ (hvu 0)]
      rw [e]
      apply fold_inv K n
      · intro x kk hk
        simp only [dif]
        rw [add_right_comm, hf _ _ hk, hf _ _ hk]
      · intro j; exact hvu j.succ

theorem fold_comp {V' : Type*} [AddCommGroup V'] (P : V →+ V') (c : V') : ∀ (n : ℕ) (v : Fin n → V)
    (f : V' → ZMod 2), (List.ofFn v).foldl dif (fun x => f (P x + c)) =
      fun x => (List.ofFn (fun j => P (v j))).foldl dif f (P x + c)
  | 0, v, f => by simp
  | n + 1, v, f => by
      simp only [List.ofFn_succ, List.foldl_cons]
      have e : dif (fun x => f (P x + c)) (v 0) = fun x => dif f (P (v 0)) (P x + c) := by
        funext x; simp only [dif, map_add]; rw [add_right_comm]
      rw [e]
      exact fold_comp P c n (fun j => v j.succ) (dif f (P (v 0)))


end Gen

section Cyc
theorem cast_sub (k : ℕ) (hk : 0 < k) (a c : ℕ) :
    (((a + k - c % k : ℕ)) : ZMod k) = (a : ZMod k) - (c : ZMod k) := by
  have h : c % k < k := Nat.mod_lt _ hk
  rw [Nat.cast_sub (by omega)]
  simp [ZMod.natCast_mod]

variable (k : ℕ) (hk : 0 < k)

def ix (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩
def rot (s : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 := x (ix k hk (i.val + k - s % k))
def mix (g : ℕ) (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + x (ix k hk (i.val + g)) + x (ix k hk (i.val + k - g % k))
def stp (x : Fin k → ZMod 2) (i : Fin k) : ZMod 2 :=
  x i + (1 + x (ix k hk (i.val + 1))) * x (ix k hk (i.val + 2))

def zf (g s : ℕ) (nm : Fin k → ZMod 2) (x : Fin k → ZMod 2) : Fin k → ZMod 2 :=
  mix k hk g (rot k hk s x + nm)
def yq (g s : ℕ) (nm : Fin k → ZMod 2) (x : Fin k → ZMod 2) (j : Fin k) : ZMod 2 :=
  (1 + zf k hk g s nm x (ix k hk (j.val + 1))) * zf k hk g s nm x (ix k hk (j.val + 2))
def Qf (g s : ℕ) (nm : Fin k → ZMod 2) (i : Fin k) (x : Fin k → ZMod 2) : ZMod 2 :=
  mix k hk g (yq k hk g s nm x) (ix k hk (i.val + 1)) *
    mix k hk g (yq k hk g s nm x) (ix k hk (i.val + 2))

theorem cast_ix (n : ℕ) : (((ix k hk n).val : ℕ) : ZMod k) = (n : ZMod k) := by
  simp [ix, ZMod.natCast_mod]

theorem winv (b : Bool) (nm : Fin k → ZMod 2) (i : Fin k) (kk : Fin k → ZMod 2)
    (hK : ∀ r : ℕ, r < (if b then 11 else 7) →
      kk (ix k hk (i.val + k - (if b then 5 else 1) % k + r)) = 0) (x : Fin k → ZMod 2) :
    Qf k hk (if b then 2 else 1) (if b then 3 else 1) nm i (x + kk) =
      Qf k hk (if b then 2 else 1) (if b then 3 else 1) nm i x := by
  have hz : ∀ r : ℕ, r < (if b then 11 else 7) → ∀ p : Fin k,
      ((p.val : ℕ) : ZMod k) = (i.val : ZMod k) + (r : ZMod k) - ((if b then 5 else 1 : ℕ) : ZMod k) →
      kk p = 0 := by
    intro r hr p hp
    have : p = ix k hk (i.val + k - (if b then 5 else 1) % k + r) := by
      apply Fin.ext
      have h2 := (ZMod.natCast_eq_natCast_iff' p.val (i.val + k - (if b then 5 else 1) % k + r) k).mp
        (by rw [hp, Nat.cast_add, cast_sub k hk]; ring)
      rw [Nat.mod_eq_of_lt p.isLt] at h2
      simpa [ix] using h2
    rw [this]; exact hK r hr
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hz
    have h0 := hz 0 (by norm_num); have h1 := hz 1 (by norm_num); have h2 := hz 2 (by norm_num)
    have h3 := hz 3 (by norm_num); have h4 := hz 4 (by norm_num); have h5 := hz 5 (by norm_num)
    have h6 := hz 6 (by norm_num)
    simp only [Bool.false_eq_true, ↓reduceIte]
    simp only [Qf, yq, zf, mix, rot, Pi.add_apply]
    simp (disch := (simp only [cast_ix, cast_sub k hk, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_zero]; ring1)) only [h0, h1, h2, h3, h4, h5, h6, add_zero]
  · simp only [↓reduceIte] at hz
    have h0 := hz 0 (by norm_num); have h1 := hz 1 (by norm_num); have h2 := hz 2 (by norm_num)
    have h3 := hz 3 (by norm_num); have h4 := hz 4 (by norm_num); have h5 := hz 5 (by norm_num)
    have h6 := hz 6 (by norm_num); have h7 := hz 7 (by norm_num); have h8 := hz 8 (by norm_num)
    have h9 := hz 9 (by norm_num); have h10 := hz 10 (by norm_num)
    simp only [↓reduceIte]
    simp only [Qf, yq, zf, mix, rot, Pi.add_apply]
    simp (disch := (simp only [cast_ix, cast_sub k hk, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
      Nat.cast_zero]; ring1)) only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, add_zero]


abbrev W := Fin k → ZMod 2

theorem pv_coord (p : Fin k) : Van 2 (fun x : W k => x p) :=
  van_lin (Pi.evalAddMonoidHom (fun _ : Fin k => ZMod 2) p)

theorem decomp (g s r1 r2 : ℕ) (nm c1 c2 : Fin k → ZMod 2) (i : Fin k) :
    ∃ C : W k → ZMod 2, Van 4 C ∧ ∀ x : W k,
      (stp k hk (mix k hk g (stp k hk (mix k hk g (rot k hk s x + nm)) + rot k hk r1 x + c1)) +
        rot k hk r2 x + c2) i = Qf k hk g s nm i x + C x := by
  have hz : ∀ p, Van 2 (fun x : W k => zf k hk g s nm x p) := by
    intro p
    simp only [zf, mix, rot, Pi.add_apply]
    refine van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _))))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
  have hy : ∀ j, Van 3 (fun x : W k => yq k hk g s nm x j) := by
    intro j
    simp only [yq]
    exact van_mul 1 1 _ _ (van_add _ _ _ (van_mono _ _ (van_const _)) (hz _)) (hz _)
  let l : W k → Fin k → ZMod 2 := fun x j => zf k hk g s nm x j + rot k hk r1 x j + c1 j
  have hl : ∀ j, Van 2 (fun x => l x j) := by
    intro j
    exact van_add _ _ _ (van_add _ _ _ (hz j) (pv_coord k _)) (van_mono _ _ (van_const _))
  have hw : ∀ j, Van 3 (fun x : W k => mix k hk g (yq k hk g s nm x) j) := by
    intro j; simp only [mix]
    exact van_add _ _ _ (van_add _ _ _ (hy _) (hy _)) (hy _)
  have hm : ∀ j, Van 2 (fun x : W k => mix k hk g (l x) j) := by
    intro j; simp only [mix]
    exact van_add _ _ _ (van_add _ _ _ (hl _) (hl _)) (hl _)
  let w' := fun (x : W k) => mix k hk g (yq k hk g s nm x)
  let m := fun (x : W k) => mix k hk g (l x)
  let i1 := ix k hk (i.val + 1)
  let i2 := ix k hk (i.val + 2)
  refine ⟨fun x => (w' x i + m x i) + (w' x i2 + m x i2) + w' x i1 * m x i2 + m x i1 * w' x i2
    + m x i1 * m x i2 + rot k hk r2 x i + c2 i, ?_, ?_⟩
  · have a1 : Van 4 (fun x => w' x i + m x i) :=
      van_mono _ _ (van_add _ _ _ (hw i) (van_mono _ _ (hm i)))
    have a2 : Van 4 (fun x => w' x i2 + m x i2) :=
      van_mono _ _ (van_add _ _ _ (hw i2) (van_mono _ _ (hm i2)))
    have a3 : Van 4 (fun x => w' x i1 * m x i2) := van_mul 2 1 _ _ (hw i1) (hm i2)
    have a4 : Van 4 (fun x => m x i1 * w' x i2) := by
      have := van_mul 1 2 _ _ (hm i1) (hw i2); exact this
    have a5 : Van 4 (fun x => m x i1 * m x i2) := van_mono _ _ (van_mul 1 1 _ _ (hm i1) (hm i2))
    have a6 : Van 4 (fun x : W k => rot k hk r2 x i) := van_mono' (by norm_num) (pv_coord k _)
    have a7 : Van 4 (fun _ : W k => c2 i) := van_mono' (by norm_num) (van_const _)
    exact van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (van_add _ _ _
      (van_add _ _ _ a1 a2) a3) a4) a5) a6) a7
  · intro x
    have e : ∀ j, (mix k hk g (stp k hk (mix k hk g (rot k hk s x + nm)) + rot k hk r1 x + c1)) j
        = w' x j + m x j := by
      intro j
      simp only [w', m, l, mix, stp, yq, zf, Pi.add_apply]
      ring
    simp only [stp, Pi.add_apply, Qf]
    rw [e, e, e]
    simp only [w', m, i1, i2]
    ring

end Cyc


section Main

theorem two_eq (a : ZMod 2) : a + a = 0 := by
  revert a; decide

theorem bit_eq (a b : ZMod 2) (h : (if a = 0 then (0 : ℕ) else 1) = (if b = 0 then 0 else 1)) :
    a = b := by
  revert a b; decide

theorem fold_dec {α : Type*} (l : List α) : ∀ (c c' : α → ℕ), (∀ j, c j ≤ 1) → (∀ j, c' j ≤ 1) →
    l.foldl (fun h j => 2 * h + c j) 0 = l.foldl (fun h j => 2 * h + c' j) 0 →
    ∀ j ∈ l, c j = c' j := by
  induction l using List.reverseRecOn with
  | nil => intro c c' _ _ _ j hj; simp at hj
  | append_singleton l a ih =>
    intro c c' hc hc' h j hj
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    have ha := hc a; have ha' := hc' a
    have e1 : c a = c' a := by omega
    have e2 : l.foldl (fun h j => 2 * h + c j) 0 = l.foldl (fun h j => 2 * h + c' j) 0 := by omega
    rcases List.mem_append.mp hj with hj | hj
    · exact ih c c' hc hc' e2 j hj
    · simp at hj; subst hj; exact e1

theorem fold_zero {α : Type*} (c : ℕ → α → ℕ) (l : List α) (h : ∀ j ∈ l, c 0 j = 0) :
    l.foldl (fun h j => 2 * h + c h j) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, mul_zero, zero_add, h a (by simp)]
    exact ih (fun j hj => h j (by simp [hj]))

variable (k : ℕ) (hk : 0 < k)

def Kb (len off : ℕ) (i : Fin k) : Submodule (ZMod 2) (W k) :=
  ⨅ (r : Fin len), LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin k => ZMod 2)
    (ix k hk (i.val + k - off % k + r.val)))

theorem mem_Kb (len off : ℕ) (i : Fin k) (x : W k) :
    x ∈ Kb k hk len off i ↔ ∀ r : ℕ, r < len → x (ix k hk (i.val + k - off % k + r)) = 0 := by
  simp only [Kb, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply]
  constructor
  · intro h r hr; exact h ⟨r, hr⟩
  · intro h r; exact h r.val r.isLt

theorem mainA (d : ℕ) (o : W k → Bool → Fin k → ZMod 2) (marked : Bool → Fin k → Bool)
    (Q : Bool → Fin k → W k → ZMod 2) (hQ5 : ∀ b i, Van 5 (Q b i))
    (hC : ∀ b i, ∃ C : W k → ZMod 2, Van 4 C ∧ ∀ x, o x b i = Q b i x + C x)
    (hinv : ∀ b i, ∀ kk ∈ Kb k hk (if b then 11 else 7) (if b then 5 else 1) i,
      ∀ x, Q b i (x + kk) = Q b i x) :
    let D := W k →ₗ[ZMod 2] ZMod 2
    let run := fun (ask : Fin d → ℕ → D) (x : W k) =>
      (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    let fits := fun (ask : Fin d → ℕ → D) =>
      ∃ readout : ℕ → Bool → Fin k → W k → ZMod 2,
        (∀ h b i, ∀ (v : Fin 4 → W k) x, (List.ofFn v).foldl dif (readout h b i) x = 0) ∧
        ∀ x b i, marked b i = true → o x b i = readout (run ask x) b i x
    let localTo := fun (q : D) (b : Bool) (i : Fin k) =>
      ∀ x : W k, (∀ r : ℕ, r < (if b then 11 else 7) →
        x (ix k hk (i.val + k - (if b then 5 else 1) % k + r)) = 0) → q x = 0
    (∃ ask, fits ask) ↔
    (∃ queries : Fin d → D, fits (fun n _ => queries n) ∧
      ∀ n, queries n = 0 ∨ ∃ b i, marked b i = true ∧ localTo (queries n) b i) := by
  classical
  intro D run fits localTo
  constructor
  swap
  · rintro ⟨q, hq, -⟩; exact ⟨_, hq⟩
  rintro ⟨ask, R, hRc, hR⟩
  let U : Submodule (ZMod 2) (W k) := ⨅ j : Fin d, LinearMap.ker (ask j 0)
  have hrun0 : ∀ x ∈ U, run ask x = 0 := by
    intro x hx
    simp only [U, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    exact fold_zero (fun h j => if ask j h x = 0 then 0 else 1) _ (fun j _ => by simp [hx j])
  let S : Set D := {q | (∀ u ∈ U, q u = 0) ∧ ∃ b i, marked b i = true ∧ localTo q b i}
  obtain ⟨T, hTS, hspan, hli⟩ := exists_linearIndependent (ZMod 2) S
  have hTfin : T.Finite := hli.setFinite
  haveI := hTfin.fintype
  let Tf := hTfin.toFinset
  have hcard : Tf.card ≤ d := by
    have h1 := finrank_span_eq_card hli
    have h2 : Set.range (Subtype.val : T → D) = T := Subtype.range_coe
    rw [h2, hspan] at h1
    have h3 : Submodule.span (ZMod 2) S ≤ Submodule.span (ZMod 2) (Set.range (fun j : Fin d => ask j 0)) := by
      rw [Submodule.span_le]
      intro q hq
      apply mem_span_of_iInf_ker_le_ker
      intro u hu
      exact hq.1 u hu
    have h4 := Submodule.finrank_mono h3
    have h5 := finrank_range_le_card (R := ZMod 2) (fun j : Fin d => ask j 0)
    simp only [Set.finrank, Fintype.card_fin] at h5
    have h6 : Tf.card = Fintype.card T := by
      simp only [Tf]; convert Set.Finite.card_toFinset hTfin
    have h7 : Fintype.card {x // x ∈ T} = Fintype.card T := Fintype.card_congr (Equiv.refl _)
    omega
  let qs : Fin d → D := fun n =>
    if h : n.val < Tf.card then (Tf.equivFin.symm ⟨n.val, h⟩ : D) else 0
  have hqT : ∀ q ∈ T, ∃ n, qs n = q := by
    intro q hq
    have hq' : q ∈ Tf := by simp [Tf, hq]
    refine ⟨⟨(Tf.equivFin ⟨q, hq'⟩).val, lt_of_lt_of_le (Tf.equivFin ⟨q, hq'⟩).isLt hcard⟩, ?_⟩
    simp [qs]
  have hqS : ∀ n, qs n = 0 ∨ qs n ∈ S := by
    intro n
    by_cases h : n.val < Tf.card
    · right
      simp only [qs, h, dif_pos]
      have := (Tf.equivFin.symm ⟨n.val, h⟩).property
      exact hTS ((Set.Finite.mem_toFinset hTfin).mp this)
    · left; simp [qs, h]
  let V : Submodule (ZMod 2) (W k) := ⨅ n : Fin d, LinearMap.ker (qs n)
  have hSV : ∀ q ∈ S, ∀ v ∈ V, q v = 0 := by
    intro q hq v hv
    have hle : Submodule.span (ZMod 2) T ≤ LinearMap.ker (Module.Dual.eval (ZMod 2) (W k) v) := by
      rw [Submodule.span_le]
      intro p hp
      obtain ⟨n, rfl⟩ := hqT p hp
      simp only [V, Submodule.mem_iInf, LinearMap.mem_ker] at hv
      show (Module.Dual.eval (ZMod 2) (W k) v) (qs n) = 0
      rw [Module.Dual.eval_apply]; exact hv n
    have := hle (hspan ▸ Submodule.subset_span hq)
    rw [LinearMap.mem_ker, Module.Dual.eval_apply] at this; exact this
  have hVUK : ∀ b i, marked b i = true →
      V ≤ U ⊔ Kb k hk (if b then 11 else 7) (if b then 5 else 1) i := by
    intro b i hm v hv
    by_contra hno
    obtain ⟨f, hfv, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hno inferInstance
    have hf0 : ∀ y ∈ U ⊔ Kb k hk (if b then 11 else 7) (if b then 5 else 1) i, f y = 0 := by
      intro y hy
      have h' : f y ∈ Submodule.map f (U ⊔ Kb k hk (if b then 11 else 7) (if b then 5 else 1) i) :=
        Submodule.mem_map.mpr ⟨y, hy, rfl⟩
      rw [hmap, Submodule.mem_bot] at h'; exact h'
    have hfS : f ∈ S := by
      refine ⟨fun u hu => hf0 u (Submodule.mem_sup_left hu), b, i, hm, ?_⟩
      intro x hx
      exact hf0 x (Submodule.mem_sup_right ((mem_Kb k hk _ _ i x).mpr hx))
    exact hfv (hSV f hfS v hv)
  have core : ∀ b i, marked b i = true → ∀ (v : Fin 4 → W k), (∀ j, v j ∈ V) →
      ∀ y, (List.ofFn v).foldl dif (Q b i) y = 0 := by
    intro b i hm v hv y
    obtain ⟨C, hC4, hoC⟩ := hC b i
    have hdec : ∀ j, ∃ u ∈ U, v j - u ∈ Kb k hk (if b then 11 else 7) (if b then 5 else 1) i := by
      intro j
      obtain ⟨u, hu, kk, hkk, he⟩ := Submodule.mem_sup.mp (hVUK b i hm (hv j))
      refine ⟨u, hu, ?_⟩
      rw [← he]; simpa using hkk
    choose u hu hvu using hdec
    have s1 : (List.ofFn v).foldl dif (Q b i) y = (List.ofFn v).foldl dif (Q b i) 0 := by
      have h := van_fold (List.ofFn v) 1 (Q b i) (by simpa using hQ5 b i)
      exact van_one_const h y
    have s2 : (List.ofFn v).foldl dif (Q b i) = (List.ofFn u).foldl dif (Q b i) :=
      fold_inv _ 4 v u (Q b i) (fun x kk hkk => hinv b i kk hkk x) hvu
    have hQe : Q b i = fun x => o x b i + C x := by
      funext x; rw [hoC x, add_assoc, two_eq, add_zero]
    have s3 : (List.ofFn u).foldl dif (fun x => o x b i) 0 =
        (List.ofFn u).foldl dif (R 0 b i) 0 := by
      apply fold_agree U
      · intro z hz
        rw [hR z b i hm, hrun0 z hz]
      · intro w hw
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
        exact hu j
      · exact U.zero_mem
    have s4 : (List.ofFn u).foldl dif C 0 = 0 := van_fold (List.ofFn u) 0 C (by simpa using hC4) 0
    rw [s1, s2, hQe, fold_add]
    beta_reduce
    rw [s3, s4, hRc 0 b i u 0, add_zero]
  obtain ⟨V', hc⟩ := V.exists_isCompl
  let P : W k →ₗ[ZMod 2] W k := V.subtype ∘ₗ V.projectionOnto V' hc
  have hPV : ∀ x, P x ∈ V := fun x => by simp [P]
  have hPid : ∀ v ∈ V, P v = v := by
    intro v hv
    have := Submodule.projectionOnto_apply_left hc ⟨v, hv⟩
    simp [P, this]
  let rd : ℕ → Bool → Fin k → W k → ZMod 2 := fun h b i x =>
    if marked b i = true then
      (if hh : ∃ x0, run (fun n _ => qs n) x0 = h then o (P (x - hh.choose) + hh.choose) b i else 0)
    else 0
  refine ⟨qs, ⟨rd, ?_, ?_⟩, ?_⟩
  · intro h b i v x
    have hz0 : ∀ y, (List.ofFn v).foldl dif (fun _ : W k => (0 : ZMod 2)) y = 0 :=
      fun y => van_fold (List.ofFn v) 0 _ (van_zero _) y
    by_cases hm : marked b i = true
    · by_cases hh : ∃ x0, run (fun n _ => qs n) x0 = h
      · obtain ⟨C, hC4, hoC⟩ := hC b i
        have e : rd h b i = fun x => (fun z => Q b i z + C z)
            (P.toAddMonoidHom x + (hh.choose - P hh.choose)) := by
          funext x
          simp only [rd, hm, hh, if_true, dif_pos]
          rw [hoC]
          congr 2 <;> simp [map_sub] <;> abel
        have hfc := congrFun (fold_comp P.toAddMonoidHom (hh.choose - P hh.choose) 4 v
          (fun z => Q b i z + C z)) x
        rw [e]; refine hfc.trans ?_
        rw [fold_add]
        beta_reduce
        rw [core b i hm (fun j => P.toAddMonoidHom (v j)) (fun j => hPV (v j)),
          van_fold _ 0 C (by simpa using hC4), add_zero]
      · have e : rd h b i = fun _ => 0 := by
          funext x; simp [rd, hm, hh]
        rw [e]; exact hz0 x
    · have e : rd h b i = fun _ => 0 := by
        funext x; simp [rd, hm]
      rw [e]; exact hz0 x
  · intro x b i hm
    have hh : ∃ x0, run (fun n _ => qs n) x0 = run (fun n _ => qs n) x := ⟨x, rfl⟩
    simp only [rd, hm, if_true, dif_pos hh]
    have hx1 := hh.choose_spec
    have hdiff : x - hh.choose ∈ V := by
      simp only [V, Submodule.mem_iInf, LinearMap.mem_ker, map_sub]
      intro n
      have hb := fold_dec (List.finRange d) _ _ (fun j => by split_ifs <;> omega)
        (fun j => by split_ifs <;> omega) hx1 n (List.mem_finRange n)
      rw [bit_eq _ _ hb, sub_self]
    rw [hPid _ hdiff, sub_add_cancel]
  · intro n
    rcases hqS n with h | h
    · exact Or.inl h
    · exact Or.inr h.2

end Main



theorem q5 (k : ℕ) (hk : 0 < k) (g s : ℕ) (nm : Fin k → ZMod 2) (i : Fin k) :
    Van 5 (Qf k hk g s nm i) := by
  have hz : ∀ p, Van 2 (fun x : W k => zf k hk g s nm x p) := by
    intro p
    simp only [zf, mix, rot, Pi.add_apply]
    refine van_add _ _ _ (van_add _ _ _ (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _))))
      (van_add _ _ _ (pv_coord k _) (van_mono _ _ (van_const _)))
  have hy : ∀ j, Van 3 (fun x : W k => yq k hk g s nm x j) := by
    intro j
    simp only [yq]
    exact van_mul 1 1 _ _ (van_add _ _ _ (van_mono _ _ (van_const _)) (hz _)) (hz _)
  have hw : ∀ j, Van 3 (fun x : W k => mix k hk g (yq k hk g s nm x) j) := by
    intro j; simp only [mix]
    exact van_add _ _ _ (van_add _ _ _ (hy _) (hy _)) (hy _)
  exact van_mul 2 2 _ _ (hw _) (hw _)

end PEqualNP.Outside.L_meta_29719

theorem PEqualNP.Outside.L_meta_29719 : (∀ (k : ℕ) (hk : 0 < k),
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  ∀ (name c₁ c₂ : Bool → W) (d : ℕ),
    let out := fun (x : W) (b : Bool) =>
      let z := mix (gap b) (rot (spin b) x + name b)
      let y := step z + rot (if b then 4 else 0) x + c₁ b
      step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
    let run := fun (ask : Fin d → ℕ → D) (x : W) =>
      (List.finRange d).foldl (fun h j =>
        2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
    ∀ marked : Bool → Fin k → Bool,
      let fits := fun (ask : Fin d → ℕ → D) =>
        ∃ readout : ℕ → Bool → Fin k → W → F,
          (∀ h b i, cubic (readout h b i)) ∧
          ∀ x b i, marked b i = true → out x b i = readout (run ask x) b i x
      let localTo := fun (q : D) (b : Bool) (i : Fin k) =>
        ∀ x : W, (∀ r : ℕ, r < (if b then 11 else 7) →
          x (ix (i.val + k - (if b then 5 else 1) % k + r)) = 0) → q x = 0
      (∃ ask, fits ask) ↔
      (∃ queries : Fin d → D, fits (fun n _ => queries n) ∧
        ∀ n, queries n = 0 ∨ ∃ b i, marked b i = true ∧ localTo (queries n) b i)) := by
  intro k hk F W D ix rot mix step gap spin diff fourth cubic name c₁ c₂ d out run marked fits localTo
  exact PEqualNP.Outside.L_meta_29719.mainA k hk d (fun x b i => out x b i) marked
    (fun b i => PEqualNP.Outside.L_meta_29719.Qf k hk (if b then 2 else 1) (if b then 3 else 1) (name b) i)
    (fun b i => PEqualNP.Outside.L_meta_29719.q5 k hk _ _ _ i)
    (fun b i => PEqualNP.Outside.L_meta_29719.decomp k hk (if b then 2 else 1) (if b then 3 else 1)
      (if b then 4 else 0) (if b then 7 else 2) (name b) (c₁ b) (c₂ b) i)
    (fun b i kk hkk x => PEqualNP.Outside.L_meta_29719.winv k hk b (name b) i kk
      ((PEqualNP.Outside.L_meta_29719.mem_Kb k hk _ _ i kk).mp hkk) x)
