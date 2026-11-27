import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25626

open scoped Fin.CommRing
abbrev F := ZMod 2
abbrev A (k : Nat) := Fin k → F
def sh {k : Nat} [NeZero k] (d : Fin k) : A k →ₗ[F] A k where
  toFun x i := x (i+d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def rm {k : Nat} [NeZero k] : A k →ₗ[F] A k := LinearMap.id + sh (-1) + sh (-2)
def tri {k : Nat} [NeZero k] : A k →ₗ[F] A k := sh (-1) + sh (-2) + sh (-3)
def bil {k h : Nat} [NeZero k] (a : Fin k) (x y : A k) : A h := fun j => x (a+(j.val : Fin k)+1)*y (a+(j.val : Fin k)+2) + x (a+(j.val : Fin k)+2)*y (a+(j.val : Fin k)+1)
def resp {k h : Nat} [NeZero k] (a : Fin k) (x y : A k) : A h × A h := (bil a x y, bil a (tri x) (tri y))
def win {k : Nat} [NeZero k] (a : Fin k) (t : Nat) (x : A k) : A t := fun j => x (a + (j.val : Fin k))

def dif {k : Nat} [NeZero k] : A k →ₗ[F] A k := LinearMap.id + sh 1

def Closed {k : Nat} [NeZero k] (S : Submodule F (A k)) :=
  ∀ (d : Fin k) (x : A k), x ∈ S → sh d x ∈ S

theorem sh_sh {k : Nat} [NeZero k] (d e : Fin k) (x : A k) : sh d (sh e x) = sh (d+e) x := by
  funext i
  exact congrArg x (add_assoc i d e)

theorem comm_all {k : Nat} [NeZero k] (P : A k →ₗ[F] A k)
    (hp : ∀ w, P (sh (-1) w) = sh (-1) (P w)) (d : Fin k) (x : A k) :
    P (sh d x) = sh d (P x) := by
  have H : ∀ m : ℕ, P (sh (-(m : Fin k)) x) = sh (-(m : Fin k)) (P x) := by
    intro m
    induction m with
    | zero => simp [sh]
    | succ m ih =>
      have E : -((m+1 : ℕ) : Fin k) = -1 + -(m : Fin k) := by push_cast; abel
      rw [E, ← sh_sh, hp, ih, sh_sh]
  simpa using H (-d).val

theorem rm_mem {k : Nat} [NeZero k] {S : Submodule F (A k)} (hs : Closed S) {x : A k}
    (hx : x ∈ S) : rm x ∈ S := S.add_mem (S.add_mem hx (hs _ _ hx)) (hs _ _ hx)

theorem tri_mem {k : Nat} [NeZero k] {S : Submodule F (A k)} (hs : Closed S) {x : A k}
    (hx : x ∈ S) : tri x ∈ S := S.add_mem (S.add_mem (hs _ _ hx) (hs _ _ hx)) (hs _ _ hx)

theorem sh_inj {k : Nat} [NeZero k] (d : Fin k) : Function.Injective (sh d) := by
  intro x y H
  funext i
  simpa [sh] using congrFun H (i-d)

theorem period_iter {k : Nat} [NeZero k] {x : A k} (d : Fin k) (H : ∀ i, x (i+d) = x i)
    (m : Nat) (i : Fin k) : x (i + (m : Fin k) * d) = x i := by
  induction m with
  | zero => simp
  | succ m ih => simpa only [Nat.cast_succ, add_mul, one_mul, ← add_assoc, H] using ih

theorem rm_inj {k : Nat} [NeZero k] (hk : k % 3 ≠ 0) : Function.Injective (rm (k := k)) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have H (i : Fin k) : x i + x (i + -1) + x (i + -2) = 0 := congrFun hx i
  have per (i : Fin k) : x (i+3) = x i := by
    have A := H (i+3)
    have B := H (i+2)
    rw [show i+3+-1=i+2 by ring, show i+3+-2=i+1 by ring] at A
    rw [show i+2+-1=i+1 by ring, show i+2+-2=i by ring] at B
    linear_combination A - B
  obtain ⟨m,hm⟩ : ∃ m : ℕ, (m : Fin k) * 3 = 1 := by
    by_cases he : k % 3 = 2
    · refine ⟨(k+1)/3, ?_⟩
      have e : (k+1)/3*3 = k+1 := by omega
      simpa using congrArg (fun a : Nat => (a : Fin k)) e
    · refine ⟨(k+k+1)/3, ?_⟩
      have e : (k+k+1)/3*3 = k+k+1 := by omega
      simpa using congrArg (fun a : Nat => (a : Fin k)) e
  have per1 (i : Fin k) : x (i+1) = x i := hm ▸ period_iter 3 per m i
  have const (i : Fin k) : x i = x 0 := by simpa using period_iter 1 per1 i.val 0
  funext i
  have e := H 0
  rw [const (0 + -1), const (0 + -2), ZModModule.add_self, zero_add] at e
  exact (const i).trans e

theorem tri_inj {k : Nat} [NeZero k] (hk : k % 3 ≠ 0) : Function.Injective (tri (k := k)) := by
  have e (x : A k) : tri x = sh (-1) (rm x) := by
    funext i
    change x (i+-1) + x (i+-2) + x (i+-3) = x (i+-1) + x (i+-1+-1) + x (i+-1+-2)
    rw [show i+-1+-1=i+-2 by ring, show i+-1+-2=i+-3 by ring]
  intro x y h
  rw [e, e] at h
  exact rm_inj hk (sh_inj _ h)

theorem onto_sub {k : Nat} (S : Submodule F (A k)) (f : A k →ₗ[F] A k)
    (hf : ∀ x ∈ S, f x ∈ S) (hi : ∀ x ∈ S, f x = 0 → x = 0) (y : A k) (hy : y ∈ S) :
    ∃ x ∈ S, f x = y := by
  let g := f.restrict hf
  have hg : Function.Injective g := LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr (by
    intro z hz
    exact Subtype.ext (hi z z.property (congrArg Subtype.val hz))))
  obtain ⟨x,hx⟩ := LinearMap.surjective_of_injective hg ⟨y,hy⟩
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

private theorem win_next {k : Nat} [NeZero k] (S : Submodule F (A k))
    (hs : ∀ (d : Fin k) (x : A k), x ∈ S → (fun i => x (i + d)) ∈ S)
    (a : Fin k) (t : Nat) (ht : t < Module.finrank F S) :
    ∃ z : S, win a t z.val = 0 ∧ z.val (a + (t : Fin k)) ≠ 0 := by
  classical
  have hcard : Fintype.card (A t) < Fintype.card S := by
    rw [Module.card_eq_pow_finrank (K := F) (V := S)]
    simpa [A, F, Fintype.card_fun, ZMod.card] using Nat.pow_lt_pow_right (by decide : 1 < 2) ht
  obtain ⟨x, y, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun x : S => win a t x.val) hcard
  let z : S := x - y
  have hprefix (i : Fin t) : z.val (a + (i.val : Fin k)) = 0 :=
    sub_eq_zero.mpr (congrFun heq i)
  by_contra h
  have step (v : S) (hv : win a t v.val = 0) : v.val (a + (t : Fin k)) = 0 := by
    by_contra hn
    exact h ⟨v, hv, hn⟩
  have hall (n : Nat) : z.val (a + (n : Fin k)) = 0 := by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hn : n < t
      · exact hprefix ⟨n, hn⟩
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hn)
        let v : S := ⟨fun i => z.val (i + (d : Fin k)), hs _ _ z.property⟩
        have hv : win a t v.val = 0 := by
          funext j
          change z.val (a + (j.val : Fin k) + (d : Fin k)) = 0
          simpa only [Nat.cast_add, add_assoc] using ih (j.val + d) (Nat.add_lt_add_right j.isLt d)
        simpa only [v, Nat.cast_add, add_assoc] using step v hv
  apply hne
  apply sub_eq_zero.mp
  apply Subtype.ext
  funext i
  change z.val i = 0
  simpa using hall (i - a).val

theorem win_surj {k : Nat} [NeZero k] (S : Submodule F (A k))
    (hs : ∀ (d : Fin k) (x : A k), x ∈ S → (fun i => x (i + d)) ∈ S)
    (a : Fin k) (t : Nat) (ht : t ≤ Module.finrank F S) :
    Function.Surjective (fun x : S => win a t x.val) := by
  induction t with
  | zero => exact fun b => ⟨0, funext fun i => Fin.elim0 i⟩
  | succ t ih =>
    intro b
    obtain ⟨x, hx⟩ := ih (by omega) (fun i => b i.castSucc)
    obtain ⟨z, hz, hn⟩ := win_next S hs a t ht
    have hone : ∀ q : F, q ≠ 0 → q = 1 := by decide
    let c := b (Fin.last t) - x.val (a + (t : Fin k))
    refine ⟨x + c • z, ?_⟩
    funext j
    change x.val (a + (j.val : Fin k)) + c * z.val (a + (j.val : Fin k)) = b j
    by_cases hj : j.val < t
    · let i : Fin t := ⟨j.val, hj⟩
      have hzi : z.val (a + (j.val : Fin k)) = 0 := congrFun hz i
      rw [hzi, mul_zero, add_zero]
      exact congrFun hx i
    · have hlast : j = Fin.last t := Fin.ext (by have := j.isLt; change j.val = t; omega)
      subst j
      change x.val (a + (t : Fin k)) + c * z.val (a + (t : Fin k)) = b (Fin.last t)
      rw [hone _ hn, mul_one]
      dsimp [c]
      abel

theorem win_inj {k : Nat} [NeZero k] (S : Submodule F (A k))
    (hs : ∀ (d : Fin k) (x : A k), x ∈ S → (fun i => x (i + d)) ∈ S)
    (a : Fin k) : Function.Injective (fun x : S => win a (Module.finrank F S) x.val) := by
  classical
  apply (win_surj S hs a _ le_rfl).injective_of_finite
  apply Fintype.equivOfCardEq
  rw [Module.card_eq_pow_finrank (K := F) (V := S)]
  simp [A]

theorem codec {W Y : Type*} [AddCommGroup Y] {m b : Nat} (v₀ : W)
    (f : W → W → Y) (label : W → A m) (hs : Function.Surjective label)
    (hc : ∀ u u', label u = label u' ↔
      ∀ v, f u v - f u v₀ = f u' v - f u' v₀) :
    (∃ (send : W → A b) (offset : W → Y) (finish : A b → W → Y),
      ∀ u v, f u v = offset u + finish (send u) v) ↔ m ≤ b := by
  classical
  choose rep hrep using hs
  have cardA (k : Nat) : Fintype.card (A k) = 2 ^ k := by
    simp [A, F, ZMod.card]
  constructor
  · rintro ⟨send, offset, finish, hf⟩
    have hinj : Function.Injective (fun x => send (rep x)) := by
      intro x y hxy
      change send (rep x) = send (rep y) at hxy
      rw [← hrep x, ← hrep y]
      apply (hc _ _).2
      intro v
      simp only [hf, hxy, add_sub_add_left_eq_sub]
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [cardA, cardA] at hcard
    exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : Nat))).1 hcard
  · intro hmb
    obtain ⟨e⟩ : Nonempty (A m ↪ A b) := Function.Embedding.nonempty_of_card_le (by
      rw [cardA, cardA]
      exact (pow_le_pow_iff_right₀ (by decide : 1 < (2 : Nat))).2 hmb)
    refine ⟨fun u => e (label u), fun u => f u v₀,
      fun c v => f (rep (Function.invFun e c)) v - f (rep (Function.invFun e c)) v₀, ?_⟩
    intro u v
    dsimp only
    rw [Function.leftInverse_invFun e.injective (label u)]
    rw [← (hc u (rep (label u))).1 (hrep _).symm v]
    abel

def strip {k : Nat} [NeZero k] (a : Fin k) (l : ℕ) (x : A k) :=
  ∀ j : ℕ, j < l → x (a + (j : Fin k) + 1) = 0

theorem recover {k : Nat} [NeZero k] (a : Fin k) (l : ℕ) (hl : 3 ≤ l) (x : A k) :
    strip a l x ∧ strip a l (tri x) ↔ win (a-2) (l+3) x = 0 := by
  let f (i : ℕ) := x (a-2+(i : Fin k))
  have e (i : ℕ) : x (a+(i : Fin k)+1) = f (i+3) := by
    dsimp [f]; congr 1; push_cast; ring
  have g (i : ℕ) : (tri x) (a+(i : Fin k)+1) = f (i+2) + f (i+1) + f i := by
    change x (a+↑i+1+-1) + x (a+↑i+1+-2) + x (a+↑i+1+-3) = _
    dsimp [f]; push_cast
    ring_nf
  change (∀ i : ℕ, i < l → x (a+↑i+1) = 0) ∧
    (∀ i : ℕ, i < l → (tri x) (a+↑i+1) = 0) ↔ _
  simp only [e, g]
  constructor
  · rintro ⟨hp,hq⟩
    have z2 := hq 2 (by omega)
    have z1 := hq 1 (by omega)
    have z0 := hq 0 (by omega)
    have h3 : f 3 = 0 := hp 0 (by omega)
    have h4 : f 4 = 0 := hp 1 (by omega)
    change f 4 + f 3 + f 2 = 0 at z2
    change f 3 + f 2 + f 1 = 0 at z1
    change f 2 + f 1 + f 0 = 0 at z0
    simp only [h4,h3,zero_add] at z2
    simp only [h3,z2,zero_add] at z1
    simp only [z1,z2,zero_add] at z0
    funext j
    change f j.val = 0
    by_cases hj : j.val < 3
    · interval_cases q : j.val <;> assumption
    · have q : j.val - 3 + 3 = j.val := by omega
      exact q ▸ hp (j.val-3) (by have := j.isLt; omega)
  · intro h
    have H (i : ℕ) (hi : i < l+3) : f i = 0 := congrFun h ⟨i,hi⟩
    constructor
    · intro i hi; exact H _ (by omega)
    · intro i hi; simp only [H (i+2) (by omega), H (i+1) (by omega), H i (by omega), zero_add]

theorem pairs {k : Nat} [NeZero k] (T : Submodule F (A k)) (ht : Closed T)
    (hr : 2 ≤ Module.finrank F T) (i : Fin k) (p q : F) :
    ∃ y ∈ T, y (i+1) = p ∧ y (i+2) = q := by
  obtain ⟨y,hy⟩ := win_surj T ht (i+1) 2 hr ![p,q]
  refine ⟨y,y.property,?_,?_⟩
  · simpa [win] using congrFun hy 0
  · have eq : i+1+(1 : Fin k) = i+2 := by ring
    simpa [win, eq] using congrFun hy 1

theorem bil_large {k h : Nat} [NeZero k] (hh : 0 < h) (T : Submodule F (A k)) (ht : Closed T)
    (hr : 2 ≤ Module.finrank F T) (a : Fin k) (x : A k) :
    (∀ y ∈ T, bil (h := h) a x y = 0) ↔ strip a (h+1) x := by
  have eq (j : ℕ) : a+((j+1 : ℕ) : Fin k)+1 = a+(j : Fin k)+2 := by push_cast; ring
  constructor
  · intro H
    have each (j : Fin h) : x (a+(j.val : Fin k)+1) = 0 ∧ x (a+(j.val : Fin k)+2) = 0 := by
      obtain ⟨y,hy,e,f⟩ := pairs T ht hr (a+(j.val : Fin k)) 0 1
      obtain ⟨z,hz,g,i⟩ := pairs T ht hr (a+(j.val : Fin k)) 1 0
      exact ⟨by simpa [bil,e,f] using congrFun (H _ hy) j,
        by simpa [bil,g,i] using congrFun (H _ hz) j⟩
    intro j hj
    by_cases hj' : j < h
    · exact (each ⟨j,hj'⟩).1
    · have e : j-1+1 = j := by omega
      rw [← e,eq]
      exact (each ⟨j-1,by omega⟩).2
  · intro H y _hy
    funext j
    have H₂ := H (j.val+1) (by have := j.isLt; omega)
    rw [eq] at H₂
    simp [bil,H₂,H j.val (by have := j.isLt; omega)]

theorem bil_small {k h : Nat} [NeZero k] (T : Submodule F (A k))
    (hone : (fun _ => (1 : F)) ∈ T) (hc : ∀ y ∈ T, ∀ i, y i = y 0)
    (a : Fin k) (x : A k) :
    (∀ y ∈ T, bil (h := h) a x y = 0) ↔ strip a h (dif x) := by
  have e (i : Fin k) : i+1+1 = i+2 := by ring
  constructor
  · intro H j hj
    have he := congrFun (H _ hone) ⟨j,hj⟩
    change x (a+↑j+1) + x (a+↑j+1+1) = 0
    simpa [bil,e] using he
  · intro H y hy
    funext j
    have he := H j j.isLt
    change x (a+↑j.val+1) + x (a+↑j.val+1+1) = 0 at he
    rw [e] at he
    change _ * y _ + _ * y _ = 0
    rw [hc y hy (a+↑j.val+1), hc y hy (a+↑j.val+2), ← add_mul, he, zero_mul]

theorem constants {k : Nat} [NeZero k] (T : Submodule F (A k)) (ht : Closed T)
    (hr : Module.finrank F T = 1) :
    (fun _ => (1 : F)) ∈ T ∧ ∀ y ∈ T, ∀ i, y i = y 0 := by
  have det (a : Fin k) (x : A k) (hx : x ∈ T) (hz : x a = 0) : x = 0 := by
    have hi := win_inj T ht a
    rw [hr] at hi
    exact congrArg Subtype.val (hi (a₁ := ⟨x,hx⟩) (a₂ := 0) (by
      funext j; have hj : j.val = 0 := by omega
      simpa [win,hj] using hz))
  have full (x : A k) (hx : x ∈ T) (hn : x ≠ 0) (i : Fin k) : x i = 1 := by
    have bit : ∀ b : F, b ≠ 0 → b = 1 := by decide
    exact bit _ (fun e => hn (det _ _ hx e))
  obtain ⟨y,hy⟩ := win_surj T ht 0 1 (by omega) (fun _ => 1)
  have head : (y : A k) 0 = 1 := by simpa [win] using congrFun hy 0
  have ne : (y : A k) ≠ 0 := by intro h; simp [h] at head
  exact ⟨(funext (full y y.property ne)) ▸ y.property, fun x hx i => by
    by_cases hn : x = 0
    · simp [hn]
    · rw [full x hx hn i,full x hx hn 0]⟩

theorem resp_split {k h : Nat} [NeZero k] (hk : k % 3 ≠ 0)
    (T : Submodule F (A k)) (ht : Closed T) (a : Fin k) (x : A k) :
    (∀ y ∈ T, resp (h := h) a x y = 0) ↔
    (∀ y ∈ T, bil (h := h) a x y = 0) ∧ (∀ y ∈ T, bil (h := h) a (tri x) y = 0) := by
  constructor
  · intro H
    refine ⟨fun y hy => congrArg Prod.fst (H y hy), ?_⟩
    intro y hy
    obtain ⟨z,hz,rfl⟩ := onto_sub T tri (fun _ => tri_mem ht)
      (fun _ _ e => tri_inj hk (e.trans tri.map_zero.symm)) y hy
    exact congrArg Prod.snd (H z hz)
  · rintro ⟨p,q⟩ y hy
    exact Prod.ext (p y hy) (q (tri y) (tri_mem ht hy))

theorem dif_tri {k : Nat} [NeZero k] (x : A k) : dif (tri x) = tri (dif x) := by
  funext i
  change (x (i+-1) + x (i+-2) + x (i+-3)) +
    (x (i+1+-1) + x (i+1+-2) + x (i+1+-3)) =
    (x (i+-1) + x (i+-1+1)) + (x (i+-2) + x (i+-2+1)) + (x (i+-3) + x (i+-3+1))
  ring_nf

theorem dif_mem {k : Nat} [NeZero k] {S : Submodule F (A k)} (hs : Closed S)
    {x : A k} (hx : x ∈ S) : dif x ∈ S := S.add_mem hx (hs _ _ hx)

theorem dif_ker {k : Nat} [NeZero k] {S : Submodule F (A k)}
    (hc : (fun _ => (1 : F)) ∉ S) (x : A k) (hx : x ∈ S) (hz : dif x = 0) : x = 0 := by
  have H (i : Fin k) : x i + x (i+1) = 0 := congrFun hz i
  have per (i : Fin k) : x (i+1) = x i := by
    have bit : ∀ p q : F, p + q = 0 → q = p := by decide
    exact bit _ _ (H i)
  have eq (i : Fin k) : x i = x 0 := by simpa using period_iter 1 per i.val 0
  have bit : ∀ p : F, p = 0 ∨ p = 1 := by decide
  obtain h|h := bit (x 0)
  · exact funext (fun i => (eq i).trans h)
  · exact False.elim (hc ((funext fun i => (eq i).trans h) ▸ hx))

theorem resp_sub {k h : Nat} [NeZero k] (a : Fin k) (x z y : A k) :
    resp (h := h) a (x-z) y = resp a x y - resp a z y := by
  apply Prod.ext <;> funext j <;> simp [resp,bil,map_sub] <;> ring

theorem short_win {k : Nat} [NeZero k] (S : Submodule F (A k)) (hs : Closed S)
    (a : Fin k) (t : ℕ) (x : A k) (hx : x ∈ S) :
    win a (min (Module.finrank F S) t) x = 0 ↔ win a t x = 0 := by
  by_cases hl : t ≤ Module.finrank F S
  · rw [min_eq_right hl]
  · rw [min_eq_left (by omega)]
    constructor
    · intro H
      have e := win_inj S hs a (a₁ := ⟨x,hx⟩) (a₂ := 0) H
      have h : x = 0 := congrArg Subtype.val e
      rw [h]; rfl
    · intro H
      funext j
      exact congrFun H ⟨j.val, by have := j.isLt; omega⟩

theorem win_eq {k : Nat} [NeZero k] (a : Fin k) (t : ℕ) (x z : A k) :
    win a t x = win a t z ↔ win a t (x-z) = 0 := by
  rw [← sub_eq_zero]; rfl

theorem bridge {k h : Nat} [NeZero k] (a : Fin k) (t b : ℕ)
    (S T : Submodule F (A k)) (hs : Closed S) (D : A k →ₗ[F] A k)
    (s r : A k → A k) (smem : ∀ u, D (s u) ∈ S) (rmem : ∀ v, r v ∈ T)
    (sonto : ∀ z ∈ S, ∃ u, D (s u) = z) (ronto : ∀ z ∈ T, ∃ v, r v = z)
    (ht : ∀ x, (∀ y ∈ T, resp (h := h) a x y = 0) ↔ win (a-2) t (D x) = 0)
    (f : A k → A k → A h × A h) (off : A k → A h × A h)
    (hf : ∀ u v, f u v - f u 0 = resp a (s u) (r v) + off v) :
    (∃ (send : A k → A b) (offset : A k → A h × A h) (finish : A b → A k → A h × A h),
      ∀ u v, f u v = offset u + finish (send u) v) ↔ min (Module.finrank F S) t ≤ b := by
  let m := min (Module.finrank F S) t
  let label (u : A k) := win (a-2) m (D (s u))
  apply codec 0 f label
  · intro z
    obtain ⟨x,hx⟩ := win_surj S hs (a-2) m (min_le_left ..) z
    obtain ⟨u,hu⟩ := sonto x x.property
    exact ⟨u,by simpa only [label,hu] using hx⟩
  · intro u w
    change win _ m _ = win _ m _ ↔ _
    rw [win_eq, short_win S hs _ t _ (S.sub_mem (smem u) (smem w)), ← map_sub, ← ht]
    simp only [hf, add_left_inj, resp_sub, sub_eq_zero]
    exact ⟨fun H v => H _ (rmem v), fun H y hy => by
      obtain ⟨v,rfl⟩ := ronto _ hy
      exact H v⟩

theorem pricing {k h : Nat} [NeZero k] (hk : k % 3 ≠ 0) (hh : 3 ≤ h)
    (P : A k →ₗ[F] A k) (hid : ∀ w, P (P w) = P w)
    (hp : ∀ w, P (sh (-1) w) = sh (-1) (P w)) (hn : Module.finrank F (LinearMap.range P) < k)
    (a : Fin k) (out : A k → A h × A h)
    (ho : ∀ x y, out (x+y) - out x - (out y - out 0) = resp a (rm x) (rm y)) (b : ℕ) :
    (∃ (send : A k → A b) (offset : A k → A h × A h) (finish : A b → A k → A h × A h),
      ∀ u v, out (P u + (v-P v)) = offset u + finish (send u) v) ↔
      min (Module.finrank F (LinearMap.range P))
        (h + (if Module.finrank F (LinearMap.range P) + 1 = k then 3 else 4)) ≤ b := by
  let S := LinearMap.range P
  let T := LinearMap.ker P
  let n := Module.finrank F S
  have rank : n + Module.finrank F T = k := by
    simpa [n,S,T,A] using P.finrank_range_add_finrank_ker
  have hs : Closed S := by
    rintro d x ⟨w,rfl⟩
    exact ⟨sh d w, comm_all P hp d w⟩
  have ht : Closed T := by
    intro d x hx
    change P x = 0 at hx
    change P (sh d x) = 0
    rw [comm_all P hp,hx,map_zero]
  let D : A k →ₗ[F] A k := if n+1 = k then dif else LinearMap.id
  let t := h + (if n+1 = k then 3 else 4)
  have dm (x : A k) (hx : x ∈ S) : D x ∈ S := by
    by_cases he : n+1 = k
    · simpa [D,he] using dif_mem hs hx
    · simpa [D,he] using hx
  have don (z : A k) (hz : z ∈ S) : ∃ x ∈ S, D x = z := by
    by_cases he : n+1 = k
    · have hc := (constants T ht (by omega)).1
      have hnot : (fun _ => (1 : F)) ∉ S := by
        rintro ⟨w,hw⟩
        change P (fun _ => (1 : F)) = 0 at hc
        have e := hid w
        rw [hw,hc] at e
        have q := congrFun e 0
        exact (zero_ne_one (α := F)) q
      simpa [D,he] using onto_sub S dif (fun _ => dif_mem hs) (dif_ker hnot) z hz
    · exact ⟨z,hz, by simp [D,he]⟩
  have detect (x : A k) : (∀ y ∈ T, resp (h := h) a x y = 0) ↔ win (a-2) t (D x) = 0 := by
    rw [resp_split hk T ht]
    by_cases he : n+1 = k
    · obtain ⟨ho,hc⟩ := constants T ht (by omega)
      rw [bil_small T ho hc,bil_small T ho hc,dif_tri]
      have et : t = h+3 := by simp [t,he]
      rw [et]
      simpa [D,he] using recover a h hh (dif x)
    · have hd : 2 ≤ Module.finrank F T := by change n < k at hn; omega
      rw [bil_large (by omega) T ht hd,bil_large (by omega) T ht hd]
      have et : t = h+1+3 := by simp [t,he]
      rw [et]
      simpa [D,he] using recover a (h+1) (by omega) x
  have rc (v : A k) : v - P v ∈ T := by
    change P (v - P v) = 0
    rw [map_sub, hid, sub_self]
  refine bridge a t b S T hs D (fun u => rm (P u)) (fun v => rm (v-P v))
    (fun u => dm _ (rm_mem hs ⟨u,rfl⟩)) (fun v => rm_mem ht (rc v)) ?_ ?_ detect
    (fun u v => out (P u + (v-P v))) (fun v => out (v-P v) - out 0) ?_
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := don _ hz
    obtain ⟨y,⟨u,hu⟩,hy⟩ := onto_sub S rm (fun _ => rm_mem hs)
      (fun _ _ e => rm_inj hk (e.trans rm.map_zero.symm)) x hx
    exact ⟨u, by rw [hu,hy]⟩
  · intro z hz
    obtain ⟨y,hy,he⟩ := onto_sub T rm (fun _ => rm_mem ht)
      (fun _ _ e => rm_inj hk (e.trans rm.map_zero.symm)) z hz
    change P y = 0 at hy
    exact ⟨y,by simpa only [hy,sub_zero] using he⟩
  · intro u v
    simp only [map_zero,sub_zero,add_zero]
    exact (sub_eq_iff_eq_add.mp (ho (P u) (v-P v)))

private theorem backIx {k : Nat} [NeZero k] (hk : 0 < k) (s : Nat) (i : Fin k) :
    (⟨(i.val + k - s % k) % k, Nat.mod_lt _ hk⟩ : Fin k) = i + -(s : Fin k) := by
  rw [← sub_eq_add_neg]
  apply Fin.ext
  change (i.val + k - s % k) % k = ((k - s % k) + i.val) % k
  have := Nat.mod_lt s hk
  congr 1
  omega

private theorem fwdIx {k : Nat} [NeZero k] (hk : 0 < k) (s : Nat) (i : Fin k) :
    (⟨(i.val + s) % k, Nat.mod_lt _ hk⟩ : Fin k) = i + (s : Fin k) := by
  apply Fin.ext
  change (i.val + s) % k = (i.val + s % k) % k
  simp

private theorem winIx {k : Nat} [NeZero k] (hk : 0 < k) (a s : Nat) :
    (⟨(a + s) % k, Nat.mod_lt _ hk⟩ : Fin k) = (a : Fin k) + (s : Fin k) := by
  exact Nat.cast_add a s

theorem oneRot {k : Nat} [NeZero k] (hk : 0 < k) (w : A k) :
    let W := Fin k → ZMod 2
    let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (s : Nat) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
    rot 1 w = sh (-1) w := by
  funext i
  exact congrArg w (backIx hk 1 i)

private def chanMix {k : Nat} [NeZero k] (d : Fin k) : A k →ₗ[F] A k :=
  LinearMap.id + sh d + sh (-d)

private theorem shVal {k : Nat} [NeZero k] (d i : Fin k) (x : A k) : sh d x i = x (i + d) := rfl

private theorem mixOne {k : Nat} [NeZero k] (x : A k) : chanMix 1 (sh (-1) x) = rm x := by
  funext i
  simp only [chanMix, rm, LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply, shVal, add_assoc]
  ring_nf

private theorem mixTwo {k : Nat} [NeZero k] (x : A k) : chanMix 2 (sh (-3) x) = tri (rm x) := by
  funext i
  simp only [chanMix, rm, tri, LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply, shVal, add_assoc]
  ring_nf
  rw [show (3 : F) = 1 by decide, show (2 : F) = 0 by decide]
  ring

private def chanStep {k : Nat} [NeZero k] (x : A k) (i : Fin k) :=
  x i + (1 + x (i + 1)) * x (i + 2)

private theorem channelPol {k h : Nat} [NeZero k] (a : Fin k) (L D : A k →ₗ[F] A k)
    (t c x y : A k) :
    let f := fun w => win a h (chanStep (L w + t) + D w + c)
    f (x+y) - f x - (f y - f 0) = bil a (L x) (L y) := by
  funext j
  simp only [Pi.sub_apply, win, chanStep, Pi.add_apply, map_add, map_zero, zero_add, Pi.zero_apply, bil]
  ring

theorem channel {k h : Nat} [NeZero k] (hk : 0 < k) (start : Nat) (row col c₁ c₂ x y : A k) :
    let W := Fin k → ZMod 2
    let Y := (Fin h → ZMod 2) × (Fin h → ZMod 2)
    let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
    let rot := fun (s : Nat) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
    let mix := fun (d : Nat) (x : W) (i : Fin k) =>
      x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
    let step := fun (x : W) (i : Fin k) =>
      x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
    let window := fun (x : W) (j : Fin h) => x (ix (start + j.val))
    let out := fun (w : W) =>
      ((window (step (mix 1 (rot 1 w + row)) + w + c₁),
        window (step (mix 2 (rot 3 w + col)) + rot 4 w + c₂)) : Y)
    out (x+y) - out x - (out y - out 0) = resp (start : Fin k) (rm x) (rm y) := by
  intro W Y ix rot mix step window out
  have hr (s : Nat) (w : W) : rot s w = sh (-(s : Fin k)) w := by
    funext i
    exact congrArg w (backIx hk s i)
  have hm (d : Nat) (w : W) : mix d w = chanMix (d : Fin k) w := by
    funext i
    change w i + w (ix (i.val + d)) + w (ix (i.val + k - d % k)) =
      w i + w (i + (d : Fin k)) + w (i + -(d : Fin k))
    rw [show ix (i.val + d) = _ from fwdIx hk d i,
      show ix (i.val + k - d % k) = _ from backIx hk d i]
  have h₁ (w : W) : mix 1 (rot 1 w + row) = rm w + chanMix 1 row := by
    simp only [hm, hr, Nat.cast_one, map_add, mixOne]
  have h₂ (w : W) : mix 2 (rot 3 w + col) = tri (rm w) + chanMix 2 col := by
    simp only [hm, hr, Nat.cast_ofNat, map_add, mixTwo]
  have hs (w : W) : step w = chanStep w := by
    funext i
    change w i + (1 + w (ix (i.val + 1))) * w (ix (i.val + 2)) =
      w i + (1 + w (i + 1)) * w (i + 2)
    rw [show ix (i.val + 1) = i + 1 from fwdIx hk 1 i,
      show ix (i.val + 2) = i + 2 from fwdIx hk 2 i]
  have hw (w : W) : window w = win (start : Fin k) h w := by
    funext j
    exact congrArg w (winIx hk start j.val)
  simp only [out, h₁, h₂]
  simp only [hr, hs, hw, Nat.cast_ofNat, resp]
  apply Prod.ext
  · exact channelPol (start : Fin k) rm LinearMap.id (chanMix 1 row) c₁ x y
  · exact channelPol (start : Fin k) (tri.comp rm) (sh (-4)) (chanMix 2 col) c₂ x y

end PEqualNP.Outside.L_meta_25626

theorem PEqualNP.Outside.L_meta_25626 : ∀ (k h : Nat) (hk : 0 < k), k % 3 ≠ 0 → 3 ≤ h → h ≤ k →
  let W := Fin k → ZMod 2
  let Y := (Fin h → ZMod 2) × (Fin h → ZMod 2)
  let ix := fun i : Nat => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : Nat) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (d : Nat) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + d)) + x (ix (i.val + k - d % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  ∀ (P : W →ₗ[ZMod 2] W), (∀ w, P (P w) = P w) →
    (∀ w, P (rot 1 w) = rot 1 (P w)) →
    let n := Module.finrank (ZMod 2) (LinearMap.range P)
    0 < n → n < k →
    ∀ (start : Nat) (row col c₁ c₂ : W) (b : Nat),
      let window := fun (x : W) (j : Fin h) => x (ix (start + j.val))
      let out := fun (w : W) =>
        ((window (step (mix 1 (rot 1 w + row)) + w + c₁),
          window (step (mix 2 (rot 3 w + col)) + rot 4 w + c₂)) : Y)
      (∃ (send : W → (Fin b → ZMod 2)) (offset : W → Y)
         (finish : (Fin b → ZMod 2) → W → Y), ∀ u v : W,
         out (P u + (v - P v)) = offset u + finish (send u) v) ↔
        min n (h + (if n + 1 = k then 3 else 4)) ≤ b := by
  intro k h hk hk3 hh _ W Y ix rot mix step P hid hrot n _ hn start row col c₁ c₂ b window out
  let : NeZero k := ⟨hk.ne'⟩
  refine PEqualNP.Outside.L_meta_25626.pricing hk3 hh P hid ?_ hn (ix start) out ?_ b
  · intro w
    have e (z : W) : rot 1 z = PEqualNP.Outside.L_meta_25626.sh (-1) z :=
      PEqualNP.Outside.L_meta_25626.oneRot hk z
    simpa only [← e] using hrot w
  · exact PEqualNP.Outside.L_meta_25626.channel hk start row col c₁ c₂
