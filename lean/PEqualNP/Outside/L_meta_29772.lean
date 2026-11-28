import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29772_aux

section Differences

variable {W W' R : Type} [AddCommGroup W] [AddCommGroup W'] [CommRing R]

def delta (f : W → R) (u x : W) : R := f (x + u) - f x

def differences (f : W → R) (directions : List W) : W → R :=
  directions.foldl delta f

def degree : ℕ → (W → R) → Prop
  | 0, f => ∀ u x, delta f u x = 0
  | n + 1, f => ∀ u, degree n (delta f u)

theorem degree_zero_const {f : W → R} (h : degree 0 f) (x : W) : f x = f 0 := by
  have hx := h x 0
  simpa [delta, sub_eq_zero] using hx

theorem delta_add (f g : W → R) (u : W) :
    delta (fun x => f x + g x) u = fun x => delta f u x + delta g u x := by
  funext x
  unfold delta
  ring

theorem delta_sub (f g : W → R) (u : W) :
    delta (fun x => f x - g x) u = fun x => delta f u x - delta g u x := by
  funext x
  unfold delta
  ring

theorem delta_scale (c : R) (f : W → R) (u : W) :
    delta (fun x => c * f x) u = fun x => c * delta f u x := by
  funext x
  unfold delta
  ring

theorem delta_shift (f : W → R) (u v : W) :
    delta (fun x => f (x + v)) u = fun x => delta f u (x + v) := by
  funext x
  simp only [delta, add_right_comm x u v]

theorem delta_mul (f g : W → R) (u : W) :
    delta (fun x => f x * g x) u =
      fun x => delta f u x * g (x + u) + f x * delta g u x := by
  funext x
  unfold delta
  ring

theorem degree_const (n : ℕ) (c : R) : degree n (fun _ : W => c) := by
  induction n generalizing c with
  | zero => intro u x; simp [delta]
  | succ n ih =>
    intro u
    have h : delta (fun _ : W => c) u = fun _ => 0 := by funext x; simp [delta]
    rw [h]
    exact ih 0

theorem degree_add {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_add f g u) x
  | succ n ih =>
    intro u
    rw [delta_add]
    exact ih (hf u) (hg u)

theorem degree_scale {n : ℕ} (c : R) {f : W → R}
    (hf : degree n f) : degree n (fun x => c * f x) := by
  induction n generalizing f with
  | zero => intro u x; simpa [hf u x] using congrFun (delta_scale c f u) x
  | succ n ih =>
    intro u
    rw [delta_scale]
    exact ih (hf u)

theorem degree_shift {n : ℕ} (v : W) {f : W → R}
    (hf : degree n f) : degree n (fun x => f (x + v)) := by
  induction n generalizing f with
  | zero =>
    intro u x
    rw [delta_shift]
    exact hf u (x + v)
  | succ n ih =>
    intro u
    rw [delta_shift]
    exact ih (hf u)

theorem degree_raise {n : ℕ} {f : W → R} (hf : degree n f) : degree (n + 1) f := by
  induction n generalizing f with
  | zero =>
    intro u v x
    change delta f u (x + v) - delta f u x = 0
    rw [hf u (x + v), hf u x, sub_self]
  | succ n ih => exact fun u => ih (hf u)

theorem degree_mul {a b : ℕ} {f g : W → R}
    (hf : degree a f) (hg : degree b g) : degree (a + b) (fun x => f x * g x) := by
  induction a generalizing b f g with
  | zero =>
    have he : (fun x => f x * g x) = fun x => f 0 * g x := by
      funext x
      rw [degree_zero_const hf x]
    simpa only [Nat.zero_add, he] using degree_scale (f 0) hg
  | succ a ia =>
    induction b generalizing f g with
    | zero =>
      have he : (fun x => f x * g x) = fun x => g 0 * f x := by
        funext x
        rw [degree_zero_const hg x, mul_comm]
      simpa only [Nat.add_zero, he] using degree_scale (g 0) hf
    | succ b ib =>
      change degree (a + 1 + b + 1) _
      intro u
      rw [delta_mul]
      have h₁ := ia (hf u) (degree_shift u hg)
      have h₂ := ib hf (hg u)
      rw [show a + (b + 1) = a + 1 + b by omega] at h₁
      exact degree_add h₁ h₂

theorem degree_fold {f : W → R} (us : List W) (n : ℕ)
    (hf : degree (us.length + n) f) : degree n (differences f us) := by
  induction us generalizing f with
  | nil => simpa [differences] using hf
  | cons u us ih =>
    change degree n (differences (delta f u) us)
    apply ih
    rw [show (u :: us).length + n = (us.length + n) + 1 by simp; omega] at hf
    exact hf u

theorem differences_sub (f g : W → R) (us : List W) (x : W) :
    differences (fun y => f y - g y) us x = differences f us x - differences g us x := by
  induction us generalizing f g with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f y - g y) u) us x = _
    rw [delta_sub, ih]
    rfl

theorem differences_zero {f : W → R} (us : List W) {n : ℕ} (hu : us.length = n + 1)
    (hf : degree n f) (x : W) : differences f us x = 0 := by
  induction us generalizing n f with
  | nil => simp at hu
  | cons u us ih =>
    cases n with
    | zero =>
      have hnil : us = [] := List.length_eq_zero_iff.1 (by simpa using hu)
      subst us
      exact hf u x
    | succ n => exact ih (Nat.succ.inj hu) (hf u)

theorem differences_eq_on {S : AddSubgroup W} {f g : W → R} (hfg : ∀ x ∈ S, f x = g x)
    (us : List W) (hu : ∀ u ∈ us, u ∈ S) (x : W) (hx : x ∈ S) :
    differences f us x = differences g us x := by
  induction us generalizing f g with
  | nil => exact hfg x hx
  | cons u us ih =>
    change differences (delta f u) us x = differences (delta g u) us x
    refine ih (fun z hz => ?_) (fun v hv => hu v (List.mem_cons_of_mem _ hv))
    simp only [delta, hfg (z + u) (S.add_mem hz (hu u List.mem_cons_self)), hfg z hz]

theorem differences_comp (p : W →+ W') (c : W') (f : W' → R) (us : List W) (x : W) :
    differences (fun y => f (p y + c)) us x = differences f (us.map p) (p x + c) := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f (p y + c)) u) us x =
      differences (delta f (p u)) (us.map p) (p x + c)
    have hδ : delta (fun y => f (p y + c)) u = fun y => delta f (p u) (p y + c) := by
      funext y
      simp only [delta, map_add, add_right_comm (p y) (p u) c]
    rw [hδ, ih]

end Differences

abbrev Scalar := ZMod 2
abbrev Word (k : ℕ) := Fin k → Scalar
abbrev Query (k : ℕ) := Word k →ₗ[Scalar] Scalar

def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x (index hk (i.val + k - s % k))

def mix {k : ℕ} (hk : 0 < k) (g : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x i + x (index hk (i.val + g)) + x (index hk (i.val + k - g % k))

def step {k : ℕ} (hk : 0 < k) (x : Word k) (i : Fin k) : Scalar :=
  x i + (1 + x (index hk (i.val + 1))) * x (index hk (i.val + 2))

def gap (b : Bool) : ℕ := if b then 2 else 1

def spin (b : Bool) : ℕ := if b then 3 else 1

def linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x)

def namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x + name b)

def firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  step hk (namedInput hk name b x) + rotate hk (if b then 4 else 0) x + c₁ b

def quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) (j : Fin k) : Scalar :=
  linearInput hk b x (index hk (j.val + 1)) * linearInput hk b x (index hk (j.val + 2))

def outputWord {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (x : Word k) (b : Bool) : Word k :=
  step hk (mix hk (gap b) (firstRow hk name c₁ b x)) +
    rotate hk (if b then 7 else 2) x + c₂ b

def topWord {k : ℕ} (hk : 0 < k) (x : Word k) (b : Bool) (i : Fin k) : Scalar :=
  mix hk (gap b) (quadratic hk b x) (index hk (i.val + 1)) *
    mix hk (gap b) (quadratic hk b x) (index hk (i.val + 2))

theorem degree_coord {k : ℕ} (i : Fin k) : degree 1 (fun x : Word k => x i) := by
  intro u v x
  simp only [delta, Pi.add_apply]
  ring

theorem degree_mix {k n : ℕ} (hk : 0 < k) (g : ℕ) (f : Word k → Word k)
    (hf : ∀ i, degree n (fun x => f x i)) (i : Fin k) :
    degree n (fun x => mix hk g (f x) i) :=
  degree_add (degree_add (hf i) (hf _)) (hf _)

theorem mix_sub {k : ℕ} (hk : 0 < k) (g : ℕ) (f h : Word k) (i : Fin k) :
    mix hk g f i - mix hk g h i = mix hk g (f - h) i := by
  simp only [mix, Pi.sub_apply]
  ring

theorem namedInput_eq {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k)
    (i : Fin k) : namedInput hk name b x i = linearInput hk b x i + mix hk (gap b) (name b) i := by
  simp only [namedInput, linearInput, mix, Pi.add_apply]
  ring

theorem degree_linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => linearInput hk b x i) :=
  degree_mix hk _ _ (fun _ => degree_coord _) i

theorem degree_namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => namedInput hk name b x i) := by
  simpa only [namedInput_eq] using
    degree_add (degree_linearInput hk b i) (degree_const 1 (mix hk (gap b) (name b) i))

theorem degree_input_remainder {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 0 (fun x => namedInput hk name b x i - linearInput hk b x i) := by
  simp only [namedInput_eq, add_sub_cancel_left]
  exact degree_const 0 _

theorem degree_quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => quadratic hk b x i) :=
  degree_mul (degree_linearInput hk b _) (degree_linearInput hk b _)

theorem product_remainder {k n : ℕ} {a b a₀ b₀ : Word k → Scalar}
    (hb : degree (n + 1) b) (ha₀ : degree (n + 1) a₀)
    (ha : degree n (fun x => a x - a₀ x)) (hb' : degree n (fun x => b x - b₀ x)) :
    degree (n + (n + 1)) (fun x => (1 + a x) * b x - a₀ x * b₀ x) := by
  have hp := degree_mul (degree_add (degree_const n (1 : Scalar)) ha) hb
  have hq := degree_mul ha₀ hb'
  rw [Nat.add_comm (n + 1) n] at hq
  convert degree_add hp hq using 1
  funext x
  ring

theorem degree_first_remainder {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 1 (fun x => firstRow hk name c₁ b x i - quadratic hk b x i) := by
  have hp := product_remainder (n := 0) (degree_namedInput hk name b (index hk (i.val + 2)))
    (degree_linearInput hk b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 2)))
  have hd := degree_add (degree_add (degree_add (degree_namedInput hk name b i) hp)
    (degree_coord (index hk (i.val + k - (if b then 4 else 0) % k)))) (degree_const 1 (c₁ b i))
  convert hd using 1
  funext x
  simp only [firstRow, step, quadratic, rotate, Pi.add_apply]
  ring

theorem degree_firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => firstRow hk name c₁ b x i) := by
  simpa only [sub_add_cancel] using
    degree_add (degree_raise (degree_first_remainder hk name c₁ b i)) (degree_quadratic hk b i)

theorem degree_output_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 3 (fun x => outputWord hk name c₁ c₂ x b i - topWord hk x b i) := by
  let y := fun x => mix hk (gap b) (firstRow hk name c₁ b x)
  let q := fun x => mix hk (gap b) (quadratic hk b x)
  have hy (j : Fin k) : degree 2 (fun x => y x j) :=
    degree_mix hk _ _ (degree_firstRow hk name c₁ b) j
  have hq (j : Fin k) : degree 2 (fun x => q x j) :=
    degree_mix hk _ _ (degree_quadratic hk b) j
  have hdiff (j : Fin k) : degree 1 (fun x => y x j - q x j) := by
    simpa only [y, q, mix_sub] using
      degree_mix hk (gap b) (fun x => firstRow hk name c₁ b x - quadratic hk b x)
        (degree_first_remainder hk name c₁ b) j
  have hp := product_remainder (n := 1) (hy (index hk (i.val + 2))) (hq (index hk (i.val + 1)))
    (hdiff (index hk (i.val + 1))) (hdiff (index hk (i.val + 2)))
  have hrotate := degree_raise (degree_raise
    (degree_coord (index hk (i.val + k - (if b then 7 else 2) % k))))
  have hd := degree_add (degree_add (degree_add (degree_raise (hy i)) hp) hrotate)
    (degree_const 3 (c₂ b i))
  convert hd using 1
  funext x
  simp only [outputWord, step, topWord, rotate, Pi.add_apply, y, q]
  ring

theorem degree_topWord {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 4 (fun x => topWord hk x b i) :=
  degree_mul (degree_mix hk _ _ (degree_quadratic hk b) _)
    (degree_mix hk _ _ (degree_quadratic hk b) _)

def fourthDifference {m : ℕ} (f : Word m → Scalar) (v : Fin 4 → Word m) : Word m → Scalar :=
  differences f (List.ofFn v)

def IsCubic {k : ℕ} (f : Word k → Scalar) : Prop :=
  ∀ v x, fourthDifference f v x = 0

theorem output_fourth {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool) (i : Fin k)
    (v : Fin 4 → Word k) (x : Word k) :
    fourthDifference (fun y => outputWord hk name c₁ c₂ y b i) v x =
      fourthDifference (fun y => topWord hk y b i) v 0 := by
  have hlen : (List.ofFn v).length = 4 := List.length_ofFn
  have h := differences_zero _ hlen (degree_output_remainder hk name c₁ c₂ b i) x
  rw [differences_sub, sub_eq_zero] at h
  have hc := degree_fold (List.ofFn v) 0 (by simpa [hlen] using degree_topWord hk b i)
  exact h.trans (degree_zero_const hc x)

def queryRun {k d : ℕ} (ask : Fin d → ℕ → Query k) (x : Word k) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

theorem queryRun_one {k : ℕ} (ask : Fin 1 → ℕ → Query k) (x : Word k) :
    queryRun ask x = if ask 0 0 x = 0 then 0 else 1 := by
  simp [queryRun, List.finRange_succ]

def GoodAt {k : ℕ} (hk : 0 < k) (ℓ : Query k) (b : Bool) (i : Fin k) : Prop :=
  ∀ v : Fin 4 → Word k, (∀ e, ℓ (v e) = 0) → fourthDifference (fun x => topWord hk x b i) v 0 = 0

theorem parity_criterion {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k)
    (marked : Bool → Fin k → Prop) :
    (∃ (ask : Fin 1 → ℕ → Query k) (readout : ℕ → Bool → Fin k → Word k → Scalar),
      (∀ h b i, IsCubic (readout h b i)) ∧
      ∀ x b i, marked b i → outputWord hk name c₁ c₂ x b i = readout (queryRun ask x) b i x) ↔
    ∃ ℓ : Query k, ∀ b i, marked b i → GoodAt hk ℓ b i := by
  classical
  constructor
  · rintro ⟨ask, readout, cubic, agree⟩
    refine ⟨ask 0 0, fun b i hm v hv => ?_⟩
    have hfg (x : Word k) (hx : x ∈ (LinearMap.ker (ask 0 0)).toAddSubgroup) :
        outputWord hk name c₁ c₂ x b i = readout 0 b i x := by
      have hz : queryRun ask x = 0 := by
        simp [queryRun_one, show ask 0 0 x = 0 from hx]
      rw [← hz]
      exact agree x b i hm
    have hmem (u : Word k) (hu : u ∈ List.ofFn v) :
        u ∈ (LinearMap.ker (ask 0 0)).toAddSubgroup := by
      obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hu
      exact hv e
    rw [← output_fourth hk name c₁ c₂ b i v 0]
    exact (differences_eq_on hfg _ hmem 0 (zero_mem _)).trans (cubic 0 b i v 0)
  · rintro ⟨ℓ, good⟩
    let K := LinearMap.ker ℓ
    obtain ⟨L, hKL⟩ := K.exists_isCompl
    let p := K.projection L hKL
    have proj_mem (x : Word k) : ℓ (p x) = 0 := by
      change K.projection L hKL x ∈ K
      rw [← Submodule.coe_projectionOnto_apply]
      exact (K.projectionOnto L hKL x).property
    let ask (_ : Fin 1) (_ : ℕ) := ℓ
    let rep (h : ℕ) : Word k := if hr : ∃ z, queryRun ask z = h then Classical.choose hr else 0
    let readout (h : ℕ) (b : Bool) (i : Fin k) (x : Word k) : Scalar :=
      if marked b i then outputWord hk name c₁ c₂ (p x + (rep h - p (rep h))) b i else 0
    refine ⟨ask, readout, fun h b i v x => ?_, fun x b i hm => ?_⟩
    · by_cases hm : marked b i
      · simp only [readout, hm, ↓reduceIte]
        have := differences_comp p.toAddMonoidHom (rep h - p (rep h))
          (fun y => outputWord hk name c₁ c₂ y b i) (List.ofFn v) x
        simp only [LinearMap.toAddMonoidHom_coe, List.map_ofFn] at this
        refine this.trans ?_
        change fourthDifference (fun y => outputWord hk name c₁ c₂ y b i) (p ∘ v) _ = 0
        rw [output_fourth]
        exact good b i hm _ (fun e => proj_mem (v e))
      · simp only [readout, hm, ↓reduceIte]
        exact differences_zero _ List.length_ofFn (degree_const 3 0) x
    · let y := rep (queryRun ask x)
      have hy : queryRun ask y = queryRun ask x := by
        have h : ∃ z, queryRun ask z = queryRun ask x := ⟨x, rfl⟩
        change queryRun ask (if hr : ∃ z, queryRun ask z = queryRun ask x then
          Classical.choose hr else 0) = queryRun ask x
        rw [dite_eq_left h]
        exact Classical.choose_spec h
      have hK : x - y ∈ K := by
        have hxy : ℓ y = ℓ x := by
          simp only [queryRun_one, ask] at hy
          generalize ℓ y = a at hy ⊢
          generalize ℓ x = c at hy ⊢
          revert a c
          decide
        rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
      have hfix : p (x - y) = x - y := Submodule.projection_apply_of_mem_left hKL hK
      have he : p x + (y - p y) = x := calc
        p x + (y - p y) = p (x - y) + y := by rw [map_sub]; abel
        _ = x := by rw [hfix, sub_add_cancel]
      simp only [readout, hm, ↓reduceIte]
      change _ = outputWord hk name c₁ c₂ (p x + (y - p y)) b i
      rw [he]

theorem index_val {k : ℕ} (hk : 0 < k) (i : Fin k) : index hk i.val = i :=
  Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem index_add {k : ℕ} (hk : 0 < k) (n s : ℕ) :
    index hk ((index hk n).val + s) = index hk (n + s) :=
  Fin.ext (Nat.mod_add_mod n k s)

theorem index_period {k : ℕ} (hk : 0 < k) {a b : ℕ} (h : a = b + k) : index hk a = index hk b :=
  Fin.ext (h ▸ Nat.add_mod_right b k)

theorem index_wrap {k : ℕ} (hk : 0 < k) (i : Fin k) {n : ℕ} (h : n = i.val + k) :
    index hk n = i :=
  (index_period hk h).trans (index_val hk i)

theorem index_back {k : ℕ} (hk : 0 < k) {s : ℕ} (hs : s < k) (n : ℕ) :
    index hk ((index hk (n + s)).val + k - s % k) = index hk n := by
  apply Fin.ext
  change ((n + s) % k + k - s % k) % k = n % k
  rw [Nat.mod_eq_of_lt hs, Nat.add_sub_assoc hs.le, Nat.mod_add_mod,
    show n + s + (k - s) = n + k by omega, Nat.add_mod_right]

theorem index_inj {k : ℕ} (hk : 0 < k) {a b : ℕ} (hab : a < b + k) (hba : b < a + k) :
    index hk a = index hk b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h' : a ≡ b [MOD k] := congrArg Fin.val h
  rcases Nat.le_total a b with hle | hle
  · have := Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' hle).1 h') (by omega)
    omega
  · have := Nat.eq_zero_of_dvd_of_lt ((Nat.modEq_iff_dvd' hle).1 h'.symm) (by omega)
    omega

theorem rotate_index {k : ℕ} (hk : 0 < k) {s : ℕ} (hs : s < k) (x : Word k) (n : ℕ) :
    rotate hk s x (index hk (n + s)) = x (index hk n) :=
  congrArg x (index_back hk hs n)

theorem mix_index {k : ℕ} (hk : 0 < k) {g : ℕ} (hg : g < k) (y : Word k) (n : ℕ) :
    mix hk g y (index hk (n + g)) =
      y (index hk (n + g)) + y (index hk (n + g + g)) + y (index hk n) := by
  rw [mix, index_add, index_back hk hg]

def coordinate {k : ℕ} (hk : 0 < k) (n : ℕ) : Query k := LinearMap.proj (index hk n)

def rowTap {k : ℕ} (hk : 0 < k) (n : ℕ) : Query k :=
  coordinate hk n + coordinate hk (n + 1) + coordinate hk (n + 2)

def colTap {k : ℕ} (hk : 0 < k) (n : ℕ) : Query k :=
  coordinate hk n + coordinate hk (n + 2) + coordinate hk (n + 4)

theorem linearInput_row {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (x : Word k) (n : ℕ) :
    linearInput hk false x (index hk (n + 2)) = rowTap hk n x := by
  have h1 : 1 < k := by omega
  rw [linearInput, show gap false = 1 from rfl, show spin false = 1 from rfl,
    mix_index hk h1 _ (n + 1), rotate_index hk h1 x (n + 1), rotate_index hk h1 x (n + 2),
    rotate_index hk h1 x n]
  change x (index hk (n + 1)) + x (index hk (n + 2)) + x (index hk n) =
    x (index hk n) + x (index hk (n + 1)) + x (index hk (n + 2))
  ring

theorem linearInput_col {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (x : Word k) (n : ℕ) :
    linearInput hk true x (index hk (n + 5)) = colTap hk n x := by
  have h2 : 2 < k := by omega
  have h3 : 3 < k := by omega
  rw [linearInput, show gap true = 2 from rfl, show spin true = 3 from rfl,
    mix_index hk h2 _ (n + 3), rotate_index hk h3 x (n + 2), rotate_index hk h3 x (n + 4),
    rotate_index hk h3 x n]
  change x (index hk (n + 2)) + x (index hk (n + 4)) + x (index hk n) =
    x (index hk n) + x (index hk (n + 2)) + x (index hk (n + 4))
  ring

def rowPoly (a b c d e : Scalar) : Scalar := (a * b + b * c + c * d) * (b * c + c * d + d * e)

def colPoly (a b c d e f g : Scalar) : Scalar :=
  (a * b + c * d + e * f) * (b * c + d * e + f * g)

theorem topWord_row {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (x : Word k) (n : ℕ) :
    topWord hk x false (index hk (n + 1)) =
      rowPoly (rowTap hk n x) (rowTap hk (n + 1) x) (rowTap hk (n + 2) x)
        (rowTap hk (n + 3) x) (rowTap hk (n + 4) x) := by
  have hQ (m : ℕ) : quadratic hk false x (index hk (m + 1)) =
      rowTap hk m x * rowTap hk (m + 1) x := by
    rw [quadratic, index_add, index_add, ← linearInput_row hk hk10, ← linearInput_row hk hk10]
  have hM (m : ℕ) : mix hk 1 (quadratic hk false x) (index hk (m + 2)) =
      rowTap hk (m + 1) x * rowTap hk (m + 2) x + rowTap hk (m + 2) x * rowTap hk (m + 3) x +
        rowTap hk m x * rowTap hk (m + 1) x := by
    rw [mix_index hk (by omega) _ (m + 1), hQ (m + 1), hQ (m + 2), hQ m]
  rw [topWord, index_add, index_add, show gap false = 1 from rfl, hM n, hM (n + 1), rowPoly]
  ring

theorem topWord_col {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (x : Word k) (n : ℕ) :
    topWord hk x true (index hk (n + 5)) =
      colPoly (colTap hk n x) (colTap hk (n + 1) x) (colTap hk (n + 2) x) (colTap hk (n + 3) x)
        (colTap hk (n + 4) x) (colTap hk (n + 5) x) (colTap hk (n + 6) x) := by
  have hQ (m : ℕ) : quadratic hk true x (index hk (m + 4)) =
      colTap hk m x * colTap hk (m + 1) x := by
    rw [quadratic, index_add, index_add, ← linearInput_col hk hk10, ← linearInput_col hk hk10]
  have hM (m : ℕ) : mix hk 2 (quadratic hk true x) (index hk (m + 6)) =
      colTap hk (m + 2) x * colTap hk (m + 3) x + colTap hk (m + 4) x * colTap hk (m + 5) x +
        colTap hk m x * colTap hk (m + 1) x := by
    rw [mix_index hk (by omega) _ (m + 4), hQ (m + 2), hQ (m + 4), hQ m]
  rw [topWord, index_add, index_add, show gap true = 2 from rfl, hM n, hM (n + 1), colPoly]
  ring

def rowTaps {k : ℕ} (hk : 0 < k) (n : ℕ) : Word k →ₗ[Scalar] Word 5 :=
  LinearMap.pi ![rowTap hk n, rowTap hk (n + 1), rowTap hk (n + 2), rowTap hk (n + 3),
    rowTap hk (n + 4)]

def colTaps {k : ℕ} (hk : 0 < k) (n : ℕ) : Word k →ₗ[Scalar] Word 7 :=
  LinearMap.pi ![colTap hk n, colTap hk (n + 1), colTap hk (n + 2), colTap hk (n + 3),
    colTap hk (n + 4), colTap hk (n + 5), colTap hk (n + 6)]

def rowForm (z : Word 5) : Scalar := rowPoly (z 0) (z 1) (z 2) (z 3) (z 4)

def colForm (y : Word 7) : Scalar := colPoly (y 0) (y 1) (y 2) (y 3) (y 4) (y 5) (y 6)

theorem fourth_pullback {k m : ℕ} (ζ : Word k →ₗ[Scalar] Word m) (T : Word m → Scalar)
    (v : Fin 4 → Word k) :
    fourthDifference (fun x => T (ζ x)) v 0 = fourthDifference T (fun e => ζ (v e)) 0 := by
  have h := differences_comp ζ.toAddMonoidHom 0 T (List.ofFn v) 0
  simp only [LinearMap.toAddMonoidHom_coe, add_zero, map_zero, List.map_ofFn] at h
  exact h

def rowDual : Fin 4 → Fin 5 := ![1, 3, 2, 4]

def rowKernel : Word 5 := ![1, 0, 1, 0, 1]

theorem row_dual : ∀ c g₀ g₁ g₂ g₃ : Scalar,
    fourthDifference rowForm
      (fun e => Pi.single (rowDual e) 1 + ![g₀, g₁, g₂, g₃] e • c • rowKernel) 0 = 1 := by
  decide

def colMono (t : Fin 7) : Fin 4 → Fin 7 :=
  if t.val ≤ 1 then ![2, 3, 5, 6] else if t.val = 3 ∨ t.val = 4 then ![0, 1, 5, 6]
  else ![0, 1, 3, 4]

theorem col_dual : ∀ (t : Fin 7) (g₀ g₁ g₂ g₃ : Scalar),
    fourthDifference colForm
      (fun e => Pi.single (colMono t e) 1 + ![g₀, g₁, g₂, g₃] e • Pi.single t 1) 0 = 1 := by
  decide

def unitAt {k : ℕ} (hk : 0 < k) (n : ℕ) : Word k := Pi.single (index hk n) 1

theorem coordinate_unitAt_self {k : ℕ} (hk : 0 < k) (a : ℕ) :
    coordinate hk a (unitAt hk a) = 1 := by
  simp [coordinate, unitAt]

theorem coordinate_unitAt_of_ne {k : ℕ} (hk : 0 < k) {a b : ℕ} (hne : b ≠ a)
    (hab : a < b + k) (hba : b < a + k) : coordinate hk b (unitAt hk a) = 0 := by
  simp [coordinate, unitAt, index_inj hk hba hab, hne]

def rowLift {k : ℕ} (hk : 0 < k) (n : ℕ) (z : Word 5) : Word k :=
  (z 0 + z 1) • unitAt hk n + (z 1 + z 2) • unitAt hk (n + 1) + z 2 • unitAt hk (n + 2) +
    z 3 • unitAt hk (n + 5) + (z 3 + z 4) • unitAt hk (n + 6)

theorem rowTaps_lift {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (n : ℕ) (z : Word 5) :
    rowTaps hk n (rowLift hk n z) = z := by
  funext t
  fin_cases t <;>
    simp (disch := omega) [rowTaps, rowTap, rowLift, Nat.add_assoc, coordinate_unitAt_self,
      coordinate_unitAt_of_ne hk] <;>
    (generalize z 0 = a; generalize z 1 = b; generalize z 2 = c; generalize z 3 = d
     generalize z 4 = e; revert a b c d e; decide)

def colLift {k : ℕ} (hk : 0 < k) (n : ℕ) (y : Word 7) : Word k :=
  (y 1 + y 3) • unitAt hk (n + 1) + (y 0 + y 4 + y 6) • unitAt hk (n + 2) +
    y 3 • unitAt hk (n + 3) + (y 4 + y 6) • unitAt hk (n + 4) + (y 0 + y 2) • unitAt hk (n + 6) +
    (y 0 + y 2 + y 6) • unitAt hk (n + 8) + y 5 • unitAt hk (n + 9)

theorem colTaps_lift {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (n : ℕ) (y : Word 7) :
    colTaps hk n (colLift hk n y) = y := by
  funext t
  fin_cases t <;>
    simp (disch := omega) [colTaps, colTap, colLift, Nat.add_assoc, coordinate_unitAt_self,
      coordinate_unitAt_of_ne hk] <;>
    (generalize y 0 = a; generalize y 1 = b; generalize y 2 = c; generalize y 3 = d
     generalize y 4 = e; generalize y 5 = f; generalize y 6 = g; revert a b c d e f g; decide)

theorem scalar_eq_one : ∀ {a : Scalar}, a ≠ 0 → a = 1 := by decide

theorem row_test {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (ℓ : Query k) (n : ℕ)
    (good : GoodAt hk ℓ false (index hk (n + 1))) (x₀ : Word k) (c : Scalar)
    (hx₀ : rowTaps hk n x₀ = c • rowKernel) (hℓ : ℓ x₀ = 1 ∨ ℓ = 0) : False := by
  let w (e : Fin 4) : Word k := rowLift hk n (Pi.single (rowDual e) 1)
  let v (e : Fin 4) : Word k := w e + ℓ (w e) • x₀
  have hv (e : Fin 4) : ℓ (v e) = 0 := by
    simp only [v, map_add, map_smul, smul_eq_mul]
    rcases hℓ with h | h
    · rw [h, mul_one, CharTwo.add_self_eq_zero]
    · simp [h]
  have h := good v hv
  rw [show (fun x => topWord hk x false (index hk (n + 1))) = fun x => rowForm (rowTaps hk n x)
    from funext fun x => topWord_row hk hk10 x n, fourth_pullback] at h
  have hζ : (fun e => rowTaps hk n (v e)) = fun e =>
      Pi.single (rowDual e) 1 + ![ℓ (w 0), ℓ (w 1), ℓ (w 2), ℓ (w 3)] e • c • rowKernel := by
    funext e
    simp only [v, w, map_add, map_smul, rowTaps_lift hk hk10, hx₀]
    fin_cases e <;> rfl
  rw [hζ, row_dual] at h
  exact one_ne_zero h

def coef {k : ℕ} (hk : 0 < k) (ℓ : Query k) (n : ℕ) : Scalar := ℓ (unitAt hk n)

def Tied (k : ℕ) (A : ℕ → Scalar) (n : ℕ) : Prop :=
  (∀ o, 7 ≤ o → o < k → A (n + o) = 0) ∧
  A n + A (n + 4) + A (n + 5) + A (n + 6) = 0 ∧
  A (n + 1) + A (n + 3) + A (n + 5) = 0 ∧
  A (n + 2) + A (n + 3) + A (n + 4) = 0

theorem tied_of_good {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (ℓ : Query k) (n : ℕ)
    (good : GoodAt hk ℓ false (index hk (n + 1))) : ℓ ≠ 0 ∧ Tied k (coef hk ℓ) n := by
  have zero (c : Scalar) (x₀ : Word k) (hx₀ : rowTaps hk n x₀ = c • rowKernel) : ℓ x₀ = 0 := by
    by_contra h
    exact row_test hk hk10 ℓ n good x₀ c hx₀ (Or.inl (scalar_eq_one h))
  refine ⟨fun h => row_test hk hk10 ℓ n good 0 0 (by simp) (Or.inr h),
    fun o ho ho' => zero 0 _ ?_, ?_, ?_, ?_⟩
  · rw [zero_smul]
    funext t
    fin_cases t <;>
      simp (disch := omega) [rowTaps, rowTap, Nat.add_assoc, coordinate_unitAt_of_ne hk]
  all_goals
    simp only [coef, ← map_add]
    refine zero 1 _ ?_
    rw [one_smul]
    funext t
    fin_cases t <;>
      simp (disch := omega) [rowTaps, rowTap, rowKernel, Nat.add_assoc, coordinate_unitAt_self,
        coordinate_unitAt_of_ne hk] <;>
      decide

theorem not_good_col {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (ℓ : Query k) (n : ℕ) :
    ¬ GoodAt hk ℓ true (index hk (n + 5)) := by
  intro good
  let u (s : Fin 7) : Word k := colLift hk n (Pi.single s 1)
  obtain ⟨t, ht⟩ : ∃ t : Fin 7, ∀ s, ℓ (u s) = 0 ∨ ℓ (u t) = 1 := by
    by_cases h : ∃ t, ℓ (u t) ≠ 0
    · obtain ⟨t, ht⟩ := h
      exact ⟨t, fun _ => Or.inr (scalar_eq_one ht)⟩
    · exact ⟨0, fun s => Or.inl (not_not.1 (not_exists.1 h s))⟩
  let v (e : Fin 4) : Word k := u (colMono t e) + ℓ (u (colMono t e)) • u t
  have hv (e : Fin 4) : ℓ (v e) = 0 := by
    simp only [v, map_add, map_smul, smul_eq_mul]
    rcases ht (colMono t e) with h | h
    · simp [h]
    · rw [h, mul_one, CharTwo.add_self_eq_zero]
  have h := good v hv
  rw [show (fun x => topWord hk x true (index hk (n + 5))) = fun x => colForm (colTaps hk n x)
    from funext fun x => topWord_col hk hk10 x n, fourth_pullback] at h
  have hζ : (fun e => colTaps hk n (v e)) = fun e => Pi.single (colMono t e) 1 +
      ![ℓ (u (colMono t 0)), ℓ (u (colMono t 1)), ℓ (u (colMono t 2)), ℓ (u (colMono t 3))] e •
        Pi.single t 1 := by
    funext e
    simp only [v, u, map_add, map_smul, colTaps_lift hk hk10]
    fin_cases e <;> rfl
  rw [hζ, col_dual] at h
  exact one_ne_zero h

theorem degree_query {k : ℕ} (ℓ : Query k) : degree 1 (fun x => ℓ x) := by
  intro u v x
  simp only [delta, map_add]
  ring

theorem degree_cube {k : ℕ} (p q r : Query k) : degree 3 (fun x => p x * q x * r x) :=
  degree_mul (degree_mul (degree_query p) (degree_query q)) (degree_query r)

theorem good_of_cubic {k : ℕ} (hk : 0 < k) (ℓ : Query k) (b : Bool) (i : Fin k)
    (G : Word k → Scalar) (hG : degree 3 G) (h : ∀ x, ℓ x = 0 → topWord hk x b i = G x) :
    GoodAt hk ℓ b i := by
  intro v hv
  have hmem (u : Word k) (hu : u ∈ List.ofFn v) : u ∈ (LinearMap.ker ℓ).toAddSubgroup := by
    obtain ⟨e, rfl⟩ := List.mem_ofFn.1 hu
    exact hv e
  exact (differences_eq_on (S := (LinearMap.ker ℓ).toAddSubgroup) h _ hmem 0 (zero_mem _)).trans
    (differences_zero _ List.length_ofFn hG 0)

def rowCubic (a b c d e : Scalar) : Scalar := a * b * c + b * c + c * d + c * d * e + a * b * d

theorem rowPoly_cases : ∀ a b c d e : Scalar,
    (a = c ∨ a + b + d + e = 0 → rowPoly a b c d e = rowCubic a b c d e) ∧
    (b = d → rowPoly a b c d e = rowCubic a b c d e + b * (a + c) * (a + e)) ∧
    (c = e → rowPoly a b c d e = rowCubic a b c d e + b * d * (a + c)) := by
  decide

theorem degree_rowCubic {k : ℕ} (p q r s t : Query k) :
    degree 3 (fun x => rowCubic (p x) (q x) (r x) (s x) (t x)) :=
  degree_add (degree_add (degree_add (degree_add (degree_cube p q r)
    (degree_raise (degree_mul (degree_query q) (degree_query r))))
    (degree_raise (degree_mul (degree_query r) (degree_query s)))) (degree_cube r s t))
    (degree_cube p q s)

theorem good_row {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (ℓ : Query k) (m : ℕ)
    (h : (∀ x, ℓ x = 0 → rowTap hk m x = rowTap hk (m + 2) x ∨
        rowTap hk m x + rowTap hk (m + 1) x + rowTap hk (m + 3) x + rowTap hk (m + 4) x = 0) ∨
      (∀ x, ℓ x = 0 → rowTap hk (m + 1) x = rowTap hk (m + 3) x) ∨
      (∀ x, ℓ x = 0 → rowTap hk (m + 2) x = rowTap hk (m + 4) x)) :
    GoodAt hk ℓ false (index hk (m + 1)) := by
  have hC := degree_rowCubic (rowTap hk m) (rowTap hk (m + 1)) (rowTap hk (m + 2))
    (rowTap hk (m + 3)) (rowTap hk (m + 4))
  rcases h with h | h | h
  · refine good_of_cubic hk ℓ false _ _ hC fun x hx => ?_
    rw [topWord_row hk hk10]
    exact (rowPoly_cases _ _ _ _ _).1 (h x hx)
  · refine good_of_cubic hk ℓ false _ _ (degree_add hC (degree_cube (rowTap hk (m + 1))
      (rowTap hk m + rowTap hk (m + 2)) (rowTap hk m + rowTap hk (m + 4)))) fun x hx => ?_
    rw [topWord_row hk hk10]
    exact (rowPoly_cases _ _ _ _ _).2.1 (h x hx)
  · refine good_of_cubic hk ℓ false _ _ (degree_add hC (degree_cube (rowTap hk (m + 1))
      (rowTap hk (m + 3)) (rowTap hk m + rowTap hk (m + 2)))) fun x hx => ?_
    rw [topWord_row hk hk10]
    exact (rowPoly_cases _ _ _ _ _).2.2 (h x hx)

theorem scalar_eq_of_add : ∀ {a b : Scalar}, a + b = 0 → a = b := by decide

theorem good_window {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (j : Fin k) :
    ∃ ℓ : Query k, ∀ i, i = j ∨ i = index hk (j.val + 1) ∨ i = index hk (j.val + 2) →
      GoodAt hk ℓ false i := by
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = j.val + k := ⟨j.val + k - 1, by omega⟩
  refine ⟨rowTap hk (n + 2) + rowTap hk (n + 4), ?_⟩
  have pair (x : Word k) (hx : (rowTap hk (n + 2) + rowTap hk (n + 4)) x = 0) :
      rowTap hk (n + 2) x = rowTap hk (n + 4) x := scalar_eq_of_add hx
  rintro i (h | h | h)
  · rw [h, ← index_wrap hk j hn]
    exact good_row hk hk10 _ n (Or.inr (Or.inr pair))
  · rw [h, ← index_period hk (show n + 1 + 1 = j.val + 1 + k by omega)]
    exact good_row hk hk10 _ (n + 1) (Or.inr (Or.inl pair))
  · rw [h, ← index_period hk (show n + 2 + 1 = j.val + 2 + k by omega)]
    exact good_row hk hk10 _ (n + 2) (Or.inl fun x hx => Or.inl (pair x hx))

theorem opposite_sum : ∀ a b c d e f g : Scalar, a + g = 0 →
    a + b + c + (b + c + d) + (d + e + f) + (e + f + g) = 0 := by
  decide

theorem good_opposite (hk : 0 < 12) (j : Fin 12) :
    ∃ ℓ : Query 12, ∀ i, i = j ∨ i = index hk (j.val + 6) → GoodAt hk ℓ false i := by
  obtain ⟨n, hn⟩ : ∃ n, n + 1 = j.val + 12 := ⟨j.val + 11, rfl⟩
  refine ⟨coordinate hk n + coordinate hk (n + 6), ?_⟩
  have ends (m : ℕ) (x : Word 12) (hx : x (index hk m) + x (index hk (m + 6)) = 0) :
      rowTap hk m x + rowTap hk (m + 1) x + rowTap hk (m + 3) x + rowTap hk (m + 4) x = 0 :=
    opposite_sum (x (index hk m)) (x (index hk (m + 1))) (x (index hk (m + 2)))
      (x (index hk (m + 3))) (x (index hk (m + 4))) (x (index hk (m + 5)))
      (x (index hk (m + 6))) hx
  rintro i (h | h)
  · rw [h, ← index_wrap hk j hn]
    exact good_row hk (by norm_num) _ n (Or.inl fun x hx => Or.inr (ends n x hx))
  · rw [h, ← index_period hk (show n + 6 + 1 = j.val + 6 + 12 by omega)]
    refine good_row hk (by norm_num) _ (n + 6) (Or.inl fun x hx => Or.inr (ends (n + 6) x ?_))
    rw [index_period hk (show n + 6 + 6 = n + 12 by omega), add_comm]
    exact hx

theorem coef_period {k : ℕ} (hk : 0 < k) (ℓ : Query k) (n : ℕ) :
    coef hk ℓ (n + k) = coef hk ℓ n := by
  rw [coef, unitAt, index_period hk rfl]
  rfl

theorem exists_coef_ne {k : ℕ} (hk : 0 < k) {ℓ : Query k} (hℓ : ℓ ≠ 0) :
    ∃ n, coef hk ℓ n ≠ 0 := by
  by_contra h
  refine hℓ (LinearMap.pi_ext fun i c => ?_)
  have hi : ℓ (Pi.single i 1) = 0 := by
    have := not_not.1 (not_exists.1 h i.val)
    rwa [coef, unitAt, index_val] at this
  rw [show (Pi.single i c : Word k) = c • Pi.single i 1 by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, hi, smul_zero, LinearMap.zero_apply]

theorem tied_add_period {k : ℕ} {A : ℕ → Scalar} (hP : ∀ n, A (n + k) = A n) (n : ℕ) :
    Tied k A (n + k) ↔ Tied k A n := by
  simp only [Tied, add_right_comm n k, hP]

theorem eq_zero_of_window {k n : ℕ} {A : ℕ → Scalar} (hP : ∀ n, A (n + k) = A n) (hk : 0 < k)
    (h : ∀ o, o < k → A (n + o) = 0) (m : ℕ) : A m = 0 := by
  have hP' : Function.Periodic A k := hP
  have hn : ∀ j, A (n + j) = 0 := fun j =>
    (hP'.const_add n).map_mod_nat j ▸ h _ (Nat.mod_lt j hk)
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 1 := ⟨k - 1, by omega⟩
  have hm := hP'.nat_mul n m
  rw [Nat.cast_id, show m + n * (c + 1) = n + (m + n * c) by ring] at hm
  exact hm.symm.trans (hn _)

theorem tied_zero {k n : ℕ} {A : ℕ → Scalar} (h : Tied k A n) (h0 : A n = 0)
    (h1 : A (n + 1) = 0) (h2 : A (n + 2) = 0) (h3 : A (n + 3) = 0) :
    ∀ o, o < k → A (n + o) = 0 := by
  obtain ⟨Z, E1, E2, E3⟩ := h
  have h4 : A (n + 4) = 0 := by simpa [h2, h3] using E3
  have h5 : A (n + 5) = 0 := by simpa [h1, h3] using E2
  have h6 : A (n + 6) = 0 := by simpa [h0, h4, h5] using E1
  intro o ho
  rcases Nat.lt_or_ge o 7 with h7 | h7
  · interval_cases o <;> assumption
  · exact Z o h7 ho

theorem tied_left {k n d o : ℕ} {A : ℕ → Scalar} (hP : ∀ n, A (n + k) = A n)
    (h : Tied k A (n + d)) (ho : o < d) (hd : d + 7 ≤ o + k) : A (n + o) = 0 := by
  have := h.1 (o + k - d) (by omega) (by omega)
  rwa [show n + d + (o + k - d) = n + o + k by omega, hP] at this

theorem tied_two {k n d : ℕ} {A : ℕ → Scalar} (hP : ∀ n, A (n + k) = A n) (hk : 10 ≤ k)
    (h : Tied k A n) (h' : Tied k A (n + d)) (hd : 3 ≤ d) (hdk : 2 * d ≤ k)
    (hex : ¬(k = 12 ∧ d = 6)) (m : ℕ) : A m = 0 := by
  refine eq_zero_of_window hP (by omega) (n := n) ?_ m
  have L : ∀ o, o < d → d + 7 ≤ o + k → A (n + o) = 0 := fun o => tied_left hP h'
  have ⟨Z, E1, E2, E3⟩ := h
  obtain ⟨-, E1', E2', -⟩ := h'
  simp only [Nat.add_assoc] at E1' E2'
  by_cases hc : d + 7 ≤ k
  · have h3 : A (n + 3) = 0 := by
      obtain rfl | h4 : d = 3 ∨ 4 ≤ d := by omega
      exacts [by simpa (disch := omega) [Z] using E1', L 3 h4 (by omega)]
    refine tied_zero h (L 0 (by omega) (by omega)) ?_ ?_ h3 <;> exact L _ (by omega) (by omega)
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ :
      (d = 4 ∧ k = 10) ∨ (d = 5 ∧ k = 11) ∨ (d = 5 ∧ k = 10) := by omega
  · have h4 : A (n + 4) = 0 := by simpa (disch := omega) [L] using E3
    have h0 : A n = 0 := by simpa (disch := omega) [Z, h4, hP n] using E1'
    refine tied_zero h h0 ?_ ?_ ?_ <;> exact L _ (by omega) (by omega)
  · have h5 : A (n + 5) = 0 := by simpa (disch := omega) [L] using E2
    have h0 : A n = 0 := by simpa (disch := omega) [Z, h5, hP n] using E1'
    refine tied_zero h h0 ?_ ?_ ?_ <;> exact L _ (by omega) (by omega)
  · have p1 : A (n + 11) = A (n + 1) := hP (n + 1)
    have e2 : A (n + 1) + A (n + 5) = 0 := by simpa (disch := omega) [L] using E2
    have e1 : A n + A (n + 5) + A (n + 6) = 0 := by simpa (disch := omega) [L] using E1
    have e1' : A (n + 5) + A n + A (n + 1) = 0 := by
      simpa (disch := omega) [Z, hP n, p1] using E1'
    have e2' : A (n + 6) + A n = 0 := by simpa (disch := omega) [Z, hP n] using E2'
    have key : ∀ a b c e : Scalar,
        b + c = 0 → a + c + e = 0 → c + a + b = 0 → e + a = 0 → a = 0 ∧ b = 0 := by decide
    obtain ⟨h0, h1⟩ := key _ _ _ _ e2 e1 e1' e2'
    refine tied_zero h h0 h1 ?_ ?_ <;> exact L _ (by omega) (by omega)

theorem marked_pair {k x y : ℕ} {A : ℕ → Scalar} (hP : ∀ n, A (n + k) = A n) (hk : 10 ≤ k)
    (hA : ∃ n, A n ≠ 0) (hx : Tied k A (x + k - 1)) (hy : Tied k A (y + k - 1))
    (hxk : x < k) (hyk : y < k) :
    (y ≤ x + 2 ∧ x ≤ y + 2) ∨ x + k ≤ y + 2 ∨ y + k ≤ x + 2 ∨
      (k = 12 ∧ (y = x + 6 ∨ x = y + 6)) := by
  wlog hxy : x ≤ y generalizing x y
  · have := this hy hx hyk hxk (by omega)
    omega
  obtain ⟨m, hm⟩ := hA
  by_contra hc
  refine hm ?_
  rcases Nat.le_total (2 * (y - x)) k with h | h
  · refine tied_two hP hk hx (d := y - x) ?_ (by omega) h (by omega) m
    rwa [show x + k - 1 + (y - x) = y + k - 1 by omega]
  · refine tied_two hP hk hy (d := x + k - y) ?_ (by omega) (by omega) (by omega) m
    rwa [show y + k - 1 + (x + k - y) = x + k - 1 + k by omega, tied_add_period hP]

theorem eq_index {k : ℕ} (hk : 0 < k) (i : Fin k) {m : ℕ} (hm : m < 2 * k) :
    i = index hk m ↔ i.val = m ∨ i.val + k = m := by
  have hi := i.isLt
  simp only [Fin.ext_iff, index]
  rcases Nat.lt_or_ge m k with h | h
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

theorem exists_last_le_two (B : ℕ → Prop) (h0 : B 0) :
    ∃ c ≤ 2, B c ∧ ∀ c', c < c' → c' ≤ 2 → ¬B c' := by
  classical
  exact ⟨Nat.findGreatest B 2, Nat.findGreatest_le 2, Nat.findGreatest_spec (Nat.zero_le 2) h0,
    fun _ => Nat.findGreatest_is_greatest⟩

theorem near_window {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (M : Fin k → Prop)
    (hM : ∀ i i', M i → M i' → (i'.val ≤ i.val + 2 ∧ i.val ≤ i'.val + 2) ∨
      i.val + k ≤ i'.val + 2 ∨ i'.val + k ≤ i.val + 2) :
    ∃ j : Fin k, ∀ i, M i → i = j ∨ i = index hk (j.val + 1) ∨ i = index hk (j.val + 2) := by
  by_cases hne : ∃ i, M i
  case neg => exact ⟨⟨0, hk⟩, fun i hi => (hne ⟨i, hi⟩).elim⟩
  obtain ⟨i, hi⟩ := hne
  obtain ⟨c, hc, ⟨j, hj, hji⟩, hmax⟩ := exists_last_le_two
    (fun c => ∃ j, M j ∧ (j.val + c = i.val ∨ j.val + c = i.val + k)) ⟨i, hi, Or.inl rfl⟩
  refine ⟨j, fun i' hi' => ?_⟩
  have h1 := hM i i' hi hi'
  have h2 := hM j i' hj hi'
  have h3 : ∀ c', c < c' → c' ≤ 2 → ¬(i'.val + c' = i.val ∨ i'.val + c' = i.val + k) :=
    fun c' h h' hB => hmax c' h h' ⟨i', hi', hB⟩
  have h31 := h3 1
  have h32 := h3 2
  rw [Fin.ext_iff, eq_index hk, eq_index hk] <;> omega

theorem marked_window {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (A : ℕ → Scalar)
    (hP : ∀ n, A (n + k) = A n) (hA : ∃ n, A n ≠ 0) (M : Fin k → Prop)
    (hM : ∀ i, M i → Tied k A (i.val + k - 1)) :
    (∃ j : Fin k, ∀ i, M i → i = j ∨ i = index hk (j.val + 1) ∨ i = index hk (j.val + 2)) ∨
    (k = 12 ∧ ∃ j : Fin k, ∀ i, M i → i = j ∨ i = index hk (j.val + 6)) := by
  have hpair := fun i i' (hi : M i) (hi' : M i') =>
    marked_pair hP hk10 hA (hM i hi) (hM i' hi') i.isLt i'.isLt
  by_cases hopp : ∃ i i', M i ∧ M i' ∧ i'.val = i.val + 6
  · obtain ⟨i, i', hi, hi', ho⟩ := hopp
    have h0 := hpair i i' hi hi'
    refine Or.inr ⟨by omega, i, fun i'' hi'' => ?_⟩
    have h1 := hpair i i'' hi hi''
    have h2 := hpair i' i'' hi' hi''
    rw [Fin.ext_iff, eq_index hk] <;> omega
  · refine Or.inl (near_window hk hk10 M fun i i' hi hi' => ?_)
    have h0 := hpair i i' hi hi'
    have h1 : i'.val ≠ i.val + 6 := fun h => hopp ⟨i, i', hi, hi', h⟩
    have h2 : i.val ≠ i'.val + 6 := fun h => hopp ⟨i', i, hi', hi, h⟩
    omega

theorem two_round_fits {k : ℕ} (hk : 0 < k) (hk10 : 10 ≤ k) (mark : Fin k → Bool × Bool)
    (name c₁ c₂ : Bool → Word k) :
    (∃ (ask : Fin 1 → ℕ → Query k) (readout : ℕ → Bool → Fin k → Word k → Scalar),
      (∀ h b i, IsCubic (readout h b i)) ∧
      ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
        outputWord hk name c₁ c₂ x b i = readout (queryRun ask x) b i x) ↔
    (∀ i, (mark i).2 = false) ∧
    ((∃ j : Fin k, ∀ i, (mark i).1 = true →
        i = j ∨ i = index hk (j.val + 1) ∨ i = index hk (j.val + 2)) ∨
      (k = 12 ∧ ∃ j : Fin k, ∀ i, (mark i).1 = true → i = j ∨ i = index hk (j.val + 6))) := by
  refine (parity_criterion hk name c₁ c₂
    fun b i => (if b then (mark i).2 else (mark i).1) = true).trans ⟨?_, ?_⟩
  · rintro ⟨ℓ, good⟩
    have hcol (i : Fin k) : (mark i).2 = false := by
      by_contra h
      refine not_good_col hk hk10 ℓ (i.val + k - 5) ?_
      rw [index_wrap hk i (show i.val + k - 5 + 5 = i.val + k by omega)]
      exact good true i (by simpa using h)
    have tied (i : Fin k) (hi : (mark i).1 = true) :
        ℓ ≠ 0 ∧ Tied k (coef hk ℓ) (i.val + k - 1) := by
      refine tied_of_good hk hk10 ℓ _ ?_
      rw [index_wrap hk i (show i.val + k - 1 + 1 = i.val + k by omega)]
      exact good false i hi
    refine ⟨hcol, ?_⟩
    by_cases hrow : ∃ i, (mark i).1 = true
    · obtain ⟨i₀, hi₀⟩ := hrow
      exact marked_window hk hk10 (coef hk ℓ) (coef_period hk ℓ)
        (exists_coef_ne hk (tied i₀ hi₀).1) (fun i => (mark i).1 = true) fun i hi => (tied i hi).2
    · exact Or.inl ⟨⟨0, hk⟩, fun i hi => (hrow ⟨i, hi⟩).elim⟩
  · rintro ⟨hcol, hrow⟩
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Query k, ∀ i, (mark i).1 = true → GoodAt hk ℓ false i := by
      rcases hrow with ⟨j, hj⟩ | ⟨rfl, j, hj⟩
      · exact (good_window hk hk10 j).imp fun ℓ hℓ i hi => hℓ i (hj i hi)
      · exact (good_opposite hk j).imp fun ℓ hℓ i hi => hℓ i (hj i hi)
    refine ⟨ℓ, fun b i hm => ?_⟩
    cases b
    · exact hℓ i hm
    · exact absurd hm (by simp [hcol i])

end PEqualNP.Outside.L_meta_29772_aux

theorem PEqualNP.Outside.L_meta_29772 :
(
let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
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
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
∀ (k : ℕ) (hk : 0 < k), 10 ≤ k →
  ∀ (mark : Fin k → Bool × Bool) (name c₁ c₂ : Bool → Fin k → ZMod 2),
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  fits k hk mark 1 name c₁ c₂ ↔
    (∀ i, (mark i).2 = false) ∧
    ((∃ j : Fin k, ∀ i, (mark i).1 = true →
       i = j ∨ i = ix (j.val + 1) ∨ i = ix (j.val + 2)) ∨
     (k = 12 ∧ ∃ j : Fin k, ∀ i, (mark i).1 = true →
       i = j ∨ i = ix (j.val + 6)))
) := by
  intro fits k hk hk10 mark name c₁ c₂ ix
  exact PEqualNP.Outside.L_meta_29772_aux.two_round_fits hk hk10 mark name c₁ c₂
