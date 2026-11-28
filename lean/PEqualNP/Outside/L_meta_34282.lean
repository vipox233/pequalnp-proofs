import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_34282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

section Prog
variable {ι κ : Type}

def K (S : (ι → Bool) → Prop) (w : ι → Bool) : Prop :=
  (∃ c : Bool, w = fun _ => c) ∨ S w ∨ S (fun x => !w x)

def ins (z : ι → Bool) (S : (ι → Bool) → Prop) : (ι → Bool) → Prop := fun w => w = z ∨ S w

def Run : ℕ → ((ι → Bool) → Prop) → (ι → Bool) → Prop
  | 0, S, f => K S f
  | t + 1, S, f => Run t S f ∨
      ∃ a b : ι → Bool, K S a ∧ K S b ∧ Run t (ins (fun x => a x && b x) S) f

lemma K_not {S : (ι → Bool) → Prop} {w : ι → Bool} (h : K S w) : K S (fun x => !w x) := by
  rcases h with ⟨c, rfl⟩ | h | h
  · exact Or.inl ⟨!c, rfl⟩
  · exact Or.inr (Or.inr (by simpa using h))
  · exact Or.inr (Or.inl h)

lemma K_ins {S : (ι → Bool) → Prop} {z w : ι → Bool} (h : K S w) : K (ins z S) w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inr h))

lemma K_new {S : (ι → Bool) → Prop} (z : ι → Bool) : K (ins z S) z := Or.inr (Or.inl (Or.inl rfl))

lemma K_and {S : (ι → Bool) → Prop} {a b : ι → Bool} (ha : ∃ c, ∀ y, a y = c) (hb : K S b) :
    K S (fun y => a y && b y) := by
  obtain ⟨c, hc⟩ := ha
  cases c
  · exact Or.inl ⟨false, funext fun y => by simp [hc y]⟩
  · have : (fun y => a y && b y) = b := funext fun y => by simp [hc y]
    rw [this]; exact hb

lemma K_bind {S : (ι → Bool) → Prop} {S' : (κ → Bool) → Prop} (σ : κ → ι)
    (h : ∀ w, S w → K S' (fun y => w (σ y))) {w : ι → Bool} (hw : K S w) :
    K S' (fun y => w (σ y)) := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact Or.inl ⟨c, rfl⟩
  · exact h w hw
  · have h2 := K_not (h _ hw)
    simpa using h2

lemma Run_map (σ : κ → ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), (∀ w, S w → K S' (fun y => w (σ y))) → Run t S f → Run t S' (fun y => f (σ y))
  | 0, _, _, _, h, hf => K_bind σ h hf
  | t + 1, S, S', f, h, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · exact Or.inl (Run_map σ t S S' f h hf)
    · refine Or.inr ⟨_, _, K_bind σ h ha, K_bind σ h hb, Run_map σ t _ _ f ?_ hf⟩
      rintro w (rfl | hw)
      · exact K_new _
      · exact K_ins (h w hw)

lemma Run_le {t t' : ℕ} {S : (ι → Bool) → Prop} {f : ι → Bool} (h : t ≤ t') (hf : Run t S f) :
    Run t' S f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact Or.inl ih

def Cl (σ : κ → ι) (p q r : ι) (S : (ι → Bool) → Prop) : Prop :=
  ∀ w, S w → w p ≠ w q → ∀ y, w (σ y) = w r

lemma Cl_K {σ : κ → ι} {p q r : ι} {S : (ι → Bool) → Prop} (h : Cl σ p q r S) {w : ι → Bool}
    (hw : K S w) (hd : w p ≠ w q) (y : κ) : w (σ y) = w r := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact absurd rfl hd
  · exact h w hw hd y
  · have h2 := h _ hw (by simpa using hd) y
    simpa using h2

lemma and_dep {a b : ι → Bool} {p q : ι} (h : (a p && b p) ≠ (a q && b q)) :
    a p ≠ a q ∨ b p ≠ b q := by
  by_contra hc
  simp only [not_or, not_not] at hc
  exact h (by rw [hc.1, hc.2])

lemma kill1 (σ : κ → ι) (p q r : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), Cl σ p q r S → (∀ w, S w → K S' (fun y => w (σ y))) → f p ≠ f q →
    (∃ y y', f (σ y) ≠ f (σ y')) → Run t S f → ∃ t', t' + 1 ≤ t ∧ Run t' S' (fun y => f (σ y))
  | 0, _, _, f, hc, _, hd, ⟨y, y', hn⟩, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S', f, hc, hm, hd, hn, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t S S' f hc hm hd hn hf
      exact ⟨t', by omega, hr⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · have hk : K S' (fun y => a (σ y) && b (σ y)) := by
          rcases and_dep hz with h | h
          · exact K_and ⟨a r, Cl_K hc ha h⟩ (K_bind σ hm hb)
          · have e : (fun y => a (σ y) && b (σ y)) = fun y => b (σ y) && a (σ y) :=
              funext fun y => Bool.and_comm _ _
            rw [e]
            exact K_and ⟨b r, Cl_K hc hb h⟩ (K_bind σ hm ha)
        refine ⟨t, le_rfl, Run_map σ t _ S' f ?_ hf⟩
        rintro w (rfl | hw)
        · exact hk
        · exact hm w hw
      · obtain ⟨t', ht, hr⟩ := kill1 σ p q r t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ y) && b (σ y)) S') f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm w hw)) hd hn hf
        exact ⟨t' + 1, by omega, Or.inr ⟨_, _, K_bind σ hm ha, K_bind σ hm hb, hr⟩⟩

lemma kill2_dep (σ0 σ1 : κ → ι) (p q : ι) {t : ℕ} {S : (ι → Bool) → Prop}
    {S0 S1 : (κ → Bool) → Prop} {f a b : ι → Bool} (hc0 : Cl σ0 p q p S) (hc1 : Cl σ1 p q q S)
    (hm0 : ∀ w, S w → K S0 (fun y => w (σ0 y))) (hm1 : ∀ w, S w → K S1 (fun y => w (σ1 y)))
    (hd : f p ≠ f q) (hn0 : ∃ y y', f (σ0 y) ≠ f (σ0 y')) (hn1 : ∃ y y', f (σ1 y) ≠ f (σ1 y'))
    (ha : K S a) (hb : K S b) (hda : a p ≠ a q) (hf : Run t (ins (fun x => a x && b x) S) f) :
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t + 1 ∧ t1 + 1 ≤ t + 1) ∨ (t0 + 1 ≤ t + 1 ∧ t1 + 2 ≤ t + 1)) := by
  have k0 := Cl_K hc0 ha hda
  have k1 := Cl_K hc1 ha hda
  have hz0 : ∀ w, ins (fun x => a x && b x) S w → K S0 (fun y => w (σ0 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k0⟩ (K_bind σ0 hm0 hb)
    · exact hm0 w hw
  have hz1 : ∀ w, ins (fun x => a x && b x) S w → K S1 (fun y => w (σ1 y)) := by
    rintro w (rfl | hw)
    · exact K_and ⟨_, k1⟩ (K_bind σ1 hm1 hb)
    · exact hm1 w hw
  cases hap : a p
  · obtain ⟨t', ht, hr⟩ := kill1 σ0 p q p t _ S0 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k0 y, hap]
        · exact hc0 w hw hd2) hz0 hd hn0 hf
    exact ⟨t', t, hr, Run_map σ1 t _ S1 f hz1 hf, Or.inl ⟨by omega, le_rfl⟩⟩
  · have haq : a q = false := by
      cases h : a q
      · rfl
      · exact absurd (hap.trans h.symm) hda
    obtain ⟨t', ht, hr⟩ := kill1 σ1 p q q t _ S1 f (by
        rintro w (rfl | hw) hd2
        · intro y; simp [k1 y, haq]
        · exact hc1 w hw hd2) hz1 hd hn1 hf
    exact ⟨t, t', Run_map σ0 t _ S0 f hz0 hf, hr, Or.inr ⟨le_rfl, by omega⟩⟩

lemma kill2 (σ0 σ1 : κ → ι) (p q : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop)
    (S0 S1 : (κ → Bool) → Prop) (f : ι → Bool), Cl σ0 p q p S → Cl σ1 p q q S →
    (∀ w, S w → K S0 (fun y => w (σ0 y))) → (∀ w, S w → K S1 (fun y => w (σ1 y))) → f p ≠ f q →
    (∃ y y', f (σ0 y) ≠ f (σ0 y')) → (∃ y y', f (σ1 y) ≠ f (σ1 y')) → Run t S f →
    ∃ t0 t1, Run t0 S0 (fun y => f (σ0 y)) ∧ Run t1 S1 (fun y => f (σ1 y)) ∧
      ((t0 + 2 ≤ t ∧ t1 + 1 ≤ t) ∨ (t0 + 1 ≤ t ∧ t1 + 2 ≤ t))
  | 0, _, _, _, f, hc, _, _, _, hd, ⟨y, y', hn⟩, _, hf =>
    absurd ((Cl_K hc hf hd y).trans (Cl_K hc hf hd y').symm) hn
  | t + 1, S, S0, S1, f, hc0, hc1, hm0, hm1, hd, hn0, hn1, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t S S0 S1 f hc0 hc1 hm0 hm1 hd hn0 hn1 hf
      exact ⟨t0, t1, r0, r1, by omega⟩
    · by_cases hz : (a p && b p) ≠ (a q && b q)
      · rcases and_dep hz with h | h
        · exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 ha hb h hf
        · have e : (fun x => a x && b x) = fun x => b x && a x :=
            funext fun x => Bool.and_comm _ _
          rw [e] at hf
          exact kill2_dep σ0 σ1 p q hc0 hc1 hm0 hm1 hd hn0 hn1 hb ha h hf
      · obtain ⟨t0, t1, r0, r1, h⟩ := kill2 σ0 σ1 p q t (ins (fun x => a x && b x) S)
          (ins (fun y => a (σ0 y) && b (σ0 y)) S0) (ins (fun y => a (σ1 y) && b (σ1 y)) S1) f
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc0 w hw hd2)
          (by
            rintro w (rfl | hw) hd2
            · exact absurd hd2 hz
            · exact hc1 w hw hd2)
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm0 w hw))
          (by
            rintro w (rfl | hw)
            · exact K_new _
            · exact K_ins (hm1 w hw)) hd hn0 hn1 hf
        exact ⟨t0 + 1, t1 + 1, Or.inr ⟨_, _, K_bind σ0 hm0 ha, K_bind σ0 hm0 hb, r0⟩,
          Or.inr ⟨_, _, K_bind σ1 hm1 ha, K_bind σ1 hm1 hb, r1⟩, by omega⟩

end Prog

section Rules
variable {n : ℕ}

abbrev BF (n : ℕ) := (Fin n → Bool) → Bool

def Vars (n : ℕ) : BF n → Prop := fun w => ∃ i : Fin n, w = fun x => x i

def LB (f : BF n) (b : ℕ) : Prop := ∀ t, Run t (Vars n) f → b ≤ t

def pt (n : ℕ) (c : ℕ) : Fin n → Bool := fun i => c.testBit i.val

def rs (f : BF n) (i : Fin n) (c : Bool) : BF n := fun x => f (Function.update x i c)

lemma vars_rs (i : Fin n) (c : Bool) (w : BF n) (hw : Vars n w) :
    K (Vars n) (fun x => w (Function.update x i c)) := by
  obtain ⟨j, rfl⟩ := hw
  by_cases h : j = i
  · subst h; exact Or.inl ⟨c, by simp⟩
  · exact Or.inr (Or.inl ⟨j, by simp [Function.update_of_ne h]⟩)

lemma vars_cl (i : Fin n) (c : Bool) (x : Fin n → Bool) :
    Cl (fun y => Function.update y i c) (Function.update x i false) (Function.update x i true)
      (Function.update x i c) (Vars n) := by
  rintro w ⟨j, rfl⟩ hd y
  by_cases h : j = i
  · subst h; simp
  · exact absurd (by simp [Function.update_of_ne h]) hd

lemma rule1 (f : BF n) (i : Fin n) (c : Bool) (b p y y' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn : rs f i c (pt n y) ≠ rs f i c (pt n y')) (h : LB (rs f i c) b) : LB f (b + 1) := by
  intro t ht
  obtain ⟨t', h1, h2⟩ := kill1 _ _ _ _ t _ (Vars n) f (vars_cl i c (pt n p)) (vars_rs i c) hd
    ⟨_, _, hn⟩ ht
  have := h t' h2
  omega

lemma rule2 (f : BF n) (i : Fin n) (b p y y' u u' : ℕ)
    (hd : f (Function.update (pt n p) i false) ≠ f (Function.update (pt n p) i true))
    (hn0 : rs f i false (pt n y) ≠ rs f i false (pt n y'))
    (hn1 : rs f i true (pt n u) ≠ rs f i true (pt n u'))
    (h0 : LB (rs f i false) b) (h1 : LB (rs f i true) b) : LB f (b + 2) := by
  intro t ht
  obtain ⟨t0, t1, r0, r1, h⟩ := kill2 _ _ _ _ t _ (Vars n) (Vars n) f (vars_cl i false (pt n p))
    (vars_cl i true (pt n p)) (vars_rs i false) (vars_rs i true) hd ⟨_, _, hn0⟩ ⟨_, _, hn1⟩ ht
  have g0 := h0 t0 r0
  have g1 := h1 t1 r1
  omega

lemma LB_mono {f : BF n} {b b' : ℕ} (h : LB f b) (hb : b' ≤ b) : LB f b' :=
  fun t ht => hb.trans (h t ht)

lemma LB_perm (π : Fin n → Fin n) (f g : BF n) (hg : ∀ x, g x = f (fun i => x (π i))) {b : ℕ}
    (h : LB g b) : LB f b := by
  intro t ht
  apply h t
  have e : g = fun x => f (fun i => x (π i)) := funext hg
  rw [e]
  refine Run_map (fun (x : Fin n → Bool) (i : Fin n) => x (π i)) t _ _ f ?_ ht
  rintro w ⟨j, rfl⟩
  exact Or.inr (Or.inl ⟨π j, rfl⟩)

end Rules

section First
variable {n : ℕ}

def lit (i : Fin n) (s : Bool) : BF n := fun x => Bool.xor (x i) (!s)

lemma lit_K (i : Fin n) (s : Bool) : K (Vars n) (lit i s) := by
  cases s
  · refine Or.inr (Or.inr ⟨i, ?_⟩)
    funext x; simp [lit]
  · refine Or.inr (Or.inl ⟨i, ?_⟩)
    funext x; simp [lit]

def VE (E : Fin n → Bool) : BF n → Prop := fun w => ∃ i : Fin n, E i = true ∧ w = fun x => x i

lemma VE_sub {E : Fin n → Bool} {w : BF n} (h : VE E w) : Vars n w := by
  obtain ⟨i, _, h⟩ := h
  exact ⟨i, h⟩

lemma lit_KE {E : Fin n → Bool} {i : Fin n} (hi : E i = true) (s : Bool) : K (VE E) (lit i s) := by
  cases s
  · refine Or.inr (Or.inr ⟨i, hi, ?_⟩)
    funext x; simp [lit]
  · refine Or.inr (Or.inl ⟨i, hi, ?_⟩)
    funext x; simp [lit]

lemma K_lit {E : Fin n → Bool} {w : BF n} (h : K (VE E) w) :
    (∃ c, ∀ y, w y = c) ∨ ∃ i s, E i = true ∧ w = lit i s := by
  rcases h with ⟨c, rfl⟩ | ⟨i, hi, rfl⟩ | ⟨i, hi, h⟩
  · exact Or.inl ⟨c, fun _ => rfl⟩
  · exact Or.inr ⟨i, true, hi, by funext x; simp [lit]⟩
  · refine Or.inr ⟨i, false, hi, ?_⟩
    funext x
    have := congrFun h x
    simp only [lit]
    rw [← this]
    cases w x <;> rfl

def dep (f : BF n) (i j : Fin n) (c : Bool) : Prop := ∃ p : Fin n → Bool,
  f (Function.update (Function.update p j c) i false) ≠ f (Function.update (Function.update p j c) i true)

def nc (f : BF n) : Prop := ∃ y y', f y ≠ f y'

def OptI (f : BF n) (b : ℕ) (i j : Fin n) (s u : Bool) : Prop := dep f i j (!u) ∧
  ((nc (rs f i (!s)) ∧ ∃ b', b ≤ b' + 3 ∧ LB (rs f i (!s)) b') ∨
    (nc (rs f i s) ∧ ∃ b', b ≤ b' + 2 ∧ LB (rs f i s) b'))

lemma first_gate {ι : Type} : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (f : ι → Bool), Run t S f → K S f ∨
    ∃ (t' : ℕ) (a b : ι → Bool), t' + 1 ≤ t ∧ K S a ∧ K S b ∧ ¬ K S (fun x => a x && b x) ∧
      Run t' (ins (fun x => a x && b x) S) f
  | 0, _, _, h => Or.inl h
  | t + 1, S, f, h => by
    rcases h with h | ⟨a, b, ha, hb, h⟩
    · rcases first_gate t S f h with h | ⟨t', a, b, ht, ha, hb, hn, hr⟩
      · exact Or.inl h
      · exact Or.inr ⟨t', a, b, by omega, ha, hb, hn, hr⟩
    · by_cases hk : K S (fun x => a x && b x)
      · have h2 : Run t S f := Run_map (fun x => x) t _ S f (by
          rintro w (rfl | hw)
          · exact hk
          · exact Or.inr (Or.inl hw)) h
        rcases first_gate t S f h2 with h | ⟨t', a, b, ht, ha, hb, hn, hr⟩
        · exact Or.inl h
        · exact Or.inr ⟨t', a, b, by omega, ha, hb, hn, hr⟩
      · exact Or.inr ⟨t, a, b, le_rfl, ha, hb, hk, h⟩

lemma lift_run {ι κ : Type} (τ : ι → κ) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), (∀ w, S w → ∃ W, K S' W ∧ ∀ x, W (τ x) = w x) → Run t S f →
    ∃ F, Run t S' F ∧ ∀ x, F (τ x) = f x
  | 0, S, S', f, h, hr => by
    rcases hr with ⟨c, rfl⟩ | hr | hr
    · exact ⟨fun _ => c, Or.inl ⟨c, rfl⟩, fun _ => rfl⟩
    · exact h f hr
    · obtain ⟨W, hW, e⟩ := h _ hr
      refine ⟨fun y => !W y, K_not hW, fun x => ?_⟩
      show (!W (τ x)) = _
      rw [e x]; simp
  | t + 1, S, S', f, h, hr => by
    have hK : ∀ w, K S w → ∃ W, K S' W ∧ ∀ x, W (τ x) = w x := by
      intro w hw
      rcases hw with ⟨c, rfl⟩ | hw | hw
      · exact ⟨fun _ => c, Or.inl ⟨c, rfl⟩, fun _ => rfl⟩
      · exact h w hw
      · obtain ⟨W, hW, e⟩ := h _ hw
        refine ⟨fun y => !W y, K_not hW, fun x => ?_⟩
        show (!W (τ x)) = _
        rw [e x]; simp
    rcases hr with hr | ⟨a, b, ha, hb, hr⟩
    · obtain ⟨F, hF, e⟩ := lift_run τ t S S' f h hr
      exact ⟨F, Or.inl hF, e⟩
    · obtain ⟨A, hA, ea⟩ := hK a ha
      obtain ⟨B, hB, eb⟩ := hK b hb
      obtain ⟨F, hF, e⟩ := lift_run τ t (ins (fun x => a x && b x) S) (ins (fun y => A y && B y) S') f (by
        rintro w (rfl | hw)
        · exact ⟨_, K_new _, fun x => by rw [ea, eb]⟩
        · obtain ⟨W, hW, ew⟩ := h w hw
          exact ⟨W, K_ins hW, ew⟩) hr
      exact ⟨F, Or.inr ⟨A, B, hA, hB, hF⟩, e⟩

def VP (n : ℕ) : ((Fin n → Bool) × Bool → Bool) → Prop :=
  fun W => (∃ k : Fin n, W = fun y => y.1 k) ∨ W = fun y => y.2

lemma opt_bound (f : BF n) (b : ℕ) (i j : Fin n) (hij : i ≠ j) (s u : Bool) (t : ℕ)
    (hr : Run t (ins (fun x => lit i s x && lit j u x) (Vars n)) f) (ho : OptI f b i j s u)
    (ih : Run t (Vars n) f → b ≤ t + 1) : b ≤ t + 1 := by
  obtain ⟨⟨p0, hdep⟩, hopt⟩ := ho
  set z : BF n := fun x => lit i s x && lit j u x with hz
  obtain ⟨F, hF, e⟩ := lift_run (fun x => (x, z x)) t _ (VP n) f (by
    rintro w (rfl | ⟨k, rfl⟩)
    · exact ⟨fun y => y.2, Or.inr (Or.inl (Or.inr rfl)), fun x => rfl⟩
    · exact ⟨fun y => y.1 k, Or.inr (Or.inl (Or.inl ⟨k, rfl⟩)), fun x => rfl⟩) hr
  have zi : ∀ y, z (Function.update y i (!s)) = false := by
    intro y; cases s <;> simp [hz, lit]
  have zj : ∀ y c, z (Function.update (Function.update y j (!u)) i c) = false := by
    intro y c
    have : Function.update (Function.update y j (!u)) i c j = !u := by
      rw [Function.update_of_ne hij.symm, Function.update_self]
    simp only [hz, lit, this]
    cases u <;> simp
  have dF : ∀ c, F (Function.update (Function.update p0 j (!u)) i c, false) =
      f (Function.update (Function.update p0 j (!u)) i c) := by
    intro c
    have := e (Function.update (Function.update p0 j (!u)) i c)
    rw [zj p0 c] at this
    exact this
  rcases hopt with ⟨⟨y, y', hnc⟩, b', hb, hL⟩ | ⟨⟨y, y', hnc⟩, b', hb, hL⟩
  · have iF : ∀ y, F (Function.update y i (!s), false) = rs f i (!s) y := by
      intro y
      have := e (Function.update y i (!s))
      rw [zi y] at this
      exact this
    by_cases hd : ∃ x0, F (x0, false) ≠ F (x0, true)
    · obtain ⟨x0, hx0⟩ := hd
      obtain ⟨t1, h1, r1⟩ := kill1 (fun x : Fin n → Bool => (x, false)) (x0, false) (x0, true) (x0, false) t
        (VP n) (Vars n) F (by
          rintro W (⟨k, rfl⟩ | rfl) hW y
          · exact absurd rfl hW
          · rfl) (by
          rintro W (⟨k, rfl⟩ | rfl)
          · exact Or.inr (Or.inl ⟨k, rfl⟩)
          · exact Or.inl ⟨false, rfl⟩) hx0
        ⟨Function.update y i (!s), Function.update y' i (!s), by rw [iF, iF]; exact hnc⟩ hF
      obtain ⟨t2, h2, r2⟩ := kill1 _ _ _ _ t1 _ (Vars n) (fun x => F (x, false))
        (vars_cl i (!s) (Function.update p0 j (!u))) (vars_rs i (!s))
        (by simp only [dF]; exact hdep) ⟨y, y', by simp only [iF]; exact hnc⟩ r1
      have e3 : (fun y => F (Function.update y i (!s), false)) = rs f i (!s) := funext iF
      have := hL t2 (e3 ▸ r2)
      omega
    · have hc : ∀ x, F (x, z x) = F (x, false) := by
        intro x
        by_contra hx
        cases h : z x
        · rw [h] at hx; exact hx rfl
        · rw [h] at hx; exact hd ⟨x, fun h' => hx h'.symm⟩
      have e4 : (fun x : Fin n → Bool => F (x, false)) = f := funext fun x => (hc x).symm.trans (e x)
      apply ih
      rw [← e4]
      refine Run_map (fun x : Fin n → Bool => (x, false)) t (VP n) _ F ?_ hF
      rintro W (⟨k, rfl⟩ | rfl)
      · exact Or.inr (Or.inl ⟨k, rfl⟩)
      · exact Or.inl ⟨false, rfl⟩
  · have iF : ∀ y, F (Function.update y i s, lit j u y) = rs f i s y := by
      intro y
      have h1 := e (Function.update y i s)
      have h2 : z (Function.update y i s) = lit j u y := by
        simp only [hz, lit, Function.update_self, Function.update_of_ne hij.symm]
        cases s <;> simp
      rw [h2] at h1
      exact h1
    obtain ⟨t1, h1, r1⟩ := kill1 (fun y : Fin n → Bool => (Function.update y i s, lit j u y))
      (Function.update (Function.update p0 j (!u)) i false, false)
      (Function.update (Function.update p0 j (!u)) i true, false)
      (Function.update (Function.update p0 j (!u)) i s, false) t (VP n) (Vars n) F (by
        rintro W (⟨k, rfl⟩ | rfl) hW y
        · exact vars_cl i s (Function.update p0 j (!u)) _ ⟨k, rfl⟩ hW y
        · exact absurd rfl hW) (by
        rintro W (⟨k, rfl⟩ | rfl)
        · exact vars_rs i s _ ⟨k, rfl⟩
        · exact lit_K j u) (by rw [dF, dF]; exact hdep) ⟨y, y', by rw [iF, iF]; exact hnc⟩ hF
    have e3 : (fun y => F (Function.update y i s, lit j u y)) = rs f i s := funext iF
    have := hL t1 (e3 ▸ r1)
    omega

lemma rule3 (f : BF n) (b : ℕ) (E : Fin n → Bool) (hE : ∀ x, f (fun k => E k && x k) = f x)
    (h0 : ∃ i j : Fin n, i < j ∧ E i = true ∧ E j = true)
    (h : ∀ i j : Fin n, i < j → E i = true → E j = true → ∀ s u : Bool,
      OptI f b i j s u ∨ OptI f b j i u s) : LB f b := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hr
    have hb : ∀ t', t' + 1 ≤ t → Run t' (Vars n) f → b ≤ t' + 1 := fun t' h1 h3 => by
      have := ih t' (by omega) h3
      omega
    have hr2 : Run t (VE E) f := by
      have := Run_map (fun (x : Fin n → Bool) (k : Fin n) => E k && x k) t (Vars n) (VE E) f (by
        rintro w ⟨k, rfl⟩
        cases hk : E k
        · exact Or.inl ⟨false, funext fun x => by simp [hk]⟩
        · exact Or.inr (Or.inl ⟨k, hk, funext fun x => by simp [hk]⟩)) hr
      have e : (fun x : Fin n → Bool => f (fun k => E k && x k)) = f := funext hE
      rw [e] at this
      exact this
    rcases first_gate t _ f hr2 with hkE | ⟨t', a, c, ht, ha, hc, hn, hrE⟩
    · exfalso
      have hk : K (Vars n) f := by
        rcases hkE with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (VE_sub h))
        · exact Or.inr (Or.inr (VE_sub h))
      have key : ∀ i j s u, ¬ OptI f b i j s u := by
        rintro i j s u ⟨⟨p, hd⟩, ⟨⟨y, y', hy⟩, _⟩ | ⟨⟨y, y', hy⟩, _⟩⟩
        · exact hy ((Cl_K (vars_cl i (!s) _) hk hd y).trans (Cl_K (vars_cl i (!s) _) hk hd y').symm)
        · exact hy ((Cl_K (vars_cl i s _) hk hd y).trans (Cl_K (vars_cl i s _) hk hd y').symm)
      obtain ⟨i0, j0, hlt, hi0, hj0⟩ := h0
      rcases h i0 j0 hlt hi0 hj0 true true with ho | ho
      · exact key _ _ _ _ ho
      · exact key _ _ _ _ ho
    · have comm : ∀ a c : BF n, (fun x => a x && c x) = fun x => c x && a x := fun a c =>
        funext fun x => Bool.and_comm _ _
      rcases K_lit ha with hca | ⟨i, s, hi, rfl⟩
      · exact absurd (K_and hca hc) hn
      have hr' : Run t' (ins (fun x => lit i s x && c x) (Vars n)) f := by
        refine Run_map (fun x => x) t' _ _ f ?_ hrE
        rintro w (rfl | hw)
        · exact K_new _
        · exact Or.inr (Or.inl (Or.inr (VE_sub hw)))
      rcases K_lit hc with hcc | ⟨j, u, hj, rfl⟩
      · exact absurd (comm _ _ ▸ K_and hcc ha) hn
      by_cases hij : i = j
      · subst hij
        exfalso
        apply hn
        by_cases hsu : s = u
        · subst hsu
          have : (fun x => lit i s x && lit i s x) = lit i s := funext fun x => Bool.and_self _
          rw [this]; exact lit_KE hi s
        · refine Or.inl ⟨false, funext fun x => ?_⟩
          cases s <;> cases u <;> cases hx : x i <;> simp_all [lit]
      have fin : ∀ i j s u, i ≠ j → Run t' (ins (fun x => lit i s x && lit j u x) (Vars n)) f →
          OptI f b i j s u ∨ OptI f b j i u s → b ≤ t' + 1 := by
        intro i j s u hij hr' ho
        rcases ho with ho | ho
        · exact opt_bound f b i j hij s u t' hr' ho (hb t' ht)
        · rw [comm] at hr'
          exact opt_bound f b j i (Ne.symm hij) u s t' hr' ho (hb t' ht)
      have : b ≤ t' + 1 := by
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact fin i j s u hij hr' (h i j hlt hi hj s u)
        · exact fin i j s u hij hr' (h j i hlt hj hi u s).symm
      omega

def depB (f : BF n) (i j : Fin n) (c : Bool) : Bool := (List.range (2 ^ n)).any fun p =>
  Bool.xor (f (Function.update (Function.update (pt n p) j c) i false))
    (f (Function.update (Function.update (pt n p) j c) i true))

def ncB (f : BF n) : Bool := (List.range (2 ^ n)).any fun p => Bool.xor (f (pt n p)) (f (pt n 0))

def optB (f : BF n) (b : ℕ) (V : List (Fin n × Bool × ℕ)) (i j : Fin n) (s u : Bool) : Bool :=
  depB f i j (!u) && V.any fun e => decide (e.1 = i) && ((ncB (rs f i (!s)) && decide (e.2.1 = !s) && decide (b ≤ e.2.2 + 3)) ||
    (ncB (rs f i s) && decide (e.2.1 = s) && decide (b ≤ e.2.2 + 2)))

lemma xor_ne {p q : Bool} (h : Bool.xor p q = true) : p ≠ q := by
  cases p <;> cases q <;> simp_all

lemma optB_sound {f : BF n} {b : ℕ} {V : List (Fin n × Bool × ℕ)} (hV : ∀ e ∈ V, LB (rs f e.1 e.2.1) e.2.2)
    {i j : Fin n} {s u : Bool} (h : optB f b V i j s u = true) : OptI f b i j s u := by
  simp only [optB, Bool.and_eq_true, List.any_eq_true, depB, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨p, _, hp⟩, ⟨i', c, b'⟩, he, hi, ho⟩ := h
  simp only at hi ho
  subst hi
  have hL := hV _ he
  simp only at hL
  refine ⟨⟨_, xor_ne hp⟩, ?_⟩
  have hnc : ∀ g : BF n, ncB g = true → nc g := by
    intro g hg
    simp only [ncB, List.any_eq_true] at hg
    obtain ⟨q, _, hq⟩ := hg
    exact ⟨_, _, xor_ne hq⟩
  rcases ho with ⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩
  · left
    exact ⟨hnc _ h1, b', h3, h2 ▸ hL⟩
  · right
    exact ⟨hnc _ h1, b', h3, h2 ▸ hL⟩

lemma rule3B (f : BF n) (b : ℕ) (E : Fin n → Bool) (hE : ∀ x, f (fun k => E k && x k) = f x)
    (h0 : ∃ i j : Fin n, i < j ∧ E i = true ∧ E j = true) (V : List (Fin n × Bool × ℕ))
    (hV : ∀ e ∈ V, LB (rs f e.1 e.2.1) e.2.2)
    (h : (List.finRange n).all (fun i => (List.finRange n).all fun j => !(decide (i < j) && E i && E j) ||
      [true, false].all fun s => [true, false].all fun u => optB f b V i j s u || optB f b V j i u s) = true) :
    LB f b := by
  refine rule3 f b E hE h0 fun i j hij hi hj s u => ?_
  have h1 := List.all_eq_true.mp (List.all_eq_true.mp h i (List.mem_finRange i)) j (List.mem_finRange j)
  have h3 : (decide (i < j) && E i && E j) = true := by rw [decide_eq_true hij, hi, hj]; rfl
  rw [h3] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  have h4 := List.all_eq_true.mp (List.all_eq_true.mp h1 s (by cases s <;> simp)) u (by cases u <;> simp)
  rcases (Bool.or_eq_true _ _).mp h4 with h5 | h5
  · exact Or.inl (optB_sound hV h5)
  · exact Or.inr (optB_sound hV h5)

end First

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true

def bc (gs : List Gate) : ℕ := (gs.filter isBinary).length

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

section Compile
variable {n : ℕ}

def rd (ws : List (BF n)) (i : ℕ) : BF n := fun x => (ws.map fun w => w x).getD i false

lemma rd_K {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (i : ℕ) :
    K S (rd ws i) := by
  by_cases h : i < ws.length
  · have : rd ws i = ws[i] := by
      funext x
      simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rw [this]
    exact hw _ (List.getElem_mem h)
  · refine Or.inl ⟨false, ?_⟩
    funext x
    simp [rd, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

lemma gate_run {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (g : Gate)
    (hg : legal g) (z : BF n)
    (hz : z = fun x => g.op.eval (g.inputs.map fun i => rd ws i x)) :
    K S z ∨ (isBinary g = true ∧ ∃ a b : BF n, K S a ∧ K S b ∧ K (ins (fun x => a x && b x) S) z) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  subst hz
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩
  · left
    rcases hop with rfl | rfl | rfl
    · exact Or.inl ⟨true, rfl⟩
    · exact Or.inl ⟨false, rfl⟩
    · exact Or.inl ⟨true, rfl⟩
  · left
    rcases hop with rfl | rfl | rfl
    · have e : (fun x => GateOp.eval .and ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · have e : (fun x => GateOp.eval .or ([i].map fun i => rd ws i x)) = rd ws i :=
        funext fun x => by simp [GateOp.eval]
      simp only [e]; exact rd_K hw i
    · exact K_not (rd_K hw i)
  · rcases hop with rfl | rfl | rfl
    · right
      refine ⟨rfl, rd ws i, rd ws j, rd_K hw i, rd_K hw j, ?_⟩
      have e : (fun x => GateOp.eval .and ([i, j].map fun i => rd ws i x)) =
          fun x => rd ws i x && rd ws j x := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_new _
    · right
      refine ⟨rfl, _, _, K_not (rd_K hw i), K_not (rd_K hw j), ?_⟩
      have e : (fun x => GateOp.eval .or ([i, j].map fun i => rd ws i x)) =
          fun x => !(!rd ws i x && !rd ws j x) := funext fun x => by simp [GateOp.eval]
      simp only [e]; exact K_not (K_new _)
    · left
      exact K_not (rd_K hw i)
  · simp at cap

lemma compile (out : ℕ) : ∀ (gs : List Gate) (ws : List (BF n)) (S : BF n → Prop),
    (∀ g ∈ gs, legal g) → (∀ w ∈ ws, K S w) →
    Run (bc gs) S (fun x => (gs.foldl step (ws.map fun w => w x)).getD out false)
  | [], ws, S, _, hw => rd_K hw out
  | g :: gs, ws, S, hg, hw => by
    set z : BF n := fun x => g.op.eval (g.inputs.map fun i => rd ws i x) with hz
    have hst : ∀ x, step (ws.map fun w => w x) g = (ws ++ [z]).map fun w => w x := by
      intro x
      simp [step, hz, rd]
    have hfold : (fun x => ((g :: gs).foldl step (ws.map fun w => w x)).getD out false) =
        fun x => (gs.foldl step ((ws ++ [z]).map fun w => w x)).getD out false := by
      funext x
      rw [List.foldl_cons, hst x]
    rw [hfold]
    have tail := fun S' h => compile out gs (ws ++ [z]) S' (fun g' h' => hg g' (by simp [h'])) h
    have ext : ∀ S' : BF n → Prop, (∀ w ∈ ws, K S' w) → K S' z → ∀ w ∈ ws ++ [z], K S' w := by
      intro S' h1 h2 w hm
      rcases List.mem_append.mp hm with hm | hm
      · exact h1 w hm
      · exact (List.mem_singleton.mp hm) ▸ h2
    have hle : bc gs ≤ bc (g :: gs) := by
      unfold bc
      rw [List.filter_cons]
      split <;> simp
    rcases gate_run hw g (hg g (by simp)) z hz with h | ⟨hb, a, b, ha, hb2, h⟩
    · exact Run_le hle (tail S (ext S hw h))
    · have hbc : bc (g :: gs) = bc gs + 1 := by simp [bc, hb]
      rw [hbc]
      exact Or.inr ⟨a, b, ha, hb2, tail _ (ext _ (fun w hm => K_ins (hw w hm)) h)⟩

lemma bound_of_LB (F : BF n) (b : ℕ) (h : LB F b) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin n → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) : b ≤ bc gs := by
  apply h
  have hr := compile o gs (List.ofFn fun i : Fin n => fun x : Fin n → Bool => x i) (Vars n) hg (by
    intro w hw
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).mp hw
    exact Or.inr (Or.inl ⟨i, rfl⟩))
  have e : (fun x : Fin n → Bool => (gs.foldl step ((List.ofFn fun i : Fin n =>
      fun x : Fin n → Bool => x i).map fun w => w x)).getD o false) = F := by
    funext x
    rw [← he x, List.map_ofFn]
    rfl
  rw [e] at hr
  exact hr

end Compile

-- Gate elimination rules from merged PEqualNP L-meta-27460 (Apache-2.0).
def v1 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v2 : BF 8 := fun x => (x 1 && x 4) || (x 3 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v3 : BF 8 := fun x => (x 1 && x 4) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v4 : BF 8 := fun x => (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 6 && x 7)

def v5 : BF 8 := fun x => (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 6 && x 7)

def v6 : BF 8 := fun x => (x 1 && x 6) || (x 1 && x 7) || (x 6 && x 7)

def v7 : BF 8 := fun x => (x 6 && x 7)

def v8 : BF 8 := fun x => (x 7)

lemma v8_lb : LB v8 0 := fun t _ => Nat.zero_le t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v7_6_true : rs v7 6 true = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v7_lb : LB v7 1 := rule1 v7 6 true 0 128 0 255 (by decide +kernel) (by decide +kernel) (v7_6_true.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v6_1_false : rs v6 1 false = v7 := by funext x; revert x; decide +kernel

def v9 : BF 8 := fun x => (x 6) || (x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v9_6_false : rs v9 6 false = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v9_lb : LB v9 1 := rule1 v9 6 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v9_6_false.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v6_1_true : rs v6 1 true = v9 := by funext x; revert x; decide +kernel

def v10 : BF 8 := fun x => (x 1 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v10_1_true : rs v10 1 true = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v10_lb : LB v10 1 := rule1 v10 1 true 0 128 0 255 (by decide +kernel) (by decide +kernel) (v10_1_true.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v6_6_false : rs v6 6 false = v10 := by funext x; revert x; decide +kernel

def v11 : BF 8 := fun x => (x 1) || (x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v11_1_false : rs v11 1 false = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v11_lb : LB v11 1 := rule1 v11 1 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v11_1_false.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v6_6_true : rs v6 6 true = v11 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v6_lb : LB v6 4 := rule3B v6 4 (fun i : Fin 8 => ((194 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨1, 6, by decide +kernel⟩ [(1, false, 1), (1, true, 1), (6, false, 1), (6, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v6_1_false.symm ▸ v7_lb)
    · exact (v6_1_true.symm ▸ v9_lb)
    · exact (v6_6_false.symm ▸ v10_lb)
    · exact (v6_6_true.symm ▸ v11_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v5_2_false : rs v5 2 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v5_lb : LB v5 5 := rule1 v5 2 false 4 64 0 255 (by decide +kernel) (by decide +kernel) (v5_2_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4_5_false : rs v4 5 false = v5 := by funext x; revert x; decide +kernel

def v12 : BF 8 := fun x => (x 2) || (x 1 && x 6) || (x 1 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v12_2_false : rs v12 2 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v12_lb : LB v12 5 := rule1 v12 2 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v12_2_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4_5_true : rs v4 5 true = v12 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v4_lb : LB v4 7 := rule2 v4 5 5 4 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v4_5_false.symm ▸ v5_lb) (v4_5_true.symm ▸ v12_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3_4_false : rs v3 4 false = v4 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v3_lb : LB v3 8 := rule1 v3 4 false 7 2 0 255 (by decide +kernel) (by decide +kernel) (v3_4_false.symm ▸ v4_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_3_false : rs v2 3 false = v3 := by funext x; revert x; decide +kernel

def v13 : BF 8 := fun x => (x 3 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 2 && x 6) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v14 : BF 8 := fun x => (x 3 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v15 : BF 8 := fun x => (x 3 && x 5) || (x 3 && x 6) || (x 3 && x 7) || (x 6 && x 7)

def v16 : BF 8 := fun x => (x 3 && x 6) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v16_3_false : rs v16 3 false = v7 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v16_3_true : rs v16 3 true = v9 := by funext x; revert x; decide +kernel

def v17 : BF 8 := fun x => (x 3 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v17_3_true : rs v17 3 true = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v17_lb : LB v17 1 := rule1 v17 3 true 0 128 0 255 (by decide +kernel) (by decide +kernel) (v17_3_true.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v16_6_false : rs v16 6 false = v17 := by funext x; revert x; decide +kernel

def v18 : BF 8 := fun x => (x 3) || (x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v18_3_false : rs v18 3 false = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v18_lb : LB v18 1 := rule1 v18 3 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v18_3_false.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v16_6_true : rs v16 6 true = v18 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v16_lb : LB v16 4 := rule3B v16 4 (fun i : Fin 8 => ((200 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨3, 6, by decide +kernel⟩ [(3, false, 1), (3, true, 1), (6, false, 1), (6, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v16_3_false.symm ▸ v7_lb)
    · exact (v16_3_true.symm ▸ v9_lb)
    · exact (v16_6_false.symm ▸ v17_lb)
    · exact (v16_6_true.symm ▸ v18_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v15_5_false : rs v15 5 false = v16 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v15_lb : LB v15 5 := rule1 v15 5 false 4 8 0 255 (by decide +kernel) (by decide +kernel) (v15_5_false.symm ▸ v16_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v14_4_false : rs v14 4 false = v15 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v14_lb : LB v14 6 := rule1 v14 4 false 5 8 0 255 (by decide +kernel) (by decide +kernel) (v14_4_false.symm ▸ v15_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v13_2_false : rs v13 2 false = v14 := by funext x; revert x; decide +kernel

def v19 : BF 8 := fun x => (x 3 && x 4) || (x 5) || (x 6) || (x 3 && x 7) || (x 4 && x 7)

def v20 : BF 8 := fun x => (x 3 && x 4) || (x 6) || (x 3 && x 7) || (x 4 && x 7)

def v21 : BF 8 := fun x => (x 3 && x 4) || (x 3 && x 7) || (x 4 && x 7)

def v22 : BF 8 := fun x => (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v22_4_true : rs v22 4 true = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v22_lb : LB v22 1 := rule1 v22 4 true 0 128 0 255 (by decide +kernel) (by decide +kernel) (v22_4_true.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v21_3_false : rs v21 3 false = v22 := by funext x; revert x; decide +kernel

def v23 : BF 8 := fun x => (x 4) || (x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v23_4_false : rs v23 4 false = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v23_lb : LB v23 1 := rule1 v23 4 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v23_4_false.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v21_3_true : rs v21 3 true = v23 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v21_4_false : rs v21 4 false = v17 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v21_4_true : rs v21 4 true = v18 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v21_lb : LB v21 4 := rule3B v21 4 (fun i : Fin 8 => ((152 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨3, 4, by decide +kernel⟩ [(3, false, 1), (3, true, 1), (4, false, 1), (4, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v21_3_false.symm ▸ v22_lb)
    · exact (v21_3_true.symm ▸ v23_lb)
    · exact (v21_4_false.symm ▸ v17_lb)
    · exact (v21_4_true.symm ▸ v18_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v20_6_false : rs v20 6 false = v21 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v20_lb : LB v20 5 := rule1 v20 6 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v20_6_false.symm ▸ v21_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v19_5_false : rs v19 5 false = v20 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v19_lb : LB v19 6 := rule1 v19 5 false 5 0 0 255 (by decide +kernel) (by decide +kernel) (v19_5_false.symm ▸ v20_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v13_2_true : rs v13 2 true = v19 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v13_lb : LB v13 8 := rule2 v13 2 6 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v13_2_false.symm ▸ v14_lb) (v13_2_true.symm ▸ v19_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_1_false : rs v2 1 false = v13 := by funext x; revert x; decide +kernel

def v24 : BF 8 := fun x => (x 1 && x 4) || (x 3 && x 4) || (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v25 : BF 8 := fun x => (x 3 && x 5) || (x 1 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 6 && x 7)

def v26 : BF 8 := fun x => (x 1 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v26_1_false : rs v26 1 false = v16 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v26_lb : LB v26 5 := rule1 v26 1 false 4 64 0 255 (by decide +kernel) (by decide +kernel) (v26_1_false.symm ▸ v16_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v25_5_false : rs v25 5 false = v26 := by funext x; revert x; decide +kernel

def v27 : BF 8 := fun x => (x 3) || (x 1 && x 6) || (x 1 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v27_3_false : rs v27 3 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v27_lb : LB v27 5 := rule1 v27 3 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v27_3_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v25_5_true : rs v25 5 true = v27 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v25_lb : LB v25 7 := rule2 v25 5 5 8 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v25_5_false.symm ▸ v26_lb) (v25_5_true.symm ▸ v27_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v24_4_false : rs v24 4 false = v25 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v24_lb : LB v24 8 := rule1 v24 4 false 7 2 0 255 (by decide +kernel) (by decide +kernel) (v24_4_false.symm ▸ v25_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_2_false : rs v2 2 false = v24 := by funext x; revert x; decide +kernel

def v28 : BF 8 := fun x => (x 1 && x 4) || (x 3 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7)

def v29 : BF 8 := fun x => (x 3 && x 4) || (x 2 && x 5) || (x 3 && x 5) || (x 3 && x 7) || (x 4 && x 7)

def v30 : BF 8 := fun x => (x 3 && x 4) || (x 3 && x 5) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v30_5_false : rs v30 5 false = v21 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v30_lb : LB v30 5 := rule1 v30 5 false 4 8 0 255 (by decide +kernel) (by decide +kernel) (v30_5_false.symm ▸ v21_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v29_2_false : rs v29 2 false = v30 := by funext x; revert x; decide +kernel

def v31 : BF 8 := fun x => (x 3 && x 4) || (x 5) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v31_5_false : rs v31 5 false = v21 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v31_lb : LB v31 5 := rule1 v31 5 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v31_5_false.symm ▸ v21_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v29_2_true : rs v29 2 true = v31 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v29_lb : LB v29 7 := rule2 v29 2 5 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v29_2_false.symm ▸ v30_lb) (v29_2_true.symm ▸ v31_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v28_1_false : rs v28 1 false = v29 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v28_lb : LB v28 8 := rule1 v28 1 false 7 16 0 255 (by decide +kernel) (by decide +kernel) (v28_1_false.symm ▸ v29_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_6_false : rs v2 6 false = v28 := by funext x; revert x; decide +kernel

def v32 : BF 8 := fun x => (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v32_2_false : rs v32 2 false = v25 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v32_lb : LB v32 8 := rule1 v32 2 false 7 32 0 255 (by decide +kernel) (by decide +kernel) (v32_2_false.symm ▸ v25_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_4_false : rs v2 4 false = v32 := by funext x; revert x; decide +kernel

def v33 : BF 8 := fun x => (x 1 && x 4) || (x 3 && x 4) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v34 : BF 8 := fun x => (x 3 && x 4) || (x 2 && x 6) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v35 : BF 8 := fun x => (x 3 && x 4) || (x 3 && x 6) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v35_4_false : rs v35 4 false = v16 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v35_lb : LB v35 5 := rule1 v35 4 false 4 8 0 255 (by decide +kernel) (by decide +kernel) (v35_4_false.symm ▸ v16_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v34_2_false : rs v34 2 false = v35 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v34_2_true : rs v34 2 true = v20 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v34_lb : LB v34 7 := rule2 v34 2 5 64 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v34_2_false.symm ▸ v35_lb) (v34_2_true.symm ▸ v20_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v33_1_false : rs v33 1 false = v34 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v33_lb : LB v33 8 := rule1 v33 1 false 7 16 0 255 (by decide +kernel) (by decide +kernel) (v33_1_false.symm ▸ v34_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_5_false : rs v2 5 false = v33 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v2_lb : LB v2 10 := rule3B v2 10 (fun i : Fin 8 => ((254 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨1, 2, by decide +kernel⟩ [(3, false, 8), (1, false, 8), (2, false, 8), (6, false, 8), (4, false, 8), (5, false, 8)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (v2_3_false.symm ▸ v3_lb)
    · exact (v2_1_false.symm ▸ v13_lb)
    · exact (v2_2_false.symm ▸ v24_lb)
    · exact (v2_6_false.symm ▸ v28_lb)
    · exact (v2_4_false.symm ▸ v32_lb)
    · exact (v2_5_false.symm ▸ v33_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_0_false : rs v1 0 false = v2 := by funext x; revert x; decide +kernel

def v36 : BF 8 := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_0_false : rs v36 0 false = v3 := by funext x; revert x; decide +kernel

def v37 : BF 8 := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v38 : BF 8 := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v39 : BF 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 0 && x 7) || (x 6 && x 7)

def v40 : BF 8 := fun x => (x 0 && x 6) || (x 0 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v40_0_false : rs v40 0 false = v7 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v40_0_true : rs v40 0 true = v9 := by funext x; revert x; decide +kernel

def v41 : BF 8 := fun x => (x 0 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v41_0_true : rs v41 0 true = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v41_lb : LB v41 1 := rule1 v41 0 true 0 128 0 255 (by decide +kernel) (by decide +kernel) (v41_0_true.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v40_6_false : rs v40 6 false = v41 := by funext x; revert x; decide +kernel

def v42 : BF 8 := fun x => (x 0) || (x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v42_0_false : rs v42 0 false = v8 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v42_lb : LB v42 1 := rule1 v42 0 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v42_0_false.symm ▸ v8_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v40_6_true : rs v40 6 true = v42 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v40_lb : LB v40 4 := rule3B v40 4 (fun i : Fin 8 => ((193 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 6, by decide +kernel⟩ [(0, false, 1), (0, true, 1), (6, false, 1), (6, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v40_0_false.symm ▸ v7_lb)
    · exact (v40_0_true.symm ▸ v9_lb)
    · exact (v40_6_false.symm ▸ v41_lb)
    · exact (v40_6_true.symm ▸ v42_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v39_5_false : rs v39 5 false = v40 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v39_lb : LB v39 5 := rule1 v39 5 false 4 1 0 255 (by decide +kernel) (by decide +kernel) (v39_5_false.symm ▸ v40_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v38_4_false : rs v38 4 false = v39 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v38_lb : LB v38 6 := rule1 v38 4 false 5 1 0 255 (by decide +kernel) (by decide +kernel) (v38_4_false.symm ▸ v39_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v37_2_false : rs v37 2 false = v38 := by funext x; revert x; decide +kernel

def v43 : BF 8 := fun x => (x 0 && x 4) || (x 5) || (x 6) || (x 0 && x 7) || (x 4 && x 7)

def v44 : BF 8 := fun x => (x 0 && x 4) || (x 6) || (x 0 && x 7) || (x 4 && x 7)

def v45 : BF 8 := fun x => (x 0 && x 4) || (x 0 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v45_0_false : rs v45 0 false = v22 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v45_0_true : rs v45 0 true = v23 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v45_4_false : rs v45 4 false = v41 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v45_4_true : rs v45 4 true = v42 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v45_lb : LB v45 4 := rule3B v45 4 (fun i : Fin 8 => ((145 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 4, by decide +kernel⟩ [(0, false, 1), (0, true, 1), (4, false, 1), (4, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v45_0_false.symm ▸ v22_lb)
    · exact (v45_0_true.symm ▸ v23_lb)
    · exact (v45_4_false.symm ▸ v41_lb)
    · exact (v45_4_true.symm ▸ v42_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v44_6_false : rs v44 6 false = v45 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v44_lb : LB v44 5 := rule1 v44 6 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v44_6_false.symm ▸ v45_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v43_5_false : rs v43 5 false = v44 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v43_lb : LB v43 6 := rule1 v43 5 false 5 0 0 255 (by decide +kernel) (by decide +kernel) (v43_5_false.symm ▸ v44_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v37_2_true : rs v37 2 true = v43 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v37_lb : LB v37 8 := rule2 v37 2 6 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v37_2_false.symm ▸ v38_lb) (v37_2_true.symm ▸ v43_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_1_false : rs v36 1 false = v37 := by funext x; revert x; decide +kernel

def v46 : BF 8 := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v47 : BF 8 := fun x => (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 6 && x 7)

def v48 : BF 8 := fun x => (x 0 && x 6) || (x 1 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v48_0_false : rs v48 0 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v48_lb : LB v48 5 := rule1 v48 0 false 4 64 0 255 (by decide +kernel) (by decide +kernel) (v48_0_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v47_5_false : rs v47 5 false = v48 := by funext x; revert x; decide +kernel

def v49 : BF 8 := fun x => (x 0) || (x 1 && x 6) || (x 1 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v49_0_false : rs v49 0 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v49_lb : LB v49 5 := rule1 v49 0 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v49_0_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v47_5_true : rs v47 5 true = v49 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v47_lb : LB v47 7 := rule2 v47 5 5 1 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v47_5_false.symm ▸ v48_lb) (v47_5_true.symm ▸ v49_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v46_4_false : rs v46 4 false = v47 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v46_lb : LB v46 8 := rule1 v46 4 false 7 1 0 255 (by decide +kernel) (by decide +kernel) (v46_4_false.symm ▸ v47_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_2_false : rs v36 2 false = v46 := by funext x; revert x; decide +kernel

def v50 : BF 8 := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7)

def v51 : BF 8 := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 7) || (x 4 && x 7)

def v52 : BF 8 := fun x => (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v52_5_false : rs v52 5 false = v45 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v52_lb : LB v52 5 := rule1 v52 5 false 4 1 0 255 (by decide +kernel) (by decide +kernel) (v52_5_false.symm ▸ v45_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v51_2_false : rs v51 2 false = v52 := by funext x; revert x; decide +kernel

def v53 : BF 8 := fun x => (x 0 && x 4) || (x 5) || (x 0 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v53_5_false : rs v53 5 false = v45 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v53_lb : LB v53 5 := rule1 v53 5 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v53_5_false.symm ▸ v45_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v51_2_true : rs v51 2 true = v53 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v51_lb : LB v51 7 := rule2 v51 2 5 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v51_2_false.symm ▸ v52_lb) (v51_2_true.symm ▸ v53_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v50_1_false : rs v50 1 false = v51 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v50_lb : LB v50 8 := rule1 v50 1 false 7 16 0 255 (by decide +kernel) (by decide +kernel) (v50_1_false.symm ▸ v51_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_6_false : rs v36 6 false = v50 := by funext x; revert x; decide +kernel

def v54 : BF 8 := fun x => (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v54_0_false : rs v54 0 false = v4 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v54_lb : LB v54 8 := rule1 v54 0 false 7 32 0 255 (by decide +kernel) (by decide +kernel) (v54_0_false.symm ▸ v4_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_4_false : rs v36 4 false = v54 := by funext x; revert x; decide +kernel

def v55 : BF 8 := fun x => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v56 : BF 8 := fun x => (x 1 && x 4) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v57 : BF 8 := fun x => (x 1 && x 4) || (x 1 && x 6) || (x 1 && x 7) || (x 4 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v57_4_false : rs v57 4 false = v6 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v57_lb : LB v57 5 := rule1 v57 4 false 4 2 0 255 (by decide +kernel) (by decide +kernel) (v57_4_false.symm ▸ v6_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v56_2_false : rs v56 2 false = v57 := by funext x; revert x; decide +kernel

def v58 : BF 8 := fun x => (x 1 && x 4) || (x 6) || (x 1 && x 7) || (x 4 && x 7)

def v59 : BF 8 := fun x => (x 1 && x 4) || (x 1 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v59_1_false : rs v59 1 false = v22 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v59_1_true : rs v59 1 true = v23 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v59_4_false : rs v59 4 false = v10 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v59_4_true : rs v59 4 true = v11 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v59_lb : LB v59 4 := rule3B v59 4 (fun i : Fin 8 => ((146 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨1, 4, by decide +kernel⟩ [(1, false, 1), (1, true, 1), (4, false, 1), (4, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v59_1_false.symm ▸ v22_lb)
    · exact (v59_1_true.symm ▸ v23_lb)
    · exact (v59_4_false.symm ▸ v10_lb)
    · exact (v59_4_true.symm ▸ v11_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v58_6_false : rs v58 6 false = v59 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v58_lb : LB v58 5 := rule1 v58 6 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v58_6_false.symm ▸ v59_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v56_2_true : rs v56 2 true = v58 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v56_lb : LB v56 7 := rule2 v56 2 5 64 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v56_2_false.symm ▸ v57_lb) (v56_2_true.symm ▸ v58_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v55_0_false : rs v55 0 false = v56 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v55_lb : LB v55 8 := rule1 v55 0 false 7 16 0 255 (by decide +kernel) (by decide +kernel) (v55_0_false.symm ▸ v56_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_5_false : rs v36 5 false = v55 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v36_lb : LB v36 10 := rule3B v36 10 (fun i : Fin 8 => ((247 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 1, by decide +kernel⟩ [(0, false, 8), (1, false, 8), (2, false, 8), (6, false, 8), (4, false, 8), (5, false, 8)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (v36_0_false.symm ▸ v3_lb)
    · exact (v36_1_false.symm ▸ v37_lb)
    · exact (v36_2_false.symm ▸ v46_lb)
    · exact (v36_6_false.symm ▸ v50_lb)
    · exact (v36_4_false.symm ▸ v54_lb)
    · exact (v36_5_false.symm ▸ v55_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_3_false : rs v1 3 false = v36 := by funext x; revert x; decide +kernel

def v60 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v61 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v62 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 6 && x 7)

def v63 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v63_0_false : rs v63 0 false = v16 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v63_3_false : rs v63 3 false = v40 := by funext x; revert x; decide +kernel

def v64 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 7) || (x 3 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v64_0_false : rs v64 0 false = v17 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v64_0_true : rs v64 0 true = v18 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v64_3_false : rs v64 3 false = v41 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v64_3_true : rs v64 3 true = v42 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v64_lb : LB v64 4 := rule3B v64 4 (fun i : Fin 8 => ((137 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 3, by decide +kernel⟩ [(0, false, 1), (0, true, 1), (3, false, 1), (3, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v64_0_false.symm ▸ v17_lb)
    · exact (v64_0_true.symm ▸ v18_lb)
    · exact (v64_3_false.symm ▸ v41_lb)
    · exact (v64_3_true.symm ▸ v42_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v63_6_false : rs v63 6 false = v64 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v63_lb : LB v63 6 := rule3B v63 6 (fun i : Fin 8 => ((201 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 3, by decide +kernel⟩ [(0, false, 4), (3, false, 4), (6, false, 4)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact (v63_0_false.symm ▸ v16_lb)
    · exact (v63_3_false.symm ▸ v40_lb)
    · exact (v63_6_false.symm ▸ v64_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v62_5_false : rs v62 5 false = v63 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v62_lb : LB v62 7 := rule1 v62 5 false 6 1 0 255 (by decide +kernel) (by decide +kernel) (v62_5_false.symm ▸ v63_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v61_4_false : rs v61 4 false = v62 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v61_lb : LB v61 8 := rule1 v61 4 false 7 1 0 255 (by decide +kernel) (by decide +kernel) (v61_4_false.symm ▸ v62_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v60_2_false : rs v60 2 false = v61 := by funext x; revert x; decide +kernel

def v65 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 5) || (x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

def v66 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

def v67 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v67_0_false : rs v67 0 false = v21 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v67_3_false : rs v67 3 false = v45 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v67_4_false : rs v67 4 false = v64 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v67_lb : LB v67 6 := rule3B v67 6 (fun i : Fin 8 => ((153 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 3, by decide +kernel⟩ [(0, false, 4), (3, false, 4), (4, false, 4)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact (v67_0_false.symm ▸ v21_lb)
    · exact (v67_3_false.symm ▸ v45_lb)
    · exact (v67_4_false.symm ▸ v64_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v66_6_false : rs v66 6 false = v67 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v66_lb : LB v66 7 := rule1 v66 6 false 6 0 0 255 (by decide +kernel) (by decide +kernel) (v66_6_false.symm ▸ v67_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v65_5_false : rs v65 5 false = v66 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v65_lb : LB v65 8 := rule1 v65 5 false 7 0 0 255 (by decide +kernel) (by decide +kernel) (v65_5_false.symm ▸ v66_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v60_2_true : rs v60 2 true = v65 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v60_lb : LB v60 10 := rule2 v60 2 8 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v60_2_false.symm ▸ v61_lb) (v60_2_true.symm ▸ v65_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_1_false : rs v1 1 false = v60 := by funext x; revert x; decide +kernel

def v68 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v69 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_0_false : rs v69 0 false = v25 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_3_false : rs v69 3 false = v47 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_1_false : rs v69 1 false = v62 := by funext x; revert x; decide +kernel

def v70 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7)

def v71 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 7) || (x 3 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v71_5_false : rs v71 5 false = v64 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v71_lb : LB v71 5 := rule1 v71 5 false 4 1 0 255 (by decide +kernel) (by decide +kernel) (v71_5_false.symm ▸ v64_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v70_1_false : rs v70 1 false = v71 := by funext x; revert x; decide +kernel

def v72 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 7)

def v73 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5)

def v74 : BF 8 := fun x => (x 3 && x 5)

def v75 : BF 8 := fun x => (x 5)

lemma v75_lb : LB v75 0 := fun t _ => Nat.zero_le t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v74_3_true : rs v74 3 true = v75 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v74_lb : LB v74 1 := rule1 v74 3 true 0 32 0 255 (by decide +kernel) (by decide +kernel) (v74_3_true.symm ▸ v75_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v73_0_false : rs v73 0 false = v74 := by funext x; revert x; decide +kernel

def v76 : BF 8 := fun x => (x 3) || (x 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v76_3_false : rs v76 3 false = v75 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v76_lb : LB v76 1 := rule1 v76 3 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v76_3_false.symm ▸ v75_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v73_0_true : rs v73 0 true = v76 := by funext x; revert x; decide +kernel

def v77 : BF 8 := fun x => (x 0 && x 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v77_0_true : rs v77 0 true = v75 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v77_lb : LB v77 1 := rule1 v77 0 true 0 32 0 255 (by decide +kernel) (by decide +kernel) (v77_0_true.symm ▸ v75_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v73_3_false : rs v73 3 false = v77 := by funext x; revert x; decide +kernel

def v78 : BF 8 := fun x => (x 0) || (x 5)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v78_0_false : rs v78 0 false = v75 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v78_lb : LB v78 1 := rule1 v78 0 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v78_0_false.symm ▸ v75_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v73_3_true : rs v73 3 true = v78 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v73_lb : LB v73 4 := rule3B v73 4 (fun i : Fin 8 => ((41 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 3, by decide +kernel⟩ [(0, false, 1), (0, true, 1), (3, false, 1), (3, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v73_0_false.symm ▸ v74_lb)
    · exact (v73_0_true.symm ▸ v76_lb)
    · exact (v73_3_false.symm ▸ v77_lb)
    · exact (v73_3_true.symm ▸ v78_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v72_7_false : rs v72 7 false = v73 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v72_lb : LB v72 5 := rule1 v72 7 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v72_7_false.symm ▸ v73_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v70_1_true : rs v70 1 true = v72 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v70_lb : LB v70 7 := rule2 v70 1 5 128 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v70_1_false.symm ▸ v71_lb) (v70_1_true.symm ▸ v72_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_6_false : rs v69 6 false = v70 := by funext x; revert x; decide +kernel

def v79 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 3 && x 6)

def v80 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 3 && x 6)

def v81 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 6) || (x 3 && x 6)

def v82 : BF 8 := fun x => (x 3 && x 6)

def v83 : BF 8 := fun x => (x 6)

lemma v83_lb : LB v83 0 := fun t _ => Nat.zero_le t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v82_3_true : rs v82 3 true = v83 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v82_lb : LB v82 1 := rule1 v82 3 true 0 64 0 255 (by decide +kernel) (by decide +kernel) (v82_3_true.symm ▸ v83_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v81_0_false : rs v81 0 false = v82 := by funext x; revert x; decide +kernel

def v84 : BF 8 := fun x => (x 3) || (x 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v84_3_false : rs v84 3 false = v83 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v84_lb : LB v84 1 := rule1 v84 3 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v84_3_false.symm ▸ v83_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v81_0_true : rs v81 0 true = v84 := by funext x; revert x; decide +kernel

def v85 : BF 8 := fun x => (x 0 && x 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v85_0_true : rs v85 0 true = v83 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v85_lb : LB v85 1 := rule1 v85 0 true 0 64 0 255 (by decide +kernel) (by decide +kernel) (v85_0_true.symm ▸ v83_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v81_3_false : rs v81 3 false = v85 := by funext x; revert x; decide +kernel

def v86 : BF 8 := fun x => (x 0) || (x 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v86_0_false : rs v86 0 false = v83 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v86_lb : LB v86 1 := rule1 v86 0 false 0 0 0 255 (by decide +kernel) (by decide +kernel) (v86_0_false.symm ▸ v83_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v81_3_true : rs v81 3 true = v86 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v81_lb : LB v81 4 := rule3B v81 4 (fun i : Fin 8 => ((73 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 3, by decide +kernel⟩ [(0, false, 1), (0, true, 1), (3, false, 1), (3, true, 1)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact (v81_0_false.symm ▸ v82_lb)
    · exact (v81_0_true.symm ▸ v84_lb)
    · exact (v81_3_false.symm ▸ v85_lb)
    · exact (v81_3_true.symm ▸ v86_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v80_5_false : rs v80 5 false = v81 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v80_lb : LB v80 5 := rule1 v80 5 false 4 1 0 255 (by decide +kernel) (by decide +kernel) (v80_5_false.symm ▸ v81_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v79_1_false : rs v79 1 false = v80 := by funext x; revert x; decide +kernel

def v87 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 3 && x 5) || (x 6)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v87_6_false : rs v87 6 false = v73 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v87_lb : LB v87 5 := rule1 v87 6 false 4 0 0 255 (by decide +kernel) (by decide +kernel) (v87_6_false.symm ▸ v73_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v79_1_true : rs v79 1 true = v87 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v79_lb : LB v79 7 := rule2 v79 1 5 64 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v79_1_false.symm ▸ v80_lb) (v79_1_true.symm ▸ v87_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_7_false : rs v69 7 false = v79 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v69_lb : LB v69 9 := rule3B v69 9 (fun i : Fin 8 => ((235 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 1, by decide +kernel⟩ [(0, false, 7), (3, false, 7), (1, false, 7), (6, false, 7), (7, false, 7)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact (v69_0_false.symm ▸ v25_lb)
    · exact (v69_3_false.symm ▸ v47_lb)
    · exact (v69_1_false.symm ▸ v62_lb)
    · exact (v69_6_false.symm ▸ v70_lb)
    · exact (v69_7_false.symm ▸ v79_lb)) (by decide +kernel)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v68_4_false : rs v68 4 false = v69 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v68_lb : LB v68 10 := rule1 v68 4 false 9 1 0 255 (by decide +kernel) (by decide +kernel) (v68_4_false.symm ▸ v69_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_2_false : rs v1 2 false = v68 := by funext x; revert x; decide +kernel

def v88 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7)

def v89 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

def v90 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 3 && x 5) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v90_5_false : rs v90 5 false = v67 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v90_lb : LB v90 7 := rule1 v90 5 false 6 1 0 255 (by decide +kernel) (by decide +kernel) (v90_5_false.symm ▸ v67_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v89_2_false : rs v89 2 false = v90 := by funext x; revert x; decide +kernel

def v91 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 5) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v91_5_false : rs v91 5 false = v67 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v91_lb : LB v91 7 := rule1 v91 5 false 6 0 0 255 (by decide +kernel) (by decide +kernel) (v91_5_false.symm ▸ v67_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v89_2_true : rs v89 2 true = v91 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v89_lb : LB v89 9 := rule2 v89 2 7 32 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v89_2_false.symm ▸ v90_lb) (v89_2_true.symm ▸ v91_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v88_1_false : rs v88 1 false = v89 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v88_lb : LB v88 10 := rule1 v88 1 false 9 16 0 255 (by decide +kernel) (by decide +kernel) (v88_1_false.symm ▸ v89_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_6_false : rs v1 6 false = v88 := by funext x; revert x; decide +kernel

def v92 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v92_2_false : rs v92 2 false = v69 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v92_lb : LB v92 10 := rule1 v92 2 false 9 32 0 255 (by decide +kernel) (by decide +kernel) (v92_2_false.symm ▸ v69_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_4_false : rs v1 4 false = v92 := by funext x; revert x; decide +kernel

def v93 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 3 && x 4) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v94 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

def v95 : BF 8 := fun x => (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v95_4_false : rs v95 4 false = v63 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v95_lb : LB v95 7 := rule1 v95 4 false 6 1 0 255 (by decide +kernel) (by decide +kernel) (v95_4_false.symm ▸ v63_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v94_2_false : rs v94 2 false = v95 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v94_2_true : rs v94 2 true = v66 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v94_lb : LB v94 9 := rule2 v94 2 7 64 0 255 0 255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (v94_2_false.symm ▸ v95_lb) (v94_2_true.symm ▸ v66_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v93_1_false : rs v93 1 false = v94 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v93_lb : LB v93 10 := rule1 v93 1 false 9 16 0 255 (by decide +kernel) (by decide +kernel) (v93_1_false.symm ▸ v94_lb)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_5_false : rs v1 5 false = v93 := by funext x; revert x; decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma v1_lb : LB v1 12 := rule3B v1 12 (fun i : Fin 8 => ((255 : ℕ).testBit i.val)) (by decide +kernel)
    ⟨0, 1, by decide +kernel⟩ [(0, false, 10), (3, false, 10), (1, false, 10), (2, false, 10), (6, false, 10), (4, false, 10), (5, false, 10)] (by
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (v1_0_false.symm ▸ v2_lb)
    · exact (v1_3_false.symm ▸ v36_lb)
    · exact (v1_1_false.symm ▸ v60_lb)
    · exact (v1_2_false.symm ▸ v68_lb)
    · exact (v1_6_false.symm ▸ v88_lb)
    · exact (v1_4_false.symm ▸ v92_lb)
    · exact (v1_5_false.symm ▸ v93_lb)) (by decide +kernel)

def onWit : List Gate := [⟨.or, [0, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [10, 13]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [9, 7]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩]

lemma binary_lt (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) : bc gs < gs.length := by
  obtain ⟨g, mem, op⟩ := h
  exact (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
    ⟨g, mem, by simp [isBinary, op]⟩

lemma onWitBasis : ∀ g ∈ onWit, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [onWit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma onWitCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨onWit, 20⟩ (List.ofFn x) = v1 x := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma graph_eq : ∀ x : Fin 8 → Bool, v1 x = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel

end PEqualNP.Outside.L_meta_34282

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_34282

theorem PEqualNP.Outside.L_meta_34282 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 3, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o hfit _hone hev
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have hb := bound_of_LB v1 12 v1_lb gates o (fun g hg => hfit g hg)
      (fun x => (hev x).trans (graph_eq x).symm)
    have hl := binary_lt gates hn
    have hw : onWit.length = 13 := rfl
    exact ⟨onWit, 20, onWitBasis, by omega, fun x => (onWitCorrect x).trans (graph_eq x)⟩
  · refine ⟨gates, o, ?_, le_rfl, hev⟩
    intro g hg
    obtain ⟨ho, hl⟩ := hfit g hg
    refine ⟨?_, hl⟩
    rcases ho with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
