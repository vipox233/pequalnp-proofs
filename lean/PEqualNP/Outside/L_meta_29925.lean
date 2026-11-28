import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29925.Binary

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

theorem K_not {S : (ι → Bool) → Prop} {w : ι → Bool} (h : K S w) : K S (fun x => !w x) := by
  rcases h with ⟨c, rfl⟩ | h | h
  · exact Or.inl ⟨!c, rfl⟩
  · exact Or.inr (Or.inr (by simpa using h))
  · exact Or.inr (Or.inl h)

theorem K_ins {S : (ι → Bool) → Prop} {z w : ι → Bool} (h : K S w) : K (ins z S) w := by
  rcases h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Or.inr h))
  · exact Or.inr (Or.inr (Or.inr h))

theorem K_new {S : (ι → Bool) → Prop} (z : ι → Bool) : K (ins z S) z := Or.inr (Or.inl (Or.inl rfl))

theorem K_and {S : (ι → Bool) → Prop} {a b : ι → Bool} (ha : ∃ c, ∀ y, a y = c) (hb : K S b) :
    K S (fun y => a y && b y) := by
  obtain ⟨c, hc⟩ := ha
  cases c
  · exact Or.inl ⟨false, funext fun y => by simp [hc y]⟩
  · have : (fun y => a y && b y) = b := funext fun y => by simp [hc y]
    rw [this]; exact hb

theorem K_bind {S : (ι → Bool) → Prop} {S' : (κ → Bool) → Prop} (σ : κ → ι)
    (h : ∀ w, S w → K S' (fun y => w (σ y))) {w : ι → Bool} (hw : K S w) :
    K S' (fun y => w (σ y)) := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact Or.inl ⟨c, rfl⟩
  · exact h w hw
  · have h2 := K_not (h _ hw)
    simpa using h2

theorem Run_map (σ : κ → ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
    (f : ι → Bool), (∀ w, S w → K S' (fun y => w (σ y))) → Run t S f → Run t S' (fun y => f (σ y))
  | 0, _, _, _, h, hf => K_bind σ h hf
  | t + 1, S, S', f, h, hf => by
    rcases hf with hf | ⟨a, b, ha, hb, hf⟩
    · exact Or.inl (Run_map σ t S S' f h hf)
    · refine Or.inr ⟨_, _, K_bind σ h ha, K_bind σ h hb, Run_map σ t _ _ f ?_ hf⟩
      rintro w (rfl | hw)
      · exact K_new _
      · exact K_ins (h w hw)

theorem Run_le {t t' : ℕ} {S : (ι → Bool) → Prop} {f : ι → Bool} (h : t ≤ t') (hf : Run t S f) :
    Run t' S f := by
  induction h with
  | refl => exact hf
  | step _ ih => exact Or.inl ih

def Cl (σ : κ → ι) (p q r : ι) (S : (ι → Bool) → Prop) : Prop :=
  ∀ w, S w → w p ≠ w q → ∀ y, w (σ y) = w r

theorem Cl_K {σ : κ → ι} {p q r : ι} {S : (ι → Bool) → Prop} (h : Cl σ p q r S) {w : ι → Bool}
    (hw : K S w) (hd : w p ≠ w q) (y : κ) : w (σ y) = w r := by
  rcases hw with ⟨c, rfl⟩ | hw | hw
  · exact absurd rfl hd
  · exact h w hw hd y
  · have h2 := h _ hw (by simpa using hd) y
    simpa using h2

theorem and_dep {a b : ι → Bool} {p q : ι} (h : (a p && b p) ≠ (a q && b q)) :
    a p ≠ a q ∨ b p ≠ b q := by
  by_contra hc
  simp only [not_or, not_not] at hc
  exact h (by rw [hc.1, hc.2])

theorem kill1 (σ : κ → ι) (p q r : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop) (S' : (κ → Bool) → Prop)
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

theorem kill2_dep (σ0 σ1 : κ → ι) (p q : ι) {t : ℕ} {S : (ι → Bool) → Prop}
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

theorem kill2 (σ0 σ1 : κ → ι) (p q : ι) : ∀ (t : ℕ) (S : (ι → Bool) → Prop)
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

end Rules

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def ops (a b : ℕ) : List ℕ := [a &&& b, a ||| b, a ^^^ (a &&& b), b ^^^ (a &&& b)]

abbrev bops (a b : ℕ) : Finset ℕ := (ops a b).toFinset

def sep (P m x : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight x P) x) m

def cuts (P m : ℕ) (ws : List ℕ) : ℕ := ws.foldr (fun w v => Nat.lor (sep P m w) v) 0

def differs (P i w : ℕ) : Prop := w.testBit (P + i) ≠ w.testBit i

theorem ops_differs (P i a b z : ℕ) (hz : z ∈ bops a b) (hd : differs P i z) :
    differs P i a ∨ differs P i b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha, hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, ha, hb]

theorem mask_bit (P i : ℕ) : (2 ^ P - 1).testBit i = decide (i < P) := Nat.testBit_two_pow_sub_one P i

theorem cuts_spec (P : ℕ) (ws : List ℕ) (i : ℕ) :
    (cuts P (2 ^ P - 1) ws).testBit i = true ↔ i < P ∧ ∃ w ∈ ws, differs P i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change ((((a >>> P) ^^^ a) &&& (2 ^ P - 1)) ||| cuts P (2 ^ P - 1) rest).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp only [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, mask_bit,
      Bool.and_eq_true, bx, decide_eq_true_eq, differs, List.mem_cons, exists_eq_or_imp]
    tauto

theorem cuts_full {P g : ℕ} (hg : ∀ i, i < P → differs P i g) {k : ℕ} {ws : List ℕ}
    (h : live bops g k ws.toFinset) : cuts P (2 ^ P - 1) ws = 2 ^ P - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [mask_bit]
  by_cases hi : i < P
  · have hw := live_separates (differs P i) (hg i hi) (ops_differs P i) h
    simpa [hi] using (cuts_spec P ws i).mpr ⟨hi, by simpa using hw⟩
  · cases hb : (cuts P (2 ^ P - 1) ws).testBit i
    · simp [hi]
    · exact absurd ((cuts_spec P ws i).mp hb).1 hi

theorem ops_swap (a b : ℕ) : bops a b = bops b a := by
  ext z
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [Nat.and_comm a b, Nat.or_comm a b]
  tauto

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : ℕ} {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) :
    ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def fz {β : Type} (n : ℕ) (f : ℕ → β) : β := Nat.casesOn n (f 0) (fun k => f (Nat.succ k))

theorem fz_eq {β : Type} (n : ℕ) (f : ℕ → β) : fz n f = f n := by cases n <;> rfl

def fzl {β : Type} : List ℕ → (List ℕ → β) → β
  | [], f => f []
  | a :: t, f => fz a fun a' => fzl t fun t' => f (a' :: t')

theorem fzl_eq {β : Type} : ∀ (l : List ℕ) (f : List ℕ → β), fzl l f = f l
  | [], f => rfl
  | a :: t, f => by simp [fzl, fz_eq, fzl_eq t]

def gz (nx : List ℕ → Bool) (z : ℕ) (l : List ℕ) : Bool := fz z fun z => nx (z :: l)

def oA (a b : ℕ) : ℕ := Nat.land a b
def oO (a b : ℕ) : ℕ := Nat.lor a b
def oX (a b : ℕ) : ℕ := Nat.xor a (Nat.land a b)
def oY (a b : ℕ) : ℕ := Nat.xor b (Nat.land a b)
def kr (_ _ : ℕ) (r : List ℕ) : List ℕ := r
def ka (a _ : ℕ) (r : List ℕ) : List ℕ := a :: r
def kb (_ b : ℕ) (r : List ℕ) : List ℕ := b :: r
def kab (a b : ℕ) (r : List ℕ) : List ℕ := a :: b :: r

abbrev KF := ℕ → ℕ → List ℕ → List ℕ
abbrev Sc := ℕ → (List ℕ → Bool) → (ℕ → ℕ → ℕ) → KF → Bool

def lane (W G : ℕ) : ℕ :=
  (cond (Nat.blt G (Nat.pow W 14)) (cond (Nat.blt G (Nat.pow W 7)) (cond (Nat.blt G (Nat.pow W 3)) (cond (Nat.blt G (Nat.pow W 1)) 0 (cond (Nat.blt G (Nat.pow W 2)) 1 2)) (cond (Nat.blt G (Nat.pow W 5)) (cond (Nat.blt G (Nat.pow W 4)) 3 4) (cond (Nat.blt G (Nat.pow W 6)) 5 6))) (cond (Nat.blt G (Nat.pow W 10)) (cond (Nat.blt G (Nat.pow W 8)) 7 (cond (Nat.blt G (Nat.pow W 9)) 8 9)) (cond (Nat.blt G (Nat.pow W 12)) (cond (Nat.blt G (Nat.pow W 11)) 10 11) (cond (Nat.blt G (Nat.pow W 13)) 12 13)))) (cond (Nat.blt G (Nat.pow W 21)) (cond (Nat.blt G (Nat.pow W 17)) (cond (Nat.blt G (Nat.pow W 15)) 14 (cond (Nat.blt G (Nat.pow W 16)) 15 16)) (cond (Nat.blt G (Nat.pow W 19)) (cond (Nat.blt G (Nat.pow W 18)) 17 18) (cond (Nat.blt G (Nat.pow W 20)) 19 20))) (cond (Nat.blt G (Nat.pow W 24)) (cond (Nat.blt G (Nat.pow W 22)) 21 (cond (Nat.blt G (Nat.pow W 23)) 22 23)) (cond (Nat.blt G (Nat.pow W 26)) (cond (Nat.blt G (Nat.pow W 25)) 24 25) (cond (Nat.blt G (Nat.pow W 27)) 26 27)))))

def sel (L P W : ℕ) (ch : ℕ → Bool) (fuel : ℕ) : ℕ → Bool :=
  Nat.rec (fun _ => true) (fun _ ih G => Nat.casesOn G false (fun k =>
    fz (lane W (Nat.succ k)) fun p => or (ch p)
      (ih (Nat.xor (Nat.succ k) (Nat.pow 2 (Nat.add (Nat.mul L p) P)))))) fuel

theorem sel_true {L P W : ℕ} (hPL : P < L) {ch : ℕ → Bool} {p : ℕ} (hc : ch p = true) : ∀ (fuel G : ℕ),
    G.testBit (L * p + P) = true → sel L P W ch fuel G = true
  | 0, _, _ => rfl
  | fuel + 1, 0, hG => by simp at hG
  | fuel + 1, k + 1, hG => by
    change fz (lane W (k + 1)) (fun p => or (ch p) (sel L P W ch fuel ((k + 1) ^^^ 2 ^ (L * p + P)))) = true
    rw [fz_eq]
    generalize lane W (k + 1) = u
    by_cases h : u = p
    · rw [h, hc]; rfl
    · rw [sel_true hPL hc fuel _ (by
        have h3 : ¬ (L * u + P = L * p + P) := fun e => h (Nat.eq_of_mul_eq_mul_left (by omega) (by omega : L * u = L * p))
        rw [Nat.testBit_xor, hG, Nat.testBit_two_pow, decide_eq_false h3]
        rfl)]
      simp
def chg (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (prs : List (ℕ × ℕ × List ℕ)) (p : ℕ) : Bool :=
  match prs[p]? with
  | none => false
  | some q => gz nx (o q.1 q.2.1) (kf q.1 q.2.1 q.2.2)

def sg (L P W : ℕ) (prs : List (ℕ × ℕ × List ℕ)) (G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ)
    (kf : KF) : Bool := sel L P W (chg nx o kf prs) 29 G

theorem sg_true {P L W G : ℕ} (hPL : P < L) {nx : List ℕ → Bool} {o : ℕ → ℕ → ℕ} {kf : KF}
    {q : ℕ × ℕ × List ℕ} (hn : nx (o q.1 q.2.1 :: kf q.1 q.2.1 q.2.2) = true)
    (prs : List (ℕ × ℕ × List ℕ)) (p : ℕ) (hq : prs[p]? = some q)
    (hG : G.testBit (L * p + P) = true) : sg L P W prs G nx o kf = true := by
  refine sel_true hPL (p := p) ?_ 29 G hG
  unfold chg
  rw [hq]
  change gz nx (o q.1 q.2.1) (kf q.1 q.2.1 q.2.2) = true
  unfold gz
  rw [fz_eq]
  exact hn
abbrev Al := (List ℕ → Bool) → (ℕ → ℕ → ℕ) → KF → Bool

def alg (prs : List (ℕ × ℕ × List ℕ)) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  prs.foldr (fun q acc => or (gz nx (o q.1 q.2.1) (kf q.1 q.2.1 q.2.2)) acc) false

theorem alg_true {nx : List ℕ → Bool} {o : ℕ → ℕ → ℕ} {kf : KF} {q : ℕ × ℕ × List ℕ}
    (hn : nx (o q.1 q.2.1 :: kf q.1 q.2.1 q.2.2) = true) : ∀ prs : List (ℕ × ℕ × List ℕ), q ∈ prs →
    alg prs nx o kf = true
  | [], h => by simp at h
  | u :: t, h => by
    change or (gz nx (o u.1 u.2.1) (kf u.1 u.2.1 u.2.2)) (alg t nx o kf) = true
    rcases List.mem_cons.mp h with rfl | h
    · unfold gz
      rw [fz_eq, hn]; rfl
    · rw [alg_true hn t h]; simp

def gt (O G V : ℕ) : ℕ := Nat.land (Nat.add V O) G
def sv (P K Z : ℕ) : ℕ := Nat.land (Nat.xor (Nat.shiftRight Z P) Z) K

def ndE (P K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e A B S : ℕ) (sc : Sc) (al : Al) (o : ℕ → ℕ → ℕ) : Bool :=
  or (sc (gt O G (Nat.lor (sv P K (o A B)) S)) (nx (Nat.succ e)) o kr)
  (or (sc (gt O G (Nat.lor (sv P K A) (Nat.lor (sv P K (o A B)) S))) (nx e) o ka)
  (or (sc (gt O G (Nat.lor (sv P K B) (Nat.lor (sv P K (o A B)) S))) (nx e) o kb)
    (Nat.casesOn e false (fun e' => al (nx e') o kab))))

def nd (P K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e A B S : ℕ) (sc : Sc) (al : Al) : Bool :=
  Nat.casesOn e
    (or (sc (gt O G (Nat.lor (sv P K (oA A B)) S)) (nx 0) oA kr)
    (or (sc (gt O G (Nat.lor (sv P K (oO A B)) S)) (nx 0) oO kr)
    (or (sc (gt O G (Nat.lor (sv P K (oX A B)) S)) (nx 0) oX kr)
      (sc (gt O G (Nat.lor (sv P K (oY A B)) S)) (nx 0) oY kr))))
    (fun e => or (ndE P K O G nx e A B S sc al oA) (or (ndE P K O G nx e A B S sc al oO)
      (or (ndE P K O G nx e A B S sc al oX) (ndE P K O G nx e A B S sc al oY))))

def pkl (W : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: t => Nat.add (Nat.mul W (pkl W t)) x

def nodeg (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e : ℕ) (ws : List ℕ) : Bool :=
  nd P K O G nx e (pkl W ((pairs ws).map fun q => q.1)) (pkl W ((pairs ws).map fun q => q.2.1))
    (pkl W ((pairs ws).map fun q => cuts P m q.2.2)) (sg L P W (pairs ws)) (alg (pairs ws))

def pkf (L : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | N + 1, f => 2 ^ L * pkf L N (fun p => f (p + 1)) + f 0

theorem pkf_bit {L : ℕ} (hL : 0 < L) : ∀ (N : ℕ) (f : ℕ → ℕ), (∀ p, f p < 2 ^ L) → ∀ j,
    (pkf L N f).testBit j = (decide (j / L < N) && (f (j / L)).testBit (j % L))
  | 0, f, _, j => by simp [pkf]
  | N + 1, f, hf, j => by
    rw [pkf, Nat.testBit_two_pow_mul_add _ (hf 0)]
    by_cases h : j < L
    · rw [ite_eq_left h, Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h]; simp
    · rw [ite_eq_right h, pkf_bit hL N _ (fun p => hf (p + 1)) (j - L)]
      have h1 : j / L = (j - L) / L + 1 := Nat.div_eq_sub_div hL (by omega)
      have h2 : (j - L) % L = j % L := (Nat.mod_eq_sub_mod (by omega)).symm
      rw [h1, h2]; simp

theorem pkf_zero (L : ℕ) : ∀ N : ℕ, pkf L N (fun _ => 0) = 0
  | 0 => rfl
  | N + 1 => by simp [pkf, pkf_zero L N]

theorem pkl_eq (L : ℕ) : ∀ (l : List ℕ) (N : ℕ), l.length ≤ N →
    pkl (2 ^ L) l = pkf L N (fun p => l.getD p 0)
  | [], N, _ => by simp [pkl, pkf_zero]
  | x :: t, 0, h => by simp at h
  | x :: t, N + 1, h => by
    have ih := pkl_eq L t N (by simpa using h)
    change 2 ^ L * pkl (2 ^ L) t + x = _
    rw [ih, pkf]
    simp

theorem pkf_add (L : ℕ) : ∀ (N : ℕ) (f : ℕ → ℕ),
    pkf L N f + pkf L N (fun _ => 1) = pkf L N (fun p => f p + 1)
  | 0, _ => rfl
  | N + 1, f => by
    simp only [pkf]
    rw [← pkf_add L N (fun p => f (p + 1))]
    ring

def BitOp (o : ℕ → ℕ → ℕ) : Prop := ∃ fb : Bool → Bool → Bool, fb false false = false ∧
  ∀ a b i, (o a b).testBit i = fb (a.testBit i) (b.testBit i)

theorem bo_A : BitOp oA := ⟨fun p q => p && q, rfl, fun a b i => Nat.testBit_and a b i⟩
theorem bo_O : BitOp oO := ⟨fun p q => p || q, rfl, fun a b i => Nat.testBit_or a b i⟩
theorem bo_X : BitOp oX := ⟨fun p q => Bool.xor p (p && q), rfl, fun a b i => by
  change (a ^^^ (a &&& b)).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_and]⟩
theorem bo_Y : BitOp oY := ⟨fun p q => Bool.xor q (p && q), rfl, fun a b i => by
  change (b ^^^ (a &&& b)).testBit i = _
  rw [Nat.testBit_xor, Nat.testBit_and]⟩
theorem bo_L : BitOp Nat.lor := ⟨fun p q => p || q, rfl, fun a b i => Nat.testBit_or a b i⟩

theorem BitOp.lt {o : ℕ → ℕ → ℕ} (h : BitOp o) {a b n : ℕ} (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    o a b < 2 ^ n := by
  obtain ⟨fb, h0, hf⟩ := h
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hp : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hi
  rw [hf, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp), Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp), h0]

theorem BitOp.pkf {o : ℕ → ℕ → ℕ} (h : BitOp o) {L : ℕ} (hL : 0 < L) (N : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ p, f p < 2 ^ L) (hg : ∀ p, g p < 2 ^ L) :
    o (pkf L N f) (pkf L N g) = pkf L N (fun p => o (f p) (g p)) := by
  have hb := fun p => h.lt (hf p) (hg p)
  obtain ⟨fb, h0, hl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro j
  rw [hl, pkf_bit hL N f hf, pkf_bit hL N g hg, pkf_bit hL N _ hb, hl]
  cases decide (j / L < N) <;> simp [h0]

theorem sep_lt (P x : ℕ) : sep P (2 ^ P - 1) x < 2 ^ P :=
  Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos P) (by norm_num))

theorem cuts_lt (P : ℕ) : ∀ ws : List ℕ, cuts P (2 ^ P - 1) ws < 2 ^ P
  | [] => Nat.two_pow_pos P
  | a :: t => Nat.or_lt_two_pow (sep_lt P a) (cuts_lt P t)

theorem lt_dbl {P x : ℕ} (h : x < 2 ^ P) : x < 2 ^ (P + P) :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem sv_eq {P : ℕ} (hP : 0 < P) (N : ℕ) (f : ℕ → ℕ) (hf : ∀ p, f p < 2 ^ (P + P)) :
    sv P (pkf (P + P) N fun _ => 2 ^ P - 1) (pkf (P + P) N f) =
      pkf (P + P) N (fun p => sep P (2 ^ P - 1) (f p)) := by
  have hL : 0 < P + P := by omega
  have hm : 2 ^ P - 1 < 2 ^ P := Nat.sub_lt (Nat.two_pow_pos P) (by norm_num)
  apply Nat.eq_of_testBit_eq
  intro j
  change (((pkf (P + P) N f) >>> P ^^^ (pkf (P + P) N f)) &&& _).testBit j = _
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, pkf_bit hL N f hf,
    pkf_bit hL N f hf, pkf_bit hL N _ (fun _ => lt_dbl hm), pkf_bit hL N _ (fun p => lt_dbl (sep_lt P (f p)))]
  change _ = (_ && (((f (j / (P + P))) >>> P ^^^ (f (j / (P + P)))) &&& (2 ^ P - 1)).testBit (j % (P + P)))
  rw [Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftRight, mask_bit]
  by_cases h : j % (P + P) < P
  · have e0 : (P + P) * (j / (P + P)) + j % (P + P) = j := Nat.div_add_mod j (P + P)
    have e1 : (P + j) / (P + P) = j / (P + P) ∧ (P + j) % (P + P) = P + j % (P + P) := by
      generalize j / (P + P) = u at e0 ⊢
      generalize j % (P + P) = r at e0 h ⊢
      subst e0
      rw [show P + ((P + P) * u + r) = (P + P) * u + (P + r) by ring]
      exact ⟨by rw [Nat.mul_add_div hL, Nat.div_eq_of_lt (by omega), Nat.add_zero],
        by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]⟩
    rw [e1.1, e1.2]
    cases decide (j / (P + P) < N) <;> simp [h]
  · simp [h]

theorem gt_bit {P : ℕ} (hP : 0 < P) {N : ℕ} (v : ℕ → ℕ) (hv : ∀ p, v p < 2 ^ P) {p : ℕ} (hp : p < N)
    (hvp : v p = 2 ^ P - 1) :
    (gt (pkf (P + P) N fun _ => 1) (pkf (P + P) N fun _ => 2 ^ P) (pkf (P + P) N v)).testBit
      ((P + P) * p + P) = true := by
  have hL : 0 < P + P := by omega
  have hPP : 2 ^ P < 2 ^ (P + P) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have e1 : ((P + P) * p + P) / (P + P) = p := by
    rw [Nat.mul_add_div hL, Nat.div_eq_of_lt (by omega)]; simp
  have e2 : ((P + P) * p + P) % (P + P) = P := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
  change ((pkf (P + P) N v + pkf (P + P) N (fun _ => 1)) &&& _).testBit _ = true
  rw [Nat.testBit_and, pkf_add, pkf_bit hL N (fun q => v q + 1) (fun q => lt_of_le_of_lt (hv q) hPP),
    pkf_bit hL N _ (fun _ => hPP), e1, e2, hvp,
    Nat.sub_add_cancel (Nat.one_le_two_pow), Nat.testBit_two_pow_self]
  simp [hp]

theorem singles_len {α : Type} : ∀ l : List α, (singles l).length = l.length
  | [] => rfl
  | a :: t => by simp [singles, singles_len t]

theorem pairs_len {α : Type} : ∀ l : List α, 2 * (pairs l).length + l.length = l.length * l.length
  | [] => rfl
  | a :: t => by
    have ih := pairs_len t
    simp only [pairs, List.length_append, List.length_map, singles_len, List.length_cons]
    nlinarith

theorem singles_mem {α : Type} : ∀ {l : List α} {q : α × List α}, q ∈ singles l → q.1 ∈ l
  | [], q, h => by simp [singles] at h
  | a :: t, q, h => by
    simp only [singles, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨⟨b, bs⟩, hu, rfl⟩
    · simp
    · exact List.mem_cons_of_mem _ (singles_mem (q := (b, bs)) hu)

theorem pairs_mem {α : Type} : ∀ {l : List α} {q : α × α × List α}, q ∈ pairs l →
    q.1 ∈ l ∧ q.2.1 ∈ l
  | [], q, h => by simp [pairs] at h
  | a :: t, q, h => by
    simp only [pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨b, bs⟩, hu, rfl⟩ | ⟨⟨b, c, bs⟩, hu, rfl⟩
    · exact ⟨by simp, List.mem_cons_of_mem _ (singles_mem (q := (b, bs)) hu)⟩
    · exact ⟨List.mem_cons_of_mem _ (pairs_mem (q := (b, c, bs)) hu).1,
        List.mem_cons_of_mem _ (pairs_mem (q := (b, c, bs)) hu).2⟩

theorem nodeg_complete {P k extra a b z : ℕ} {ws r kept : List ℕ} (hP : 0 < P)
    (next : ℕ → List ℕ → Bool) (hb : ∀ w ∈ ws, w < 2 ^ (P + P)) (hm : (a, b, r) ∈ pairs ws)
    (h8 : ws.length ≤ 8) (hz : z ∈ bops a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts P (2 ^ P - 1) (z :: kept) = 2 ^ P - 1)
    (ht : next (k - kept.length) (z :: kept) = true) :
    nodeg P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
      (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) next extra ws = true := by
  have hL : 0 < P + P := by omega
  have hPL : P < P + P := by omega
  have hlen : (pairs ws).length ≤ 28 := by
    have := pairs_len ws
    have : ws.length * ws.length ≤ 8 * ws.length := Nat.mul_le_mul_right _ h8
    nlinarith
  obtain ⟨p, hpl, hpe⟩ := List.getElem_of_mem hm
  have hq : (pairs ws)[p]? = some (a, b, r) := by rw [List.getElem?_eq_getElem hpl, hpe]
  have hp21 : p < 28 := by omega
  unfold nodeg
  set prs := pairs ws with hprs
  rw [pkl_eq (P + P) (prs.map fun q => q.1) 28 (by simpa using hlen),
    pkl_eq (P + P) (prs.map fun q => q.2.1) 28 (by simpa using hlen),
    pkl_eq (P + P) (prs.map fun q => cuts P (2 ^ P - 1) q.2.2) 28 (by simpa using hlen)]
  set fa : ℕ → ℕ := fun p => (prs.map fun q => q.1).getD p 0 with hfa
  set fb : ℕ → ℕ := fun p => (prs.map fun q => q.2.1).getD p 0 with hfb
  set fs : ℕ → ℕ := fun p => (prs.map fun q => cuts P (2 ^ P - 1) q.2.2).getD p 0 with hfs
  have bnd : ∀ (F : ℕ × ℕ × List ℕ → ℕ) (n : ℕ), (∀ q ∈ prs, F q < 2 ^ n) → ∀ p, (prs.map F).getD p 0 < 2 ^ n := by
    intro F n hF p
    by_cases h : p < prs.length
    · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map]
      exact hF _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ (by simpa using h)]
      exact Nat.two_pow_pos n
  have hA : ∀ p, fa p < 2 ^ (P + P) := bnd _ _ fun q hq => hb _ (pairs_mem hq).1
  have hB : ∀ p, fb p < 2 ^ (P + P) := bnd _ _ fun q hq => hb _ (pairs_mem hq).2
  have hS : ∀ p, fs p < 2 ^ P := bnd _ _ fun q _ => cuts_lt P q.2.2
  have ea : fa p = a := by simp [hfa, List.getD_eq_getElem?_getD, hq]
  have eb : fb p = b := by simp [hfb, List.getD_eq_getElem?_getD, hq]
  have es : fs p = cuts P (2 ^ P - 1) r := by simp [hfs, List.getD_eq_getElem?_getD, hq]
  set K := pkf (P + P) 28 fun _ => 2 ^ P - 1 with hK
  set O := pkf (P + P) 28 fun _ => 1 with hO
  set G := pkf (P + P) 28 fun _ => 2 ^ P with hG
  have hc' : Nat.lor (sep P (2 ^ P - 1) z) (cuts P (2 ^ P - 1) kept) = 2 ^ P - 1 := hc

  have V0 : ∀ o : ℕ → ℕ → ℕ, BitOp o → Nat.lor (sv P K (o (pkf (P + P) 28 fa) (pkf (P + P) 28 fb))) (pkf (P + P) 28 fs) =
      pkf (P + P) 28 (fun p => Nat.lor (sep P (2 ^ P - 1) (o (fa p) (fb p))) (fs p)) := by
    intro o ho
    rw [ho.pkf hL 28 fa fb hA hB, hK, sv_eq hP 28 _ (fun p => ho.lt (hA p) (hB p)),
      bo_L.pkf hL 28 _ _ (fun p => lt_dbl (sep_lt P _)) (fun p => lt_dbl (hS p))]
  have b0 : ∀ (o : ℕ → ℕ → ℕ) (p : ℕ), Nat.lor (sep P (2 ^ P - 1) (o (fa p) (fb p))) (fs p) < 2 ^ P := fun o p =>
    bo_L.lt (sep_lt P _) (hS p)
  have V1 : ∀ o : ℕ → ℕ → ℕ, BitOp o → ∀ h : ℕ → ℕ, (∀ p, h p < 2 ^ (P + P)) →
      Nat.lor (sv P K (pkf (P + P) 28 h)) (Nat.lor (sv P K (o (pkf (P + P) 28 fa) (pkf (P + P) 28 fb))) (pkf (P + P) 28 fs)) =
      pkf (P + P) 28 (fun p => Nat.lor (sep P (2 ^ P - 1) (h p)) (Nat.lor (sep P (2 ^ P - 1) (o (fa p) (fb p))) (fs p))) := by
    intro o ho h hh
    rw [V0 o ho, hK, sv_eq hP 28 h hh,
      bo_L.pkf hL 28 _ _ (fun p => lt_dbl (sep_lt P _)) (fun p => lt_dbl (b0 o p))]
  have hz' : ∃ o, (o = oA ∨ o = oO ∨ o = oX ∨ o = oY) ∧ z = o a b := by
    have h1 := hz
    simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with e | e | e | e
    · exact ⟨oA, by simp, e⟩
    · exact ⟨oO, by simp, e⟩
    · exact ⟨oX, by simp, e⟩
    · exact ⟨oY, by simp, e⟩
  obtain ⟨o, ho4, hzo⟩ := hz'
  have ho : BitOp o := by
    rcases ho4 with rfl | rfl | rfl | rfl
    exacts [bo_A, bo_O, bo_X, bo_Y]
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases extra with _ | e
  · have hk0 : kept = r := by
      rcases hk with rfl | rfl | rfl | rfl
      · rfl
      all_goals (simp only [List.length_cons] at hn; omega)
    subst hk0
    have key : sg (P + P) P (2 ^ (P + P)) prs (gt O G (Nat.lor (sv P K (o (pkf (P + P) 28 fa) (pkf (P + P) 28 fb)))
        (pkf (P + P) 28 fs))) (next 0) o kr = true := by
      refine sg_true hPL (q := (a, b, kept)) ?_ prs p hq ?_
      · change next 0 (o a b :: kept) = true
        rw [← hzo]
        convert ht using 2; omega
      · rw [V0 o ho]
        exact gt_bit hP _ (b0 o) hp21 (by rw [ea, eb, es, ← hzo]; exact hc')
    change or _ (or _ (or _ _)) = true
    rcases ho4 with rfl | rfl | rfl | rfl <;> rw [key] <;> simp
  · have key : ndE P K O G next e (pkf (P + P) 28 fa) (pkf (P + P) 28 fb) (pkf (P + P) 28 fs)
        (sg (P + P) P (2 ^ (P + P)) prs) (alg prs) o = true := by
      unfold ndE
      rcases hk with rfl | rfl | rfl | rfl
      · rw [sg_true hPL (nx := next (Nat.succ e)) (o := o) (kf := kr) (q := (a, b, kept))
          (by
            change next (Nat.succ e) (o a b :: kept) = true
            rw [← hzo]
            convert ht using 2; omega) prs p hq
          (by
            rw [V0 o ho]
            exact gt_bit hP _ (b0 o) hp21 (by rw [ea, eb, es, ← hzo]; exact hc'))]
        simp
      · rw [sg_true hPL (nx := next e) (o := o) (kf := ka) (q := (a, b, r))
          (by
            change next e (o a b :: a :: r) = true
            rw [← hzo]
            convert ht using 2; simp only [List.length_cons]; omega) prs p hq
          (by
            rw [V1 o ho fa hA]
            refine gt_bit hP _ (fun p => bo_L.lt (sep_lt P _) (b0 o p)) hp21 ?_
            rw [ea, eb, es, ← hzo]
            change sep P (2 ^ P - 1) a ||| (sep P (2 ^ P - 1) z ||| cuts P (2 ^ P - 1) r) = _
            have h2 : sep P (2 ^ P - 1) z ||| (sep P (2 ^ P - 1) a ||| cuts P (2 ^ P - 1) r) = 2 ^ P - 1 := hc'
            convert h2 using 1; ac_rfl)]
        simp
      · rw [sg_true hPL (nx := next e) (o := o) (kf := kb) (q := (a, b, r))
          (by
            change next e (o a b :: b :: r) = true
            rw [← hzo]
            convert ht using 2; simp only [List.length_cons]; omega) prs p hq
          (by
            rw [V1 o ho fb hB]
            refine gt_bit hP _ (fun p => bo_L.lt (sep_lt P _) (b0 o p)) hp21 ?_
            rw [ea, eb, es, ← hzo]
            change sep P (2 ^ P - 1) b ||| (sep P (2 ^ P - 1) z ||| cuts P (2 ^ P - 1) r) = _
            have h2 : sep P (2 ^ P - 1) z ||| (sep P (2 ^ P - 1) b ||| cuts P (2 ^ P - 1) r) = 2 ^ P - 1 := hc'
            convert h2 using 1; ac_rfl)]
        simp
      · rcases e with _ | e'
        · simp only [List.length_cons] at hn; omega
        · have h4 : alg prs (next e') o kab = true := by
            refine alg_true (q := (a, b, r)) ?_ prs hm
            change next e' (o a b :: a :: b :: r) = true
            rw [← hzo]
            convert ht using 2; simp only [List.length_cons]; omega
          change or _ (or _ (or _ (alg prs (next e') o kab))) = true
          rw [h4]; simp
    change or _ (or _ (or _ _)) = true
    rcases ho4 with rfl | rfl | rfl | rfl <;> rw [key] <;> simp

def c2 (a b : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 1) (gz nx (o a b) (kf a b []))
    false)

def s2 (L P W a b G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c2 a b nx o kf) 29 G

def a2 (a b : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b []))
    (false)

def u2 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (0)) a)
    (Nat.add (Nat.mul W (0)) b)
    (Nat.add (Nat.mul W (0)) 0)
    (s2 L P W a b) (a2 a b)

def c3 (a b c : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 2) (cond (Nat.blt p 1) (gz nx (o a b) (kf a b [c]))
    (gz nx (o a c) (kf a c [b])))
    (cond (Nat.blt p 3) (gz nx (o b c) (kf b c [a]))
    false))

def s3 (L P W a b c G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c3 a b c nx o kf) 29 G

def a3 (a b c : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b [c]))
    (or (gz nx (o a c) (kf a c [b]))
    (or (gz nx (o b c) (kf b c [a]))
    (false)))

def u3 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) b)) a)) a)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) c)) c)) b)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) (Nat.lor (sep P m a) 0))) (Nat.lor (sep P m b) 0))) (Nat.lor (sep P m c) 0))
    (s3 L P W a b c) (a3 a b c)

def c4 (a b c d : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 3) (cond (Nat.blt p 1) (gz nx (o a b) (kf a b [c, d]))
    (cond (Nat.blt p 2) (gz nx (o a c) (kf a c [b, d]))
    (gz nx (o a d) (kf a d [b, c]))))
    (cond (Nat.blt p 5) (cond (Nat.blt p 4) (gz nx (o b c) (kf b c [a, d]))
    (gz nx (o b d) (kf b d [a, c])))
    (cond (Nat.blt p 6) (gz nx (o c d) (kf c d [a, b]))
    false)))

def s4 (L P W a b c d G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c4 a b c d nx o kf) 29 G

def a4 (a b c d : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b [c, d]))
    (or (gz nx (o a c) (kf a c [b, d]))
    (or (gz nx (o a d) (kf a d [b, c]))
    (or (gz nx (o b c) (kf b c [a, d]))
    (or (gz nx (o b d) (kf b d [a, c]))
    (or (gz nx (o c d) (kf c d [a, b]))
    (false))))))

def u4 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) c)) b)) b)) a)) a)) a)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) d)) d)) c)) d)) c)) b)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) (Nat.lor (sep P m a) (Nat.lor (sep P m b) 0)))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) 0)))) (Nat.lor (sep P m a) (Nat.lor (sep P m d) 0)))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) 0)))) (Nat.lor (sep P m b) (Nat.lor (sep P m d) 0)))) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0)))
    (s4 L P W a b c d) (a4 a b c d)

def c5 (a b c d e : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 5) (cond (Nat.blt p 2) (cond (Nat.blt p 1) (gz nx (o a b) (kf a b [c, d, e]))
    (gz nx (o a c) (kf a c [b, d, e])))
    (cond (Nat.blt p 3) (gz nx (o a d) (kf a d [b, c, e]))
    (cond (Nat.blt p 4) (gz nx (o a e) (kf a e [b, c, d]))
    (gz nx (o b c) (kf b c [a, d, e])))))
    (cond (Nat.blt p 8) (cond (Nat.blt p 6) (gz nx (o b d) (kf b d [a, c, e]))
    (cond (Nat.blt p 7) (gz nx (o b e) (kf b e [a, c, d]))
    (gz nx (o c d) (kf c d [a, b, e]))))
    (cond (Nat.blt p 9) (gz nx (o c e) (kf c e [a, b, d]))
    (cond (Nat.blt p 10) (gz nx (o d e) (kf d e [a, b, c]))
    false))))

def s5 (L P W a b c d e G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c5 a b c d e nx o kf) 29 G

def a5 (a b c d e : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b [c, d, e]))
    (or (gz nx (o a c) (kf a c [b, d, e]))
    (or (gz nx (o a d) (kf a d [b, c, e]))
    (or (gz nx (o a e) (kf a e [b, c, d]))
    (or (gz nx (o b c) (kf b c [a, d, e]))
    (or (gz nx (o b d) (kf b d [a, c, e]))
    (or (gz nx (o b e) (kf b e [a, c, d]))
    (or (gz nx (o c d) (kf c d [a, b, e]))
    (or (gz nx (o c e) (kf c e [a, b, d]))
    (or (gz nx (o d e) (kf d e [a, b, c]))
    (false))))))))))

def u5 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) d)) c)) c)) b)) b)) b)) a)) a)) a)) a)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) e)) e)) d)) e)) d)) c)) e)) d)) c)) b)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) 0))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) 0))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) 0))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0))))) (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0))))) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))))) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))))
    (s5 L P W a b c d e) (a5 a b c d e)

def c6 (a b c d e f : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 8) (cond (Nat.blt p 4) (cond (Nat.blt p 2) (cond (Nat.blt p 1) (gz nx (o a b) (kf a b [c, d, e, f]))
    (gz nx (o a c) (kf a c [b, d, e, f])))
    (cond (Nat.blt p 3) (gz nx (o a d) (kf a d [b, c, e, f]))
    (gz nx (o a e) (kf a e [b, c, d, f]))))
    (cond (Nat.blt p 6) (cond (Nat.blt p 5) (gz nx (o a f) (kf a f [b, c, d, e]))
    (gz nx (o b c) (kf b c [a, d, e, f])))
    (cond (Nat.blt p 7) (gz nx (o b d) (kf b d [a, c, e, f]))
    (gz nx (o b e) (kf b e [a, c, d, f])))))
    (cond (Nat.blt p 12) (cond (Nat.blt p 10) (cond (Nat.blt p 9) (gz nx (o b f) (kf b f [a, c, d, e]))
    (gz nx (o c d) (kf c d [a, b, e, f])))
    (cond (Nat.blt p 11) (gz nx (o c e) (kf c e [a, b, d, f]))
    (gz nx (o c f) (kf c f [a, b, d, e]))))
    (cond (Nat.blt p 14) (cond (Nat.blt p 13) (gz nx (o d e) (kf d e [a, b, c, f]))
    (gz nx (o d f) (kf d f [a, b, c, e])))
    (cond (Nat.blt p 15) (gz nx (o e f) (kf e f [a, b, c, d]))
    false))))

def s6 (L P W a b c d e f G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c6 a b c d e f nx o kf) 29 G

def a6 (a b c d e f : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b [c, d, e, f]))
    (or (gz nx (o a c) (kf a c [b, d, e, f]))
    (or (gz nx (o a d) (kf a d [b, c, e, f]))
    (or (gz nx (o a e) (kf a e [b, c, d, f]))
    (or (gz nx (o a f) (kf a f [b, c, d, e]))
    (or (gz nx (o b c) (kf b c [a, d, e, f]))
    (or (gz nx (o b d) (kf b d [a, c, e, f]))
    (or (gz nx (o b e) (kf b e [a, c, d, f]))
    (or (gz nx (o b f) (kf b f [a, c, d, e]))
    (or (gz nx (o c d) (kf c d [a, b, e, f]))
    (or (gz nx (o c e) (kf c e [a, b, d, f]))
    (or (gz nx (o c f) (kf c f [a, b, d, e]))
    (or (gz nx (o d e) (kf d e [a, b, c, f]))
    (or (gz nx (o d f) (kf d f [a, b, c, e]))
    (or (gz nx (o e f) (kf e f [a, b, c, d]))
    (false)))))))))))))))

def u6 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) e)) d)) d)) c)) c)) c)) b)) b)) b)) b)) a)) a)) a)) a)) a)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) f)) f)) e)) f)) e)) d)) f)) e)) d)) c)) f)) e)) d)) c)) b)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0)))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0)))))
    (s6 L P W a b c d e f) (a6 a b c d e f)

def c7 (a b c d e f u : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) : Bool :=
  (cond (Nat.blt p 11) (cond (Nat.blt p 5) (cond (Nat.blt p 2) (cond (Nat.blt p 1) (gz nx (o a b) (kf a b [c, d, e, f, u]))
    (gz nx (o a c) (kf a c [b, d, e, f, u])))
    (cond (Nat.blt p 3) (gz nx (o a d) (kf a d [b, c, e, f, u]))
    (cond (Nat.blt p 4) (gz nx (o a e) (kf a e [b, c, d, f, u]))
    (gz nx (o a f) (kf a f [b, c, d, e, u])))))
    (cond (Nat.blt p 8) (cond (Nat.blt p 6) (gz nx (o a u) (kf a u [b, c, d, e, f]))
    (cond (Nat.blt p 7) (gz nx (o b c) (kf b c [a, d, e, f, u]))
    (gz nx (o b d) (kf b d [a, c, e, f, u]))))
    (cond (Nat.blt p 9) (gz nx (o b e) (kf b e [a, c, d, f, u]))
    (cond (Nat.blt p 10) (gz nx (o b f) (kf b f [a, c, d, e, u]))
    (gz nx (o b u) (kf b u [a, c, d, e, f]))))))
    (cond (Nat.blt p 16) (cond (Nat.blt p 13) (cond (Nat.blt p 12) (gz nx (o c d) (kf c d [a, b, e, f, u]))
    (gz nx (o c e) (kf c e [a, b, d, f, u])))
    (cond (Nat.blt p 14) (gz nx (o c f) (kf c f [a, b, d, e, u]))
    (cond (Nat.blt p 15) (gz nx (o c u) (kf c u [a, b, d, e, f]))
    (gz nx (o d e) (kf d e [a, b, c, f, u])))))
    (cond (Nat.blt p 19) (cond (Nat.blt p 17) (gz nx (o d f) (kf d f [a, b, c, e, u]))
    (cond (Nat.blt p 18) (gz nx (o d u) (kf d u [a, b, c, e, f]))
    (gz nx (o e f) (kf e f [a, b, c, d, u]))))
    (cond (Nat.blt p 20) (gz nx (o e u) (kf e u [a, b, c, d, f]))
    (cond (Nat.blt p 21) (gz nx (o f u) (kf f u [a, b, c, d, e]))
    false)))))

def s7 (L P W a b c d e f u G : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  sel L P W (c7 a b c d e f u nx o kf) 29 G

def a7 (a b c d e f u : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) : Bool :=
  or (gz nx (o a b) (kf a b [c, d, e, f, u]))
    (or (gz nx (o a c) (kf a c [b, d, e, f, u]))
    (or (gz nx (o a d) (kf a d [b, c, e, f, u]))
    (or (gz nx (o a e) (kf a e [b, c, d, f, u]))
    (or (gz nx (o a f) (kf a f [b, c, d, e, u]))
    (or (gz nx (o a u) (kf a u [b, c, d, e, f]))
    (or (gz nx (o b c) (kf b c [a, d, e, f, u]))
    (or (gz nx (o b d) (kf b d [a, c, e, f, u]))
    (or (gz nx (o b e) (kf b e [a, c, d, f, u]))
    (or (gz nx (o b f) (kf b f [a, c, d, e, u]))
    (or (gz nx (o b u) (kf b u [a, c, d, e, f]))
    (or (gz nx (o c d) (kf c d [a, b, e, f, u]))
    (or (gz nx (o c e) (kf c e [a, b, d, f, u]))
    (or (gz nx (o c f) (kf c f [a, b, d, e, u]))
    (or (gz nx (o c u) (kf c u [a, b, d, e, f]))
    (or (gz nx (o d e) (kf d e [a, b, c, f, u]))
    (or (gz nx (o d f) (kf d f [a, b, c, e, u]))
    (or (gz nx (o d u) (kf d u [a, b, c, e, f]))
    (or (gz nx (o e f) (kf e f [a, b, c, d, u]))
    (or (gz nx (o e u) (kf e u [a, b, c, d, f]))
    (or (gz nx (o f u) (kf f u [a, b, c, d, e]))
    (false)))))))))))))))))))))

def u7 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f u : ℕ) : Bool :=
  nd P K O G nx e0 (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) f)) e)) e)) d)) d)) d)) c)) c)) c)) c)) b)) b)) b)) b)) b)) a)) a)) a)) a)) a)) a)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) u)) u)) f)) u)) f)) e)) u)) f)) e)) d)) u)) f)) e)) d)) c)) u)) f)) e)) d)) c)) b)
    (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (Nat.add (Nat.mul W (0)) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m b) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m a) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) 0))))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m b) (Nat.lor (sep P m c) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m b) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))) (Nat.lor (sep P m c) (Nat.lor (sep P m d) (Nat.lor (sep P m e) (Nat.lor (sep P m f) (Nat.lor (sep P m u) 0))))))
    (s7 L P W a b c d e f u) (a7 a b c d e f u)

def d7 (P m L W K O G _g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f u : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u7 P m L W K O G nx e0 a b c d e f u) (fun j t => List.casesOn t (nodeg P m L W K O G nx e0 [a,b,c,d,e,f,u,j]) (fun _ _ => true))

def d6 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u6 P m L W K O G nx e0 a b c d e f) (fun y t => d7 P m L W K O G g nx e0 a b c d e f y t)

def d5 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u5 P m L W K O G nx e0 a b c d e) (fun y t => d6 P m L W K O G g nx e0 a b c d e y t)

def d4 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u4 P m L W K O G nx e0 a b c d) (fun y t => d5 P m L W K O G g nx e0 a b c d y t)

def d3 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u3 P m L W K O G nx e0 a b c) (fun y t => d4 P m L W K O G g nx e0 a b c y t)

def d2 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (u2 P m L W K O G nx e0 a b) (fun y t => d3 P m L W K O G g nx e0 a b y t)

def d1 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l (Nat.beq a g) (fun y t => d2 P m L W K O G g nx e0 a y t)

set_option maxRecDepth 100000 in
theorem f2 (a b : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b]) p = c2 a b nx o kf p := by
  by_cases h : p < 1
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 1 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c2
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e2 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) :
    nodeg P m L W K O G nx e0 [a, b] = u2 P m L W K O G nx e0 a b := by
  have hs : sg L P W (pairs [a, b]) = s2 L P W a b := by
    funext G nx o kf
    unfold sg s2
    congr 1
    funext p
    exact f2 a b nx o kf p
  have ha : alg (pairs [a, b]) = a2 a b := rfl
  unfold nodeg u2
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem f3 (a b c : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b, c]) p = c3 a b c nx o kf p := by
  by_cases h : p < 3
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b, c])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b, c]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 3 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c3
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e3 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c : ℕ) :
    nodeg P m L W K O G nx e0 [a, b, c] = u3 P m L W K O G nx e0 a b c := by
  have hs : sg L P W (pairs [a, b, c]) = s3 L P W a b c := by
    funext G nx o kf
    unfold sg s3
    congr 1
    funext p
    exact f3 a b c nx o kf p
  have ha : alg (pairs [a, b, c]) = a3 a b c := rfl
  unfold nodeg u3
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem f4 (a b c d : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b, c, d]) p = c4 a b c d nx o kf p := by
  by_cases h : p < 6
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b, c, d])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b, c, d]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 6 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c4
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e4 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d : ℕ) :
    nodeg P m L W K O G nx e0 [a, b, c, d] = u4 P m L W K O G nx e0 a b c d := by
  have hs : sg L P W (pairs [a, b, c, d]) = s4 L P W a b c d := by
    funext G nx o kf
    unfold sg s4
    congr 1
    funext p
    exact f4 a b c d nx o kf p
  have ha : alg (pairs [a, b, c, d]) = a4 a b c d := rfl
  unfold nodeg u4
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem f5 (a b c d e : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b, c, d, e]) p = c5 a b c d e nx o kf p := by
  by_cases h : p < 10
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b, c, d, e])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b, c, d, e]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 10 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c5
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e5 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e : ℕ) :
    nodeg P m L W K O G nx e0 [a, b, c, d, e] = u5 P m L W K O G nx e0 a b c d e := by
  have hs : sg L P W (pairs [a, b, c, d, e]) = s5 L P W a b c d e := by
    funext G nx o kf
    unfold sg s5
    congr 1
    funext p
    exact f5 a b c d e nx o kf p
  have ha : alg (pairs [a, b, c, d, e]) = a5 a b c d e := rfl
  unfold nodeg u5
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem f6 (a b c d e f : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b, c, d, e, f]) p = c6 a b c d e f nx o kf p := by
  by_cases h : p < 15
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b, c, d, e, f])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b, c, d, e, f]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 15 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c6
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e6 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f : ℕ) :
    nodeg P m L W K O G nx e0 [a, b, c, d, e, f] = u6 P m L W K O G nx e0 a b c d e f := by
  have hs : sg L P W (pairs [a, b, c, d, e, f]) = s6 L P W a b c d e f := by
    funext G nx o kf
    unfold sg s6
    congr 1
    funext p
    exact f6 a b c d e f nx o kf p
  have ha : alg (pairs [a, b, c, d, e, f]) = a6 a b c d e f := rfl
  unfold nodeg u6
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem f7 (a b c d e f u : ℕ) (nx : List ℕ → Bool) (o : ℕ → ℕ → ℕ) (kf : KF) (p : ℕ) :
    chg nx o kf (pairs [a, b, c, d, e, f, u]) p = c7 a b c d e f u nx o kf p := by
  by_cases h : p < 21
  · interval_cases p <;> rfl
  · have h1 : (pairs [a, b, c, d, e, f, u])[p]? = none := by
      rw [List.getElem?_eq_none]
      have := pairs_len [a, b, c, d, e, f, u]
      simp only [List.length_cons, List.length_nil] at this
      omega
    have hb : ∀ m, m ≤ 21 → Nat.blt p m = false := fun m hm => by
      cases hx : Nat.blt p m
      · rfl
      · have := Nat.blt_eq.mp hx; omega
    unfold chg c7
    rw [h1]
    simp [hb]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem e7 (P m L W K O G : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b c d e f u : ℕ) :
    nodeg P m L W K O G nx e0 [a, b, c, d, e, f, u] = u7 P m L W K O G nx e0 a b c d e f u := by
  have hs : sg L P W (pairs [a, b, c, d, e, f, u]) = s7 L P W a b c d e f u := by
    funext G nx o kf
    unfold sg s7
    congr 1
    funext p
    exact f7 a b c d e f u nx o kf p
  have ha : alg (pairs [a, b, c, d, e, f, u]) = a7 a b c d e f u := rfl
  unfold nodeg u7
  rw [hs, ha]
  simp only [pairs, singles, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    pkl, cuts, List.foldr_cons, List.foldr_nil]

set_option maxRecDepth 100000 in
theorem d1_true (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 a b : ℕ) (t : List ℕ)
    (h : (a :: b :: t).length ≤ 8 → nodeg P m L W K O G nx e0 (a :: b :: t) = true) :
    d1 P m L W K O G g nx e0 a (b :: t) = true := by
  rcases t with _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨u, _ | ⟨j, t⟩⟩⟩⟩⟩⟩
  · exact (e2 P m L W K O G nx e0 a b).symm.trans (h (by simp))
  · exact (e3 P m L W K O G nx e0 a b c).symm.trans (h (by simp))
  · exact (e4 P m L W K O G nx e0 a b c d).symm.trans (h (by simp))
  · exact (e5 P m L W K O G nx e0 a b c d e).symm.trans (h (by simp))
  · exact (e6 P m L W K O G nx e0 a b c d e f).symm.trans (h (by simp))
  · exact (e7 P m L W K O G nx e0 a b c d e f u).symm.trans (h (by simp))
  · cases t with
    | nil => exact h (by simp)
    | cons v vs => rfl

def d0 (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) (l : List ℕ) : Bool :=
  List.casesOn l false (fun y t => d1 P m L W K O G g nx e0 y t)

theorem d0_goal (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) :
    d0 P m L W K O G g nx e0 [g] = true := Nat.beq_refl g

theorem d0_true (P m L W K O G g : ℕ) (nx : ℕ → List ℕ → Bool) (e0 : ℕ) (ws : List ℕ)
    (h2 : 2 ≤ ws.length) (h : ws.length ≤ 8 → nodeg P m L W K O G nx e0 ws = true) :
    d0 P m L W K O G g nx e0 ws = true := by
  rcases ws with _ | ⟨a, _ | ⟨b, t⟩⟩
  · simp at h2
  · simp at h2
  · change d1 P m L W K O G g nx e0 a (b :: t) = true
    exact d1_true P m L W K O G g nx e0 a b t h

def optimized (P m L W K O G g k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (fun _ ws => d0 P m L W K O G g (fun _ _ => false) 0 ws)
    (fun _ nx e ws => d0 P m L W K O G g nx e ws) k

def optq (P m L W K O G g q i k : ℕ) (e : ℕ) (ws : List ℕ) : Bool :=
  d0 P m L W K O G g (fun e l => cond (Nat.beq (Nat.mod (l.headD 0) q) i)
    (optimized P m L W K O G g k e l) false) e ws

theorem step_complete {P g : ℕ} (hP : 0 < P) (hg : ∀ i, i < P → differs P i g) (k : ℕ)
    (next : ℕ → List ℕ → Bool) (ws : List ℕ) (extra : ℕ) (hn : ws.Nodup)
    (hb : ∀ w ∈ ws, w < 2 ^ (P + P)) (room : extra + ws.length = k + 1 + 1)
    (a b z : ℕ) (needed : Finset ℕ) (ha : a ∈ ws.toFinset) (hbm : b ∈ ws.toFinset) (hab : a ≠ b)
    (hz : z ∈ bops a b) (hout : z ∉ ws.toFinset) (hs : ws.toFinset = insert a (insert b needed))
    (tail : live bops g k (insert z needed))
    (ih : ∀ (kept : List ℕ), (z :: kept).Nodup → (∀ w ∈ z :: kept, w < 2 ^ (P + P)) →
      live bops g k (z :: kept).toFinset → kept.length ≤ k → next (k - kept.length) (z :: kept) = true) :
    d0 P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
      (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g next extra ws = true := by
  have hzl : z < 2 ^ (P + P) := by
    have h1 := hb a (List.mem_toFinset.mp ha)
    have h2 := hb b (List.mem_toFinset.mp hbm)
    have h3 := hz
    simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with rfl | rfl | rfl | rfl
    exacts [bo_A.lt h1 h2, bo_O.lt h1 h2, bo_X.lt h1 h2, bo_Y.lt h1 h2]
  obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hbm) hab
  have h2 : 2 ≤ ws.length := by
    have := hp.length_eq
    simp only [List.length_cons] at this
    omega
  apply d0_true _ _ _ _ _ _ _ _ _ _ _ h2
  intro h8
  have goz {a b : ℕ} (perm : ws.Perm (a :: b :: r)) (hmem : (a, b, r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ bops a b) :
      nodeg P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
        (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) next extra ws = true := by
    obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hl : live bops g k (z :: kept).toFinset := by
      simpa [hfin] using tail
    have hc := live_card hl
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have len := perm.length_eq
    simp only [List.length_cons] at len
    have hbk : ∀ w ∈ z :: kept, w < 2 ^ (P + P) := by
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hzl
      · have : w ∈ needed := hfin ▸ List.mem_toFinset.mpr hw
        have h5 : w ∈ ws.toFinset := by
          rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem this)
        exact hb w (List.mem_toFinset.mp h5)
    exact nodeg_complete hP next hb hmem h8 hop hk (by omega) (by omega) (cuts_full hg hl)
      (ih kept hnd hbk hl (by omega))
  rcases hm with direct | swap
  · exact goz hp direct hs hz
  · exact goz (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

theorem optimized_complete {P g : ℕ} (hP : 0 < P) (hg : ∀ i, i < P → differs P i g) (n : ℕ) (ws : List ℕ)
    (extra : ℕ) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 2 ^ (P + P))
    (room : extra + ws.length = n + 1) (h : live bops g n ws.toFinset) :
    optimized P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
      (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g n extra ws = true := by
  induction n generalizing ws extra with
  | zero =>
    rw [singleton_list hn h]
    exact d0_goal P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1) (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g (fun _ _ => false) 0
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hbm, hab, z, hz, hout, needed, hs, tail⟩
    · rw [singleton_list hn done]
      exact d0_goal P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1) (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g
        (optimized P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1) (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g k) extra
    · exact step_complete hP hg k _ ws extra hn hb room a b z needed ha hbm hab hz hout hs tail
        (fun kept h1 h2 h3 h4 => ih (z :: kept) (k - kept.length) h1 h2
          (by simp only [List.length_cons]; omega) h3)

theorem optq_complete {P g q : ℕ} (hq : 0 < q) (hP : 0 < P) (hg : ∀ i, i < P → differs P i g) (k : ℕ)
    (ws : List ℕ) (extra : ℕ) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w < 2 ^ (P + P))
    (room : extra + ws.length = k + 1 + 1) (h : live bops g (k + 1) ws.toFinset) :
    ∃ i, i < q ∧ optq P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
      (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g q i k extra ws = true := by
  rcases first_live h with done | ⟨a, ha, b, hbm, hab, z, hz, hout, needed, hs, tail⟩
  · refine ⟨0, hq, ?_⟩
    rw [singleton_list hn done]
    exact d0_goal P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1) (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g _ extra
  · refine ⟨z % q, Nat.mod_lt _ hq, ?_⟩
    refine step_complete hP hg k _ ws extra hn hb room a b z needed ha hbm hab hz hout hs tail ?_
    intro kept h1 h2 h3 h4
    have e : Nat.beq (Nat.mod ((z :: kept).headD 0) q) (z % q) = true := Nat.beq_refl _
    simp only [e]
    exact optimized_complete hP hg k (z :: kept) (k - kept.length) h1 h2
      (by simp only [List.length_cons]; omega) h3

def search (P m L W K O G g q i k : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws => fzl ws fun ws =>
    cond (Nat.ble ws.length (k + 1 + 1)) (cond (Nat.beq (cuts P m ws) m)
      (fz (k + 1 + 1 - ws.length) fun e => optq P m L W K O G g q i k e ws) false) false

theorem search_complete {P g q : ℕ} (hq : 0 < q) (hP : 0 < P) (hg : ∀ i, i < P → differs P i g) (k : ℕ)
    (inputs : List ℕ) (hb : ∀ w ∈ inputs, w < 2 ^ (P + P))
    (hn : inputs.Nodup) (h : build bops g (k + 1) inputs.toFinset) :
    ∃ i, i < q ∧ search P (2 ^ P - 1) (P + P) (2 ^ (P + P)) (pkf (P + P) 28 fun _ => 2 ^ P - 1)
      (pkf (P + P) 28 fun _ => 1) (pkf (P + P) 28 fun _ => 2 ^ P) g q i k inputs = true := by
  classical
  obtain ⟨s, hs, hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live bops g (k + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  obtain ⟨i, hi, ho⟩ := optq_complete hq hP hg k ws (k + 1 + 1 - ws.length) hnd
    (fun w hw => hb w (List.mem_filter.mp hw).1) (by omega) hl'
  refine ⟨i, hi, List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr (List.filter_sublist ..), ?_⟩⟩
  have h1 : Nat.ble ws.length (k + 1 + 1) = true := Nat.ble_eq.mpr sz
  have h2 : Nat.beq (cuts P (2 ^ P - 1) ws) (2 ^ P - 1) = true := by
    rw [cuts_full hg hl']; exact Nat.beq_refl _
  rw [fzl_eq, h1, h2, fz_eq]
  exact ho
def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

theorem enc_congr {ρ : Type} {w w' : ρ → Bool} (h : ∀ x, w x = w' x) (l : List ρ) :
    enc w l = enc w' l := by
  have : w = w' := funext h
  rw [this]

theorem enc_false {ρ : Type} (l : List ρ) : enc (fun _ : ρ => false) l = 0 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [enc, ih]

theorem enc_op {ρ : Type} (o : Bool → Bool → Bool) (o' : ℕ → ℕ → ℕ) (h0 : o false false = false)
    (ho : ∀ a b i, (o' a b).testBit i = o (a.testBit i) (b.testBit i)) (a b : ρ → Bool)
    (l : List ρ) : enc (fun r => o (a r) (b r)) l = o' (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [ho, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega), h0]

section Code
variable {ρ : Type} (x0 : ρ) (pts : List ρ)

def code (w : ρ → Bool) : ℕ := enc (fun x => Bool.xor (w x) (w x0)) pts

theorem code_const (c : Bool) : code x0 pts (fun _ => c) = 0 := by
  unfold code
  rw [← enc_false pts]
  exact enc_congr (fun x => by simp) pts

theorem code_not (w : ρ → Bool) : code x0 pts (fun x => !w x) = code x0 pts w :=
  enc_congr (fun x => by
    show Bool.xor (!w x) (!w x0) = Bool.xor (w x) (w x0)
    cases w x <;> cases w x0 <;> rfl) pts

theorem code_and (a b : ρ → Bool) :
    code x0 pts (fun x => a x && b x) ∈ bops (code x0 pts a) (code x0 pts b) := by
  have e1 := enc_op (ρ := ρ) (fun p q => p && q) (· &&& ·) rfl (fun a b i => Nat.testBit_and a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e2 := enc_op (ρ := ρ) (fun p q => p || q) (· ||| ·) rfl (fun a b i => Nat.testBit_or a b i)
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e3 := enc_op (ρ := ρ) (fun p q => Bool.xor p (p && q)) (fun a b => a ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  have e4 := enc_op (ρ := ρ) (fun p q => Bool.xor q (p && q)) (fun a b => b ^^^ (a &&& b)) rfl
    (fun a b i => by simp [Nat.testBit_and, Nat.testBit_xor])
    (fun x => Bool.xor (a x) (a x0)) (fun x => Bool.xor (b x) (b x0)) pts
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  unfold code
  cases ha : a x0 <;> cases hb : b x0
  · left
    rw [ha, hb] at e1
    rw [← e1]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; left
    rw [ha, hb] at e3
    rw [← e3]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; right; right
    rw [ha, hb] at e4
    rw [← e4]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts
  · right; left
    rw [ha, hb] at e2
    rw [← e2]
    exact enc_congr (fun x => by simp only [ha, hb]; cases a x <;> cases b x <;> rfl) pts

theorem bops_zero {b z : ℕ} (hz : z ∈ bops 0 b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem bops_self {b z : ℕ} (hz : z ∈ bops b b) : z = 0 ∨ z = b := by
  simp only [bops, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp

theorem sim (f : ρ → Bool) (hf : code x0 pts f ≠ 0) : ∀ (t : ℕ) (S : (ρ → Bool) → Prop)
    (A : Finset ℕ), (∀ w, S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A) → Run t S f →
    build bops (code x0 pts f) t A
  | 0, S, A, h, hr => by
    rcases hr with ⟨c, rfl⟩ | hr | hr
    · exact absurd (code_const x0 pts c) hf
    · exact (h f hr).resolve_left hf
    · have := h _ hr
      rw [code_not] at this
      exact this.resolve_left hf
  | t + 1, S, A, h, hr => by
    rcases hr with hr | ⟨a, b, ha, hb, hr⟩
    · exact Or.inl (sim f hf t S A h hr)
    · have hK : ∀ w, K S w → code x0 pts w = 0 ∨ code x0 pts w ∈ A := by
        intro w hw
        rcases hw with ⟨c, rfl⟩ | hw | hw
        · exact Or.inl (code_const x0 pts c)
        · exact h w hw
        · have := h _ hw
          rwa [code_not] at this
      have hmem := code_and x0 pts a b
      by_cases hz : code x0 pts (fun x => a x && b x) = 0 ∨ code x0 pts (fun x => a x && b x) ∈ A
      · refine Or.inl (sim f hf t _ A ?_ hr)
        rintro w (rfl | hw)
        · exact hz
        · exact h w hw
      · have ha' := hK a ha
        have hb' := hK b hb
        have haA : code x0 pts a ∈ A := by
          rcases ha' with h0 | h1
          · rw [h0] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ hb') hz
          · exact h1
        have hbA : code x0 pts b ∈ A := by
          rcases hb' with h0 | h1
          · rw [h0, ops_swap] at hmem
            rcases bops_zero hmem with e | e
            · exact absurd (Or.inl e) hz
            · exact absurd (e ▸ ha') hz
          · exact h1
        have hne : code x0 pts a ≠ code x0 pts b := by
          intro e
          rw [e] at hmem
          rcases bops_self hmem with e2 | e2
          · exact hz (Or.inl e2)
          · exact hz (Or.inr (e2 ▸ hbA))
        refine Or.inr ⟨_, haA, _, hbA, hne, _, hmem, sim f hf t _ _ ?_ hr⟩
        rintro w (rfl | hw)
        · exact Or.inr (Finset.mem_insert_self _ _)
        · exact (h w hw).imp id (fun h => Finset.mem_insert_of_mem h)

end Code

def ptl (n : ℕ) (l : List ℕ) : List (Fin n → Bool) := l.map (pt n)

def ic (n : ℕ) (zs os : List ℕ) : List ℕ :=
  (List.finRange n).map fun i =>
    code (pt n (zs.headD 0)) (ptl n zs ++ ptl n os) fun x : Fin n → Bool => x i

def top (n : ℕ) (f : BF n) (zs os : List ℕ) (q i k : ℕ) : Bool :=
  fz zs.length fun P => fz (Nat.sub (Nat.pow 2 P) 1) fun m => fz (Nat.add P P) fun L =>
  fz (Nat.pow 2 L) fun W => fz (pkf L 28 fun _ => m) fun K => fz (pkf L 28 fun _ => 1) fun O =>
  fz (pkf L 28 fun _ => Nat.pow 2 P) fun G =>
  fzl (((ic n zs os).filter fun c => !Nat.beq c 0).dedup) fun inp =>
  fz (code (pt n (zs.headD 0)) (ptl n zs ++ ptl n os) f) fun g =>
  search P m L W K O G g q i k inp

theorem base {n : ℕ} (f : BF n) (z1 : ℕ) (zt : List ℕ) (os : List ℕ) (q k : ℕ) (hq : 0 < q)
    (hlen : os.length = (z1 :: zt).length)
    (hz : (z1 :: zt).all (fun c => !f (pt n c)) = true)
    (ho : os.all (fun c => f (pt n c)) = true)
    (h : ∀ i, i < q → top n f (z1 :: zt) os q i k = false) : LB f (k + 2) := by
  intro t ht
  by_contra hlt
  have hr := Run_le (show t ≤ k + 1 by omega) ht
  set zs := z1 :: zt with hzs
  set x0 := pt n (zs.headD 0) with hx0
  set pts := ptl n zs ++ ptl n os with hpts
  set P := zs.length with hP
  have hPpos : 0 < P := by simp [hP, hzs]
  have hz' : ∀ c ∈ zs, f (pt n c) = false := by
    intro c hc
    have := List.all_eq_true.mp hz c hc
    simpa using this
  have ho' : ∀ c ∈ os, f (pt n c) = true := fun c hc => List.all_eq_true.mp ho c hc
  have hfx0 : f x0 = false := hz' z1 (by simp [hzs])
  have hbit : ∀ i, i < P → (code x0 pts f).testBit i = false ∧
      (code x0 pts f).testBit (P + i) = true := by
    intro i hi
    have hl1 : i < zs.length := hi
    have hl2 : i < os.length := by omega
    unfold code
    rw [enc_testBit, enc_testBit, hpts, List.map_append]
    constructor
    · rw [List.getD_append _ _ _ _ (by simpa [ptl] using hl1),
        List.getD_eq_getElem _ _ (by simpa [ptl] using hl1)]
      simp [ptl, hfx0, hz' _ (List.getElem_mem hl1)]
    · rw [List.getD_append_right _ _ _ _ (by simp [ptl, hP])]
      have e2 : P + i - (List.map (fun x => f x ^^ f x0) (ptl n zs)).length = i := by
        simp [ptl, hP]
      rw [e2, List.getD_eq_getElem _ _ (by simpa [ptl] using hl2)]
      simp [ptl, hfx0, ho' _ (List.getElem_mem hl2)]
  have hg : ∀ i, i < P → differs P i (code x0 pts f) := by
    intro i hi
    unfold differs
    rw [(hbit i hi).1, (hbit i hi).2]
    decide
  have hne : code x0 pts f ≠ 0 := by
    intro e
    have := (hbit 0 hPpos).2
    rw [e] at this
    simp at this
  have hb := sim x0 pts f hne (k + 1) (Vars n)
    (((ic n zs os).filter fun c => !Nat.beq c 0).dedup).toFinset (by
      rintro w ⟨i, rfl⟩
      by_cases h0 : code x0 pts (fun x => x i) = 0
      · exact Or.inl h0
      · right
        rw [List.mem_toFinset, List.mem_dedup, List.mem_filter]
        refine ⟨List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩, ?_⟩
        have : Nat.beq (code x0 pts fun x => x i) 0 = false := by
          cases hb : Nat.beq (code x0 pts fun x => x i) 0
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hb) h0
        rw [this]; rfl) hr
  obtain ⟨i, hi, hs⟩ := search_complete hq hPpos hg k _ (by
    intro w hw
    rw [List.mem_dedup, List.mem_filter] at hw
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hw.1
    have := enc_lt (fun x => Bool.xor (x j) (x0 j)) pts
    have hl : pts.length = P + P := by simp [hpts, ptl, hlen, hP]
    rw [hl] at this
    exact this) (List.nodup_dedup _) hb
  have h1 := h i hi
  simp only [top, fz_eq, fzl_eq] at h1
  exact Bool.noConfusion (h1.symm.trans hs)
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

theorem rd_K {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (i : ℕ) :
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

theorem gate_run {S : BF n → Prop} {ws : List (BF n)} (hw : ∀ w ∈ ws, K S w) (g : Gate)
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

theorem compile (out : ℕ) : ∀ (gs : List Gate) (ws : List (BF n)) (S : BF n → Prop),
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

theorem bound_of_LB (F : BF n) (b : ℕ) (h : LB F b) (gs : List Gate) (o : ℕ)
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

def cyc7 : BF 7 := fun x => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def zeros : List ℕ := [0, 1, 1, 2, 2, 4, 4, 5, 5, 5, 5, 5, 5, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 64, 64, 66, 66, 66, 68, 68, 68, 68, 72, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 80, 80, 80, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84]
def ones : List ℕ := [3, 3, 65, 3, 6, 6, 12, 7, 13, 15, 69, 71, 77, 12, 24, 11, 13, 25, 27, 73, 89, 11, 14, 26, 30, 24, 48, 19, 25, 49, 51, 81, 113, 19, 22, 26, 50, 54, 22, 28, 52, 60, 23, 29, 31, 53, 55, 61, 63, 85, 87, 93, 95, 117, 119, 125, 127, 48, 96, 35, 49, 97, 99, 35, 38, 50, 98, 102, 38, 44, 52, 100, 108, 39, 45, 47, 53, 101, 103, 109, 111, 44, 56, 104, 120, 43, 45, 57, 59, 105, 107, 121, 123, 43, 46, 58, 62, 106, 110, 122, 126, 65, 96, 67, 70, 98, 69, 70, 76, 100, 73, 76, 88, 104, 75, 78, 79, 90, 91, 94, 106, 81, 88, 112, 83, 86, 90, 114, 115, 118, 85, 86, 92, 116, 124]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert0 : top 7 cyc7 zeros ones 17 0 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert1 : top 7 cyc7 zeros ones 17 1 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert2 : top 7 cyc7 zeros ones 17 2 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert3 : top 7 cyc7 zeros ones 17 3 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert4 : top 7 cyc7 zeros ones 17 4 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert5 : top 7 cyc7 zeros ones 17 5 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert6 : top 7 cyc7 zeros ones 17 6 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert7 : top 7 cyc7 zeros ones 17 7 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert8 : top 7 cyc7 zeros ones 17 8 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert9 : top 7 cyc7 zeros ones 17 9 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert10 : top 7 cyc7 zeros ones 17 10 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert11 : top 7 cyc7 zeros ones 17 11 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert12 : top 7 cyc7 zeros ones 17 12 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert13 : top 7 cyc7 zeros ones 17 13 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert14 : top 7 cyc7 zeros ones 17 14 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert15 : top 7 cyc7 zeros ones 17 15 8 = false := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cert16 : top 7 cyc7 zeros ones 17 16 8 = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cycle_binary : LB cyc7 10 := base cyc7 0 [1, 1, 2, 2, 4, 4, 5, 5, 5, 5, 5, 5, 8, 8, 9, 9, 9, 9, 9, 9, 10, 10, 10, 10, 16, 16, 17, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 20, 20, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 21, 32, 32, 33, 33, 33, 33, 34, 34, 34, 34, 34, 36, 36, 36, 36, 36, 37, 37, 37, 37, 37, 37, 37, 37, 40, 40, 40, 40, 41, 41, 41, 41, 41, 41, 41, 41, 42, 42, 42, 42, 42, 42, 42, 42, 64, 64, 66, 66, 66, 68, 68, 68, 68, 72, 72, 72, 72, 74, 74, 74, 74, 74, 74, 74, 80, 80, 80, 82, 82, 82, 82, 82, 82, 84, 84, 84, 84, 84] ones 17 8
    (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by
      intro i hi
      interval_cases i
      · exact cert0
      · exact cert1
      · exact cert2
      · exact cert3
      · exact cert4
      · exact cert5
      · exact cert6
      · exact cert7
      · exact cert8
      · exact cert9
      · exact cert10
      · exact cert11
      · exact cert12
      · exact cert13
      · exact cert14
      · exact cert15
      · exact cert16
)

theorem short {gates : List Gate} (h : ∃ g ∈ gates, g.op = GateOp.not) : bc gates < gates.length := by
  obtain ⟨g, mem, op⟩ := h
  exact (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g, mem, by simp [isBinary, op]⟩

theorem no_not (C : Circuit) (hf : FanInTwo C) (hs : C.size = 10)
    (he : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = cyc7 x) :
    ∀ g ∈ C.gates, g.op ≠ GateOp.not := by
  intro g hg hn
  have h := bound_of_LB cyc7 10 cycle_binary C.gates C.output (by
    intro v hv
    simpa [legal] using hf v hv) he
  have lt := short ⟨g, hg, hn⟩
  change C.gates.length = 10 at hs
  omega

end PEqualNP.Outside.L_meta_29925.Binary

namespace PEqualNP.Outside.L_meta_29925.Check

abbrev B := BitVec 64
abbrev Sig := B × B
def top : B := BitVec.allOnes 64
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def stable (a : Sig) : Bool := a.1.getLsbD 49 == a.1.getLsbD 50
def maskOK (a : Sig) : Bool :=
  a.1.getLsbD 49 && a.1.getLsbD 50 && (a.2 &&& 0xfc00000000000000 == 0)
def permit (d : Bool) (a b : Sig) : Bool :=
  (stable a || (d && maskOK b)) && (stable b || (d && maskOK a))
def bb (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def bin (d : Bool) (a b : Sig) : Sig :=
  if permit d a b then bb d a b else zero
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  have h : permit d a b = permit d b a := Bool.and_comm _ _
  rw [bin,bin,h]
  cases d <;> simp [bb,BitVec.or_comm,BitVec.and_comm]

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

def Live : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {target}
  | k+1, t, S =>
    (∃ u U a, t = u+1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live k u (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live k t (insert (bin d a b) U))

lemma Live.stop : Live 0 0 {target} := ⟨rfl,rfl⟩

lemma Live.unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U) := Or.inl ⟨_,_,_,rfl,rfl,ha,hfresh,tail⟩

lemma Live.binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U)) := Or.inr ⟨_,_,_,_,rfl,ha,hb,hab,hfresh,tail⟩

lemma liveInd {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P k t (insert (neg a) U) tail → P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P k t (insert (bin d a b) U) tail → P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

lemma liveCases {P : ∀ k t S, Live k t S → Prop}
    (stop : P 0 0 {target} Live.stop)
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)), P (k+1) (t+1) (insert a U) (Live.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)), P (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hfresh tail))
    {k t S} (h : Live k t S) : P k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl⟩ := h
    exact stop
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail
    · exact binary ha hb hab hf tail

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h using liveInd with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 64
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  unfold bin at h
  split at h
  swap
  · cases t <;> simp [sep,zero] at h
  by_cases hi : i < 64
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bb,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 64)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 64) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h using liveInd with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 64 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 64)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

open PEqualNP.CircuitLowerBounds
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (allow : Bool) (w : List Sig) (z : Sig) : Prop :=
  (allow = true ∧ ∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma pull_gate {flag : Bool} {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness flag w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ t' ≤ t+flag.toNat ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨flagOn,a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by simp [flagOn],Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,by omega,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma necessary (raw : List Sig) (every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true) {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

def special : List Sig := []
def gateAvailable (v : List Sig) (g : Sig) : Bool :=
  !(v.contains g) && g != zero && g != one

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n = k-t then
    base == top && gateAvailable v g && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && gateAvailable v g && r (g::(h++rest)))

def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  !(special.contains a) &&
    tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let c := coverage (decide (0<t)) v
  v.any (unaryAt k t r v c)

def allowedKeeps (a b : Sig) : List (List Sig) :=
  [[],[a],[b],[a,b]].filter (fun w => w.all fun x => !(special.contains x))

def fastBinary (r : List Sig → Bool) (v : List Sig) (a b : Sig) (ua ub : B) : Bool :=
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => gateAvailable v g && r (g::rest)
  ((ua &&& ~~~b.1) == 0 && (ub &&& ~~~a.1) == 0 &&
    !(special.contains a) && !(special.contains b) && use (bin false a b)) ||
    ((ua &&& b.2) == 0 && (ub &&& a.2) == 0 && use (bin true a b))

def slowBinary (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  let rest := dropped [a,b] v
  let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
  ((!(special.contains a) && !(special.contains b)) &&
    tryGate k t r v rest (v.length-2) mask (bin false a b) [[],[a],[b],[a,b]]) ||
    tryGate k t r v rest (v.length-2) mask (bin true a b) (allowedKeeps a b)

def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t

lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h
      exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h
        exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  let d := decide (0<t)
  let c := coverage d v
  if t == 0 && v.length == k+2 then
    let acts := v.map (fun a => (a, c.2.1 &&& sep false a))
    scanPairs (fun a b => fastBinary r v a.1 b.1 a.2 b.2) acts
  else scanPairs (slowBinary k t r v c) v

def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
    v == [target] || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v == [target]
  | k+1,t,v => stepTest k t v (search k (t-1)) (search k t)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,gateAvailable,ha,hp.1,hp.2,hr] at *
  · have hav : gateAvailable v g = true := by simp [gateAvailable, ha, hp.1, hp.2]
    simp only [tryGate, ite_eq_right tight, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq, hav, and_true]
    exact ⟨h,hh,⟨hl,cov⟩,hr⟩

private lemma canUse {op : Bool} {v : List Sig} {a b : Sig}
    (h : gateAvailable v (bin op a b) = true) : permit op a b = true := by
  by_contra! he
  simp [bin,he,gateAvailable] at h
private lemma unique_needed (c : Cov) (a b : Sig) (op : Bool)
    (use : permit op a b = true)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  rw [bin,if_pos use] at hh
  cases op <;> simp only [sep,bb,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private lemma fast_ok {k r v c a b}
    (hlen : v.length-2=k) (h : slowBinary k 0 r v c a b = true) :
    fastBinary r v a b (c.2.1 &&& sep false a) (c.2.1 &&& sep false b) = true := by
  simp only [slowBinary,tryGate,Nat.sub_zero,hlen,ite_true,decide_false,Bool.or_eq_true,
    Bool.and_eq_true,beq_iff_eq] at h
  simp only [fastBinary, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  rcases h with ⟨⟨ha,hb⟩,⟨hc,hav⟩,hr⟩ | ⟨⟨hc,hav⟩,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b false (canUse hav) hc)
    exact Or.inl ⟨⟨⟨⟨h1,h2⟩,ha⟩,hb⟩,hav,hr⟩
  · obtain ⟨h1,h2⟩ := BitVec.or_eq_zero_iff.mp (unique_needed c a b true (canUse hav) hc)
    exact Or.inr ⟨⟨h1,h2⟩,hav,hr⟩

private lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (ha : a ∉ special) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨by simp [ha], gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩

private lemma slow_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    slowBinary k t r v (coverage (decide (0<t)) v) a b = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have allow : h ∈ allowedKeeps a b := by
    apply List.mem_filter.mpr
    refine ⟨opts,List.all_eq_true.mpr (fun x hx => ?_)⟩
    have hm : x ∈ U := (List.mem_filter.mp hx).2 |> of_decide_eq_true
    rcases List.mem_cons.mp (List.mem_filter.mp hx).1 with rfl | hx
    · simpa using fun ha : x ∈ special => (hra ha).2 hm
    · obtain rfl := List.mem_singleton.mp hx
      simpa using fun hb : x ∈ special => (hrb hb).2 hm
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  unfold slowBinary
  dsimp only
  rw [hlen,hmask]
  cases d with
  | false =>
    have na : a ∉ special := fun ha => Bool.false_ne_true (hra ha).1
    have nb : b ∉ special := fun hb => Bool.false_ne_true (hrb hb).1
    apply Bool.or_eq_true_iff.mpr
    left
    exact Bool.and_eq_true_iff.mpr ⟨by simp [na,nb],
      gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)⟩
  | true =>
    apply Bool.or_eq_true_iff.mpr
    right
    exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn allow hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    {r : List Sig → Bool}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (hra : a ∈ special → d = true ∧ a ∉ U)
    (hrb : b ∈ special → d = true ∧ b ∉ U)
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have h1 := slow_found hv he hle hab fresh hra hrb l ih
  have e' : v.toFinset = insert b (insert a U) := by rwa [Finset.insert_comm b a]
  have hf : bin d b a ∉ insert b (insert a U) := by rwa [bin_comm d b a, Finset.insert_comm b a]
  have ht : Live m t (insert (bin d b a) U) := by rwa [bin_comm d b a]
  have h2 := slow_found hv e' hle hab.symm hf hrb hra ht (by simpa only [bin_comm d b a] using ih)
  unfold binaryMoves
  split
  · rename_i cut
    simp only [Bool.and_eq_true, beq_iff_eq] at cut
    obtain ⟨rfl,hvlen⟩ := cut
    have hlen : v.length - 2 = k := by omega
    let f := fun x => (x, (coverage false v).2.1 &&& sep false x)
    have na : f a ∈ v.map f := List.mem_map_of_mem ah
    have nb : f b ∈ v.map f := List.mem_map_of_mem bh
    exact scanPairs_complete _ na nb (fun e => hab (congrArg Prod.fst e))
      (fast_ok hlen h1) (fast_ok hlen h2)
  · exact scanPairs_complete _ ah bh hab h1 h2

private lemma reduced_step {m t S : Nat} {s : Finset Sig} {v : List Sig} {u b : List Sig → Bool}
    (h : Live m t s) (hb : m ≤ S+1) (hv : v.Nodup) (he : v.toFinset = s)
    (hu : ∀ w, w.Nodup → ∀ l ≤ S, Live l (t-1) w.toFinset → u w = true)
    (hb' : ∀ w, w.Nodup → ∀ l ≤ S, Live l t w.toFinset → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h
  rw [← he, List.toFinset_card_of_nodup hv] at size
  rw [stepTest, if_neg (by omega)]
  induction h using liveCases with
  | stop =>
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [he])
    have eq := List.perm_singleton.mp p
    simp [eq]
  | @unary m t U a ha hf tail =>
    apply Bool.or_eq_true_iff.mpr
    left
    apply Bool.or_eq_true_iff.mpr
    right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp, unary_found hv he (by omega) hf (by simp [special]) tail ?_⟩
    intro w hn hs
    exact hu w hn m (by omega) (hs.symm ▸ tail)
  | @binary m t U a b d ha hc hab hf tail =>
    apply Bool.or_eq_true_iff.mpr
    right
    apply binary_found hv he (by omega) hab hf (by simp [special]) (by simp [special]) tail
    intro w hn hs
    exact hb' w hn m (by omega) (hs.symm ▸ tail)

lemma search_complete {m t : Nat} {S : Finset Sig} (h : Live m t S) (k : Nat) (hk : m ≤ k)
    (v : List Sig) (hv : v.Nodup) (hs : v.toFinset = S) : search k t v = true := by
  induction k generalizing m t S v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    obtain ⟨rfl,rfl⟩ := h
    have p : v.Perm [target] := List.perm_of_nodup_nodup_toFinset_eq hv (by simp) (by simp [hs])
    simp [search, List.perm_singleton.mp p]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hv hs <;>
      exact fun w hn l hl hh => ih hh hl w hn rfl

def raw : List Sig := [(0xfe0c03f80000007f,0x2001c3870e1c387), (0xfc18000000003fff,0x408e1c3870e1c38), (0x360000001fff80,0x8110e1c3870e1c3), (0x6600000fffc000,0x102070e1c3870e1c), (0xc60007ffe00000,0x2041870e1c3870e1), (0x187fc07f0000000,0x40803870e1c3870e), (0x301fff800000000,0x8101c3870e1c3870)]
private lemma bb_laws (a : Sig) :
    bb false a one = a ∧ bb true a zero = a ∧
    bb false a zero = zero ∧ bb true a one = one ∧
    bb false a a = a ∧ bb true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bb,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

def StepOK (w : List Sig) (z : Sig) : Prop :=
  represented w z ∨ ∃ d a b, represented w a ∧ represented w b ∧ permit d a b = true ∧ z = bb d a b
def Steps (w : List Sig) : List Sig → Prop
  | [] => True
  | z::zs => StepOK w z ∧ Steps (w++[z]) zs

private lemma bb_comm (d : Bool) (a b : Sig) : bb d a b=bb d b a := by
  cases d <;> simp [bb,BitVec.and_comm,BitVec.or_comm]
private lemma enough {w : List Sig} {z : Sig} (hu : StepOK w z) :
    represented w z ∨ witness false w z := by
  rcases hu with h | ⟨d,a,b,ha,hb,permitOK,rfl⟩
  · exact Or.inl h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bb_laws a
  obtain ⟨b1,b0,bz,bo,bb₁,bb₂⟩ := bb_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bb_comm]; cases d <;> simp_all
  · rw [bb_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,by simp [bin,permitOK]⟩)

private lemma extract_steps {w zs : List Sig} (h : Steps w zs) (out : target ∈ w ++ zs) :
    ∃ k S, k ≤ zs.length ∧ Live k 0 S ∧ ∀ a ∈ S, a ∈ w := by
  induction zs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop,by simpa using out⟩
  | cons z zs ih =>
    obtain ⟨k,S,hk,hl,hs⟩ := ih h.2 (by simpa using out)
    obtain ⟨j,t,T,hj,ht,hh,sub⟩ := pull_gate hl (enough h.1) hs
    have tz : t=0 := by simpa using ht
    subst t
    exact ⟨j,T,by simp; omega,hh,sub⟩

theorem reject_of_test (test : search 10 0 raw = false)
    (zs : List Sig) (h : Steps raw zs) (hl : zs.length ≤ 10) (ho : target ∈ raw ++ zs) : False := by
  obtain ⟨k,S,hk,live,sub⟩ := extract_steps h ho
  have req := necessary raw (by decide +kernel) live sub
  have bad := search_complete live 10 (by omega) raw (by decide +kernel) req
  simp [test] at bad
end PEqualNP.Outside.L_meta_29925.Check
namespace PEqualNP.Outside.L_meta_29925.Check
namespace Minor
abbrev R := BitVec 2
abbrev Q := BitVec 6
abbrev Ix := Fin 64
abbrev Sample := Ix × Ix × Ix × Ix × Ix × Ix
def Sample.p (i : Sample) : Ix := i.1
def Sample.a (i : Sample) : Ix := i.2.1
def Sample.b (i : Sample) : Ix := i.2.2.1
def Sample.n (i : Sample) : Ix := i.2.2.2.1
def Sample.c (i : Sample) : Ix := i.2.2.2.2.1
def Sample.d (i : Sample) : Ix := i.2.2.2.2.2

def six (a b c d e f : Bool) : Q :=
  BitVec.ofBool f ++ BitVec.ofBool e ++ BitVec.ofBool d ++ BitVec.ofBool c ++
  BitVec.ofBool b ++ BitVec.ofBool a
def obs (i : Sample) (x : Sig) : Q :=
  six (x.1.getLsbD i.p) (x.1.getLsbD i.a) (x.1.getLsbD i.b)
      (x.2.getLsbD i.n) (x.2.getLsbD i.c) (x.2.getLsbD i.d)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma sixA : ∀ a b c d e f a' b' c' d' e' f' : Bool,
    six (a&&a') (b&&b') (c&&c') (d&&d') (e&&e') (f&&f') =
      six a b c d e f &&& six a' b' c' d' e' f' := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma sixO : ∀ a b c d e f a' b' c' d' e' f' : Bool,
    six (a||a') (b||b') (c||c') (d||d') (e||e') (f||f') =
      six a b c d e f ||| six a' b' c' d' e' f' := by decide +kernel

def accept (r : R) (q : Q) : Bool :=
  let masks := if r=0 then 0xff03550155015501 else if r=1 then 0xff0fff0f55055505
    else if r=2 then 0xff335511ff335511 else 0xffffffffffffff7f
  Nat.testBit masks q.toNat

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma closed (a b : R) (x y : Q) (d : Bool)
    (hd : a &&& b = 0) (hx : accept a x = true) (hy : accept b y = true) :
    accept (a ||| b) (if d then x ||| y else x &&& y) = true := by
  revert a b x y d
  decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma closedZero (r : R) : accept r 0 = true := by revert r; decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma reject7 (r : R) : accept r 7 = false := by revert r; decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma obs_bin (i : Sample) (a b : Sig) (d : Bool) :
    obs i (bin d a b) =
      if permit d a b then if d then obs i a ||| obs i b else obs i a &&& obs i b else 0 := by
  simp only [bin]
  split
  · cases d <;> simp only [bb, obs, Bool.false_eq_true, ite_false, ite_true,
      BitVec.getLsbD_or, BitVec.getLsbD_and]
    · exact sixA _ _ _ _ _ _ _ _ _ _ _ _
    · exact sixO _ _ _ _ _ _ _ _ _ _ _ _
  · have bz : ∀ j : Ix, (0 : B).getLsbD j.val = false := by decide +kernel
    simp only [obs,zero,bz]; rfl
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma obs_target (i : Sample) : obs i target = 7 := by
  have bz : ∀ j : Ix, (0 : B).getLsbD j.val = false := by decide +kernel
  simp only [obs,target,top,BitVec.getLsbD_allOnes,bz,Fin.isLt,decide_true]
  rfl

def affine (S : Finset Sig) (f : Sig → R) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x &&& f y = 0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private lemma bound {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using liveInd with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem noLive {k S} (i : Sample) (f : Sig → R) (h : Live k 0 S)
    (tight : k+1 ≤ S.card) (aff : affine S f)
    (cls : ∀ x ∈ S, accept (f x) (obs i x) = true) : False := by
  induction k generalizing S f with
  | zero =>
    obtain ⟨_,rfl⟩ := h
    have hh := cls target (by simp)
    simp only [obs_target,reject7] at hh
    contradiction
  | succ k ih =>
    rcases h with ⟨t,_,_,ht,_⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hg,tail⟩
    · omega
    let g := bin d a b
    have gn : g ∉ U := fun hm => hg (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have sz := (bound tail).2
    rw [Finset.card_insert_of_notMem gn] at sz
    have ca := Finset.card_insert_le a (insert b U)
    have cb := Finset.card_insert_le b U
    have an : a ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hm)] at tight
      omega
    have bn : b ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at tight ca
      omega
    let f' := fun x => if x=g then f a ||| f b else f x
    have memU {x} (hx : x ∈ U) : x ∈ insert a (insert b U) :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
    have am : a ∈ insert a (insert b U) := by simp
    have bm : b ∈ insert a (insert b U) := by simp
    have dis {x} (hx : x ∈ U) : (f a ||| f b) &&& f x = 0 := by
      rw [BitVec.and_or_distrib_right, aff _ am _ (memU hx) (fun h => an (h.symm ▸ hx)),
        aff _ bm _ (memU hx) (fun h => bn (h.symm ▸ hx))]
      rfl
    apply ih f' tail
    · rw [Finset.card_insert_of_notMem gn]; omega
    · intro x hx y hy ne
      rcases Finset.mem_insert.mp hx with rfl | hx <;> rcases Finset.mem_insert.mp hy with rfl | hy
      · contradiction
      · change f' g &&& f' y = 0
        simpa [f',show y≠g from Ne.symm ne] using dis hy
      · rw [BitVec.and_comm]
        change f' g &&& f' x = 0
        simpa [f',show x≠g from ne] using dis hx
      · simpa [f',show x≠g from fun e => gn (e ▸ hx),show y≠g from fun e => gn (e ▸ hy)]
          using aff x (memU hx) y (memU hy) ne
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [f',ite_true,g,obs_bin]
        split
        · exact closed _ _ _ _ d (aff a am b bm hab) (cls a am) (cls b bm)
        · exact closedZero _
      · simpa [f',show x≠g from fun e => gn (e ▸ hx)] using cls x (memU hx)
end Minor
end PEqualNP.Outside.L_meta_29925.Check
namespace PEqualNP.Outside.L_meta_29925.Check.Minor
def tag (q : Q) : R :=
  if accept 0 q then 0 else if accept 1 q then 1 else if accept 2 q then 2 else 3
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem tag_ok (q : Q) (h : q ≠ 7) : accept (tag q) q = true := by
  revert q; decide +kernel
def valid (i : Sample) (seen : R) : List Sig → Bool
  | [] => true
  | x::xs =>
    let q := obs i x
    let r := tag q
    q != 7 && seen &&& r == 0 && valid i (seen ||| r) xs
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem valid_sound {i : Sample} {v : List Sig} {s : R}
    (h : valid i s v = true) :
    (∀ x ∈ v, accept (tag (obs i x)) (obs i x) = true ∧ s &&& tag (obs i x) = 0) ∧
    affine v.toFinset (fun x => tag (obs i x)) := by
  induction v generalizing s with
  | nil => simp [affine]
  | cons x xs ih =>
    obtain ⟨⟨n,t⟩,h⟩ := Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp
    have ht : s &&& tag (obs i x) = 0 := eq_of_beq t
    have hn : obs i x ≠ 7 := by simpa only [bne_iff_ne] using n
    obtain ⟨h1,h2⟩ := ih h
    have her {y} (hy : y ∈ xs) := (h1 y hy).2
    constructor
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨tag_ok _ hn,ht⟩
      · exact ⟨(h1 _ hy).1,(BitVec.or_eq_zero_iff.mp (BitVec.and_or_distrib_right ▸ her hy)).1⟩
    · intro a ha b hb ne
      simp only [List.mem_toFinset,List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · contradiction
      · exact (BitVec.or_eq_zero_iff.mp (BitVec.and_or_distrib_right ▸ her hb)).2
      · rw [BitVec.and_comm]
        exact (BitVec.or_eq_zero_iff.mp (BitVec.and_or_distrib_right ▸ her ha)).2
      · exact h2 a (List.mem_toFinset.mpr ha) b (List.mem_toFinset.mpr hb) ne

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem noLive_of_valid {v : List Sig} {i : Sample} {k : Nat} (hv : v.Nodup)
    (h : valid i 0 v = true) (tight : k+1 ≤ v.length) : ¬Live k 0 v.toFinset := by
  intro l
  obtain ⟨cl,af⟩ := valid_sound h
  apply noLive i _ l _ af
  · exact fun x hx => (cl x (List.mem_toFinset.mp hx)).1
  · rwa [List.toFinset_card_of_nodup hv]
end PEqualNP.Outside.L_meta_29925.Check.Minor
namespace PEqualNP.Outside.L_meta_29925.Check
namespace Cut
def fetch (bits data i : Nat) : Nat := (data >>> (bits*i)) &&& (2^bits - 1)
def press (n : Nat) (f : Nat → α) : α := Nat.casesOn n (f 0) (fun j => f j.succ)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem eq_press {α : Type} (n : Nat) (f : Nat → α) : press n f = f n := by cases n <;> rfl
def strictV : List Sig → (List Sig → Bool) → Bool
  | [], f => f []
  | s::w, f => press s.1.toNat fun a => press s.2.toNat fun b =>
    strictV w fun l => f ((BitVec.ofNat 64 a, BitVec.ofNat 64 b)::l)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem strictV_eq (v : List Sig) (f : List Sig → Bool) : strictV v f = f v := by
  induction v generalizing f with
  | nil => rfl
  | cons a v ih => simp [strictV,eq_press,ih]
def recon (dict : Nat) : Nat → Nat → List Sig
  | 0, _ => []
  | n+1, w => if w = 0 then [] else
    let j := w &&& 1023
    press (fetch 128 dict (j-1)) fun sn =>
      (BitVec.ofNat 64 sn, BitVec.ofNat 64 (sn >>> 64)) :: recon dict n (w >>> 10)
abbrev Rows := Nat × Nat
def Rows.data (t : Rows) := t.1
def Rows.num (t : Rows) := t.2
def Rows.get (t : Rows) (dict i : Nat) : List Sig :=
  press (fetch 90 t.data i) fun z => recon dict 9 z
def digest (v : List Sig) : Nat := v.foldl (fun acc a =>
  let z := (a.1.toNat + 18446744073709551616 * a.2.toNat) % 2305843009213693951
  acc + (z*z*z % 2305843009213693951)) 0
def unpack (w : Nat) : Minor.Sample :=
  ⟨Fin.ofNat 64 w,Fin.ofNat 64 (w >>> 6),Fin.ofNat 64 (w >>> 12),Fin.ofNat 64 (w >>> 18),
    Fin.ofNat 64 (w >>> 24),Fin.ofNat 64 (w >>> 30)⟩
def bound (k : Nat) (v : List Sig) : Prop := v.Nodup → ∀ m ≤ k, ¬Live m 0 v.toFinset
def done (code : Nat → Nat) (dict : Nat) (t : Rows) (k : Nat) (v : List Sig) : Bool :=
  press (code (digest v + k * 87654321)) fun w =>
    if 68719476736 ≤ w then
      let j := w-68719476736
      Nat.blt j t.num && v.isPerm (t.get dict j)
    else Nat.ble (k+1) v.length && Minor.valid (unpack w) 0 v
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem done_sound {code dict t k v} (h : done code dict t k v = true)
    (rows : ∀ i < t.num, bound k (t.get dict i)) : bound k v := by
  rw [done,eq_press] at h
  split at h
  · obtain ⟨hj,he⟩ := Bool.and_eq_true_iff.mp h
    have z := rows _ (Nat.blt_eq.mp hj)
    have perm := List.isPerm_iff.mp he
    have eq : v.toFinset = (t.get dict (code (digest v + k * 87654321) - 68719476736)).toFinset := by
      ext x; simpa using (perm.mem_iff (a:=x))
    intro hn m hm live
    exact z (perm.nodup_iff.mp hn) m hm (eq ▸ live)
  · obtain ⟨hl,hv⟩ := Bool.and_eq_true_iff.mp h
    intro hn m hm
    exact Minor.noLive_of_valid hn hv (by have := Nat.ble_eq.mp hl; omega)
def flag (code : Nat → Nat) (dict : Nat) (t : Rows) (k : Nat) (v : List Sig) : Bool :=
  strictV v fun l => !(stepTest k 0 l (fun _ => false) (fun w => !(done code dict t k w)))
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem allRows {code : Nat → Nat} {dict : Nat} {t n : Rows} {k : Nat}
    (hn : ∀ i < n.num, bound k (n.get dict i))
    (test : ∀ i < t.num, flag code dict n k (t.get dict i) = true) :
    ∀ i < t.num, bound (k+1) (t.get dict i) := by
  intro i hi hv m hm live
  have h := test i hi
  rw [flag,strictV_eq] at h
  let cb := fun w => !(done code dict n k w)
  have hb : ∀ w, w.Nodup → ∀ l ≤ k, Live l 0 w.toFinset → cb w = true := by
    intro w hw l hl hh
    cases eq : done code dict n k w with
    | false => simp [cb,eq]
    | true => exact False.elim (done_sound eq hn hw l hl hh)
  have bad := reduced_step live hm hv rfl hb hb
  have e : stepTest k 0 (t.get dict i) cb cb = stepTest k 0 (t.get dict i) (fun _ => false) cb :=
    by simp [stepTest]
  rw [e] at bad
  change (!(stepTest k 0 (t.get dict i) (fun _ => false) cb)) = true at h
  rw [bad] at h
  contradiction
def span (p : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => true
  | n+1 => p (s+n) && span p s n
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem span_ok {p : Nat → Bool} {s : Nat} : ∀ {n}, span p s n = true →
    ∀ i, s ≤ i → i < s+n → p i = true := by
  intro n; induction n with
  | zero => intros; omega
  | succ n ih =>
    intro h i hi hj
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : i=s+n
    · simpa [he] using h1
    · exact ih h2 i hi (by omega)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem reject_of_bound (h : bound 10 raw)
    (zs : List Sig) (hs : Steps raw zs) (hl : zs.length ≤ 10) (ho : target ∈ raw ++ zs) : False := by
  obtain ⟨k,S,hk,live,sub⟩ := extract_steps hs ho
  have req := necessary raw (by decide +kernel) live sub
  exact h (by decide +kernel) k (by omega) (req.symm ▸ live)
end Cut
end PEqualNP.Outside.L_meta_29925.Check
namespace PEqualNP.Outside.L_meta_29925.Check
namespace Cut
def salts : Nat := 0x230006000000030005000c0000000f000200060000003900000006001c00100009004400060005009500000002000c0007003b0008004000040000002a000e0003005a000000060001000500160005000a004a00030000000600090010000b0003000f00000006001c001e000000230000000c0004000200020003000700170004002000290006000000070002000200030012002500010000000200080001000c000100020004001b000b00230037000000000000000c00110005000a00030000001200750018000200000001001700280000000c00070008001e000700000002001800070005000300000000001f000400000005002100010004002000000004002b00000000003a001a0005001400090008000200060008000400060000000000120007001d000100120007000000000017001200830005002c000c000b0007004e000900020000004a0001003b004e0004000200010014001000150000000900010000002400110001000100150036001500030006000800030000000400290000007f003c00270000000000000042000f00cd000b0003003b000d0006000b000800000000000000010003001c0000001b000200010003001b0013000000000002000500000013002700160006000500030006001d00070005001d0001000b000000000003000900050007007e0005000f0002000100020004000600030000000100000007000400000000000c00050012000300050014000900010000000b000100160029002c000c0009000f000e0011000000090018001c00170003000200020005000000150001000900090002000000030000002d002f003400000001001800010028000f001c0003000400010006000300070003000b000100150002004a000000340002001800010003000b000500020016000c000700040002006d000000600048000f001000070001000100000039001600100000000b00040006000400220008000000010002001e00040001000900260008000e000100280007000a000500000000000600000005000b000d0000000c001400070006007e000b00040001000100030000000100000005000e002b001e001e000100030002000a00040006000200160005000000000003000200060013000400050006000d000000090011001800010010000a0032000000470002000100080000001d000b00220007000900160000002a0008001800000002000000010000000600100005000800100007000400000036001c00150004002300000053000200180015000300020002000c00080021002f008a0001001800020006000400080000000700010012000500000000000200010001000e0090000700030013002f0027000200070001000700020006000c000b00170000001d000d000d000200100000000700060003000000110001000c0003000800040009000400050064000500080015000900010006000f0000004c003000020000000f0000006400000003000100070020000100010004000c0000000300000000001b0001000000010003000a0004000000020000000800030000000800250000000100060013000a0003000000000001001f000f000000010001001600040001000000070018001e002b0002003300020005005e000700190000000e002000000002000b000100020004000900120000003c001a0004000c001b000200270036000100000003000a000c001c0002002700040000000f00010003000100010000000b001800040007000400080001000000030000002c00060006001a0002000f0010000c0001001e00050000000b000300040003000500160002000000010001000300160000000a000000000002001600090003000e0001000000000008000100010018000000000004001000000001000000010003001800000003001c001600000004000000080003000b0011002100060003000f00020008001100000025000000000003000200010008000000170000000f001900090000000000020002000d003500010006000100060003001000220000000400ac0005000b000300000076007d00070000001200010000000e001e001200050002000c0051000a00030000000500010000000100000004000100000000000f0010001a000300010000000100040002000100040006000000090008000000440029000c00140000001e000000010002000000010001000100020006000000010000001a0003000300000002000b0000000a00040001009e0018000000010023000000040009000200020000000100020007000500060001000200030001000d0019005400000025000300160009000000050022000100000001004400100000000900020006000000120001001b001800a300010008000000040002003b00000017000000090001001400010003000b000200000000000a0032000b000700060002000d0002000d00000007000000120015000300050003003200070000000c002b000000050000005a00020008002500070000003a00010003000a00040000000600000023000100070003000200010012000100060019000300060007000b00050000000b000400050000000800010000000000000000001400040000000e00020009000000010013001300020001001400020013000200000015001a00220000000600590001000b003c00740004000d0003000b0004000d000100030045000c00020001001600210000000d000a000200010008001e00000001000a00030044000400060011000100170001002d000000000003000300740014000f0001000400080001000000020000000600000001001f000500080015002a000000010001000e000400240000001a00010003000a001f0000002e000100000003000400440000002e0000000300140001000000210051000d000100060000002200030004003a001d0000000d00050018001200010006000b000f000800020002001a0000001f00280009000100000000000a00010002000a000a0002000200050002000e006c0000000f00010012000400000000004b000c0006000400030013000900150000001800030010000000050014000000180003000000060000000200080032000100050006001e002100010000001200000000000700490002000000010009001d001b001e000600af000900070002000f0000000a00110009000300020000000200020006000400040002000c00000005000d0000000600050000000500000002000f00010057000200100000000c0017000100380011000600000014000b000d00130001003200020009000a000d00000008000b0015002d000700010009000a000700070003000d0016000a000200000000000d00070005000000040000000a001c0004001200240007001200000002000c0001000200000007000100020015002100000000001e0011000100000001000c0000000000090041000000000004000400c7000900080001000700030000000000050002001d0003000600160000000700010000003900180030000f00000008000000440006000d00030002000b00000000002000000014000b0004000100040003000100030016000c000d000000000003000900010000000200050002004f0003000200120004000700030002001b0001000200080000000900020011000a00050005000e0001000c000f001000060020001b0004000200050000000000010003000000490000001b0002000f0000000800000047
def hints : Nat := 0x2075011830423801c0081d40460c01a31c00600d18e0030068c7001803463800040ea0230600d18e040000000f40081d40460040ea02300207501180103a808c0000000000c01a31c080000000b830068c7000081d40460000000000600d18e0400000000c1803463800c01a31c00600d18e000103a808e0000000bc0c01a31c00600d18e000000000001803463800040ea0230008952ae030068c7000081d40460040ea0230600d18e000085547381803463800040ce02380000003f00000000020000000320000000000600d18e000000000000000000000c01a31c0000000000030068c7000042aa39c0440ea0230600d18e000103a808c0081d40460c01a31c00600d18e0061055473818034638100000000800000000000000000001803463800040ea0230600d18e0030068c70200000019a0040ea02300000000040000001f40081d40460040ea0230000000000000000000000000000000000000000000000030068c7000000000000040ea02300000000000103a808c1803463800040ea02380000005a830068c7001803463800c01a31c00600d18e040000001640081d40460c01a31c00600d18e0030068c7000000000000c01a31c0002075011830068c7001803463800000000000600d18e0000000000018011c00e0c01a31c00600d18e0030068c7001803463800c01a31c0002075011830068c7000081d40460c01a31c00010aa8e7030068c7001803463810000000d7000000000030068c70018034638100000001c0600d18e000103a808c0081d40460c01a31c000207501180103a808c0000000000040ea0230600d18e000000000001803463800c01a31c00600d18e000103a808c000000000000000000002075011c000000330000000000000000000002075011830068c702000000106000000000002075011c0000001640081d40470000000310600d18e0030068c7001803463800c01a31c00600d18e0030068c7000000000000000000000600d18e040000001480000000000c01a31c0800000041030068c7000081d4046000000000000000000000000000018034638000000000000207501180000000000000000000000000000600d18e0030068c7001803463810000000840600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c0002075011c0000000080081d40460c01a31c00600d18e0030068c7000081d40460040ea0230600d18e000105547381803463800c01a31c0800000044c0000000041803463800c01a31c080000003d030068c7000042aa39c0c01a31c00600d18e0030068c7000081d40470000000180600d18e0030068c70200000000f0000000460010aa8e7400000000c1803463800c01a31c00600d18e000103a808c08a1aa0380021551ce0600d18e0030068c7020000001100c108e007002075011830068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c080000003280085547381803463800c01a31c0002075011830068c7000081d40460c01a31c00600d18e000103a808c08022a3b90000000220600d18e000000000001803463800c01a31c0000000000000000000018034638000112a55c0600d18e0030068c7000081d40460c01a31c0002075011830068c70200000004e000000000000000000030068c7001803463800c01a31c0002075011830068c7001803463800000000000600d18e0030068c70018011c00f000000041000000000030068c7001803463800c01a31c00600d18e000000000001803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e0030068c7000000000000c01a31c000000000000000000001803463800040ea02300207501180103a808c1803463800c108e0070600d18e000103a808c1803463800c01a31c00600d18e000000000001803463800000000000600d18e000000000000000000000c01a31c000000000000044a95700000000000c01a31c0000000000030068c70018034638000000000006004700380000000001803463800c01a31c00020750118200170e540081d4047000000081002075011830068c70018034638000000000004002e1ca80000000000000000000040ea02300000000000000000001803463800c01a31c0000000000030068c7000000000000c01a31c080000001e830068c7020000001450000000730600d18e040000000481803463800c01a31c00600d18e000000000001803463800c01a31c000000000000000000020000001340c01a31c000000000000000000000000000000c01a31c00600d18e000103a808c1000b872a0000000000600d18e00000000000180346381000000076800000008030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e000085547380000000000c01a31c000000000000000000001803463800c01a31c00600d18e0000000000018011c00e0040ea023800000058030068c7000000000000c01a31c0002075011830068c7001803463800c01a31c00600d18e0030068c7000081d404608005c3950600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c000000000000103a808c18034638100000004f0600d18e0030068c7001803463800000000000600d18e0030068c7000000000000040ea0230600d18e0030068c7000081d4046000000000800000063030068c7000081d40460040ea0230010aa8e7030068c7001803463800040ea0230600d18e0030068c7001803463800040ea0230600d18e000000000001803463800c01a31c0800000050c0000002c41803463800c01a31c0002075011830068c7001803463800040ea0230600d18e000103a808c1803463800c01a31c00600d18e0000855473a0000000000c01a31c0800000024030068c7001803463800c01a31c00600d18e0000000000018034638100000002100000000000085547380081d40460c01a31c0000000000030068c7020000000a00c01a31c00600d18e000000000000000000000040ea0230600d18e0030068c7000081d40460040ea023002075011830068c7020000000f00021551ce0600d18e040000001e80082aa39c000000000002075011830068c7001803463800021551ce800000010030068c70200000004800000000000207501180103a808c0081d40460000000000600d18e000103a808c0081d40460c01a31c0000000000030068c7001803463800c008e007060047003c00000024c180346380000000000800000002030068c7020000001b10000000b60600d18e0030068c70018011c00e0c01a31c00600d18e0030068c7001803463800021551ce0600d18e0030068c7001803463800c01a31c00600d18e0030068c70200000007208005c3950600d18e0030068c7000081d40460040ea02300000000000000000001803463800c01a31c00600d18e0030068c700180346381000000008060047003c0000000c80082aa39c0c01a31c080000000f830068c7000081d40460040ea02304002e1ca80103a808c1803463810000000950600d18e000103a808c1803463800c01a31c00600d18e0030068c7001803463800421551ce0600d18e0030068c7002803463800040ea0230600d18e0030068c7001803463800c01a31c0002075011830068c70018034638100000002d002075011c0000000740081d40460c01a31c0002075011830068c7001803463800000000000600d18e0030068c700180346381000000002800000005030068c7001803463800c01a31c0800000041830068c7020000000a20c01a31c00600d18e0400000002c0042aa39c0c01a31c000207501180000000000000000000c01a31c00600d18e0030068c7000000000000c01a31c00600d18e0030068c7000081d40460040ea02380000004e830068c7001803463800c01a31c00600d18e0030068c702000000045000000012002075011830068c7001803463800040ea0230600d18e0030068c7000000000000040ea023800000018030068c70018034638100000009c0600d18e040000001a80081d404700000002c0600d18e000044a95701803463800c01a31c00600d18e0030068c700180346381000000003002075011830068c7000081d40460c01a31c00600d18e000000000001803463800c01a31c0002075011830068c7020000001a808005c395060047003c0000002a81803463800040ea023800000006830068c7001803463800c01a31c0002075011830068c7001803463800c01a31c0042075011800000000018034638000000000000000000040000000d81803463800c01a31c0000000000030068c7000000000000c01a31c00010aa8e7030068c70200000004c0c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c7020000000380c01a31c00600d18e000044a95701803463800040ea0230600d18e000103a808c1803463800000000000600d18e0030068c7000000000000c01a31c00600d18e040000000781803463800c01a31c004002e1ca80000000001803463800c01a31c00600d18e0030068c7001803463800040ea023002075011830068c70200000004600000000000207501180085547381803463800040ea023002075011c0000001100000000000c01a31c00000000000200170e541803463800c01a31c00600d18e0030068c7001803463800040ea0230800d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c0800000002030068c7001803383800c018e1c00600d18e000000000001803463800c01a31c080000000580000000001000b872a0c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e0030068c7001803463800021551ce0600d18e040000000001803463800c01a31c0800000026830068c7001803463800c01a31c00600d18e000085547381803463800c01a31c00600d18e00200170e54180346380000000000000000000030068c7001803463800040ea02380000003a030068c70200000014a0021551ce800000014400000004c1803463800c01a31c080000000380085547381803463800c01a31c0000000000030068c7001803463800021551ce000000000030068c700180346380000000000002075011830068c7001803463800c01a31c00600d18e000103a808e00000011c0c01a31c0800000024030068c7001803463800c01a31c00600d18e0030068c7001803463800c008e0070600d18e00000000000000000000000000000000000000040068c7541803463800000000000600d18e0030068c7001803463800c008e00780000000a830068c7000081d40460000000000010aa8e7030068c7001803463800000000000600d18e0011808dca80000000000040ea0230600d18e000000000000081d40460c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c0000000000030068c7001803463800040ea023800000022c00000023c18009c00e0c01a31c0060047003830068c7001803463800040ea0230600d18e0030068c70018011c00e1841551ce0600d18e0030068c7001803463800021551ce0600d18e0030068c7001803463800040ea023002075011830068c70018034638100000006780000004b83006387001803463800c01a31c00610d18e0030068c7000081d40460c01a31c00600d18e0400000002c1803463800c01a31c00600d18e0030068c7001803463800c01a31c080000006a80044a95701803463800040ea0230008952ae030068c7003042aa39c0021551ce0600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800000000000600d18e000103a808c1803463810000000a30600d18e0030068c7001803463800c01a31c00600d18e0030023801c1803463800c01a31c00600d18e00000000000180346380000000000800000049030068c70200000008d0000000890600d18e000103a808c1803463800c01a31c0002075011800000000018034638000000000000000000000103a808c1803463800c01a31c00600d18e0030068c7000042aa39c0c01a31c0002075011830068c7000000000000c01a31c0000000000000000000018034638000000000000207501180000000001803463800c01a31c00600d18e0040068c7001803463810000000260600d18e0030068c7001803463800c01a31c00010aa8e7030023801c1000b872a0040ea02304002e1ca830068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7003082aa39c0040ea0230600d18e0030068c7000000000000c01a31c00600d18e0030068c7002803463801001a3395800000053830068c7000081d40460c01a31c080000005c00103a808c1803463800c01a31c0002075011830068c7001803463800000000000600d18e0030023801c18211c00e0040ea023800000047830068c7001803463800c01a31c00600d18e040000001bc0042aa39c0040ea0230600d18e0030068c7001803463800c01a31c0002075011830023801c0000000000c01a31c00600d18e006085547380000000000c01a31c00600d18e0030068c700180346380000000000000000000030068c7001803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e0030068c7001803463800000000000600d18e000103a808c1803463800c01a31c00600d18e0000000000018034638000000000000000000000000000001803463800040ea023002075011830068c7020000000aa0040ea0230600d18e0030068c7001803463800840ea0230600d18e0030068c7020000000da1401a31c00600d18e0030068c7001803463800c01a31c00600d18e000103a808c1803463800c01a31c080000000a830068c7000081d40460040ea0230600d18e0030068c70018034638000112a39c042075011830068c700002254ab80000000000600d18e0400000001a0000000c000000000080000004e830023801c0000000000c01a31c00600d18e0030068c7001803463800000000000010aa8e7030068c7001803463800c01a31c00600d18e0030068c700180346380000000000002075011830023801e0000001660c01a31c000207501180103a808c1000b872a0c01a31c00018aa807030068c7020000000d40040ea0230600d18e0030068c7001803463810000000b2800000001830068c7020000000640040ea0230600d18e0030068c700180346381000000075002075011830068c7001803463800040ea023800000009c0000000081803463800c01a31c080000002f40000001a40081d40460c01a31c00600d18e0030068c7000081d40460c01a31c0002075011830068c7001803463800c01a31c080000001a830068c7001803463800c01a31c0000000000030068c7000081d40460040ea0230600d18e0030068c70200000000700000007c80000001240000000b418034638008005c3950020750118000000000002254ab900000000b00000000000000000001803463800c01a31c00600d18e0030068c7000000000000021551ce0600d18e0030068c7001803463800c01a31c004002e1ca80103a808c1803463800c01a31c00600d18e000000000001803463800040ea0230600d18e0030068c7020000000280c01a31c00010aa8e7030068c7001803463800040ea0230600d18e0030068c7001803463800000000000600d18e0030068c70200000018600000000000000000000000000001803463800c01a31c080000005800000000020000000980c01a31c0060047003c0000002141803463800040ea02380000000700000000001803463800c01a31c00600d18e0030068c7000081d404700000000804002e1ca830068c70200000002c0000000000600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c080000001e030068c7000000000000000000000600d18e0030023801e00000001e0000000000600d18e0030068c7001803463800040ea0230600d18e000000000000081d4046000000000060047003830068c700000000000000000000000000000030068c70018034638000000000000000000000000000000000000000c01a31c0000000000030068c7001803463800c01a31c0002075011850068c7001803463800000000000600d18e000000000000000000000c01a31c00600d18e0030068c7000000000000c01a31c0800000022830068c7001803463800000000000600d18e0030068c70018011c00e000000000800000009030068c7001803463800c01a31c00600d18e040000001480000000000040ea02300000000000000000001803463800000000000600d18e0030068c70000000000100000008d0600d18e0000000000000000000000000000000000000000103a808c1803463800000000000600d18e000103a808c0042aa39c0c01a31c00600d18e0030068c7001803463800000000000600d18e0000000000018011c00e0000000000600d18e000085547380081d4046000000000002075011830068c7001803463800000000000600d18e000000000000000000000040ea0230600d18e000000000020000000020c01a31c00600d18e0030068c7020000001ba0c01a31c0002075011830068c7001803463800c01a31c080000004f80000000001803463800000000000600d18e0030068c7001803463800c01a31c0000000000030068c7000000000000c01a31c00600d18e0030068c7000000000010000000990600d18e000000000000081d40460c01a31c00600d18e0030068c7000000000010000000cf00207501180103a808c0000000000000000000600d18e0030068c7001803463800c01a31c00600d18e0030068c700002254ab80c01a31c00600d18e0030068c70200000003500000009f0600d18e0030068c7001803463800c01a31c00600d18e040000000001803463800c01a31c0800000025830068c7000042aa39c0c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c00600d18e000085547381803463800c01a31c0000000000400000021e0000000600c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c00608d18e040000000801803463800c01a31c000207501182103a80540081d40460c01a31c0002075011830068c70018034638008005c3950600d18e000103a808c1803463800c01a31c000000000000000000001803463800c01a31c080000000300000000001803463800c01a31c0060847015030023801c0081d40460c01a31c080000003280103a808e0000000780c01a31c0002075011830068c7000081d40460c01a31c00600d18e000103a808e0000001000c01a31c0002075011830068c7001803463800c01a31c0002075011830068c7001803463800040ea0230600d18e0400000016c180346381000000098000000000030068c7001803463800c01a31c00600d18e040000001900000000000c01a31c0002075011830068c700002254ab8000000000002075011830068c7001803463810000000e200000000000103a808e0000001000c01a31c00600d18e0000000000200000012e0c01a31c00600d18e0030068c7000000000000c01a31c0800000059830068c7001803463800c01a31c00600d18e000103a808c0081d40460c01a31c00600d18e000044a957200000000c0000000000600d18e000103a808e00000007100000002e0600d18e000103a808c1803463800c008e007060047003830068c70018034638008005c3950600d18e000000000000081d40460c01a31c0000000000030023801e0000000d900000000a0600d18e0030068c7020000000da0c01a31c080000001400103a808c1803463800040ea023000000000030068c7001803463800040ea02300000000040000000d40000000000000000000600d18e000103a808c0081d40460c01a31c000000000040000001ec00000000100000001b0600d18e0400000004c0000000000c01a31c00600d18e0030068c700180346380000000000800000043030068c7001803463800c01a31c00600d18e0030068c7000082aa01c00000000000000000000000000000081d4046000000000000000000030068c7000082aa39c0c01a31c00010aa8e7030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c0000000000030068c7001803463800c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c700002254ab800000000006084700380000000000042aa39c000000000002075011830068c7020000001b40c01a31c0000000000050c4a8e1c1803463800c01a31c00600d18e0040068c700002254ab80c01a31c00600d18e0030068c7001803463800c01a31c00600d18e000103a808c1803463800c01a31c000000000000103a808c1803463800040ea0230600d18e000103a808c0081d4046000000000800000031800000000018211c00e0c01a31c00600d18e0030068c700002254ab80000000000600d18e0400000030200000008e0c01a31c00600d18e000000000000000000000c01a31c00600d18e0030423801e00000000c0000000000600d18e0030068c7001803463800c01a31c00600d18e000103a808c1803463800040ea0230600d18e000000000000081d40460c01a31c00600d18e000000000001803463800c01a31c0002075011c0000001980000000000c01a31c000000000000000000000000000010000000170600d18e0030068c7000000000000c01a31c0000000000030068c70200000008c0040ea0230600d18e0030068c7020000000d00c01a31c00600d18e0030068c700000000000000000000002075011830068c7001803463801401a31c00600d18e000103a808c1803463800c01a31c00600d18e040000003940081d40460c01a31c00600d18e0030068c7000042aa39c0c01a31c00600d18e000103a808e0000000380c01a31c00600d18e0030068c700180346380000000000800000052830068c7020000001040000000000600d18e0000855473818034638100000005a0600d18e000103a808e0000000a20c01a31c0002075011830068c7001803463800040ea0230600d18e000103a808c1803463810000000ad060047003c0000003920000000280c01a31c00600d18e0030068c7000042aa39c00000000000000000000044a95701803463800040ea023060047003830068c7001803463800c01a31c00600d18e0000855473a00000005c000000000000000000030068c7020000000960c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0000000000018011c00e0c01a31c0002075011830068c7000042aa39c0c008e007800000020830068c7000000000000c01a31c080000004580103a808c1803463800c01a31c0000000000030068c7000000000000040ea0230600d18e040000000281803463800c01a31c0000000000030068c7001803463801401a31c000000000040000000d000000000000000000080000002540000002bc00000000100000000e0600d18e0030068c7001803463800c01a31c000207501180000000000081d40460040ea0230010aa8e7030068c700002254ab80c01a31c000000000040000002901803463800040ea02300000000040000000cc1803463800c008e007000000000030068c7001803463800c01a31c00600d18e000103a808e0000000120c01a31c0000000000000000000018034638100000000d0600d18e000000000000000000000c01a31c0000000000030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c0000000000030068c7001803463810000000110600d18e00200170e5418011c00e0c01a31c00600d18e000103a808c1843463800c01a31c00600d18e000103a808c0081d40460040ea0230600d18e0030068c7003082aa3d40c01a31c0002075011c00000003600000001a0c01a31c00600d18e000103a808c1803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e040000000781803463800c01a31c00600d18e0030068c7001803463800040ea0230600d18e000103a808c0081d40460c01a31c0800000000830068c7020000000360021551ce0a00d18ea830068c7001803463800c01a31c0060047003830068c7001803463800c604e0070600d18e0030068c7000081d40460c008e00780000000100103a808c1803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e00404070ea8180346381000000007002075011830023801c1803463800c01a31c00600d18e000103a808c1803463800040ea02380000004d830068c7000042aa39c0c01a31c080000003e030068c7001803463800c01a31c0002075011830068c7000081d40470000000540600d18e000103a808c1803463800040ea0230600d18e0030068c7000042aa39c0c01a31c00600d18e040000000f81803463800c01a31c080000001200103a808e00000002c0c01a31c00600d18e0030068c7020000000ba0c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c700088046e5400112a55c0600d18e0030068c7001803463810000000450600d18e0030068c7001803463800c01a31c004002e1ca80103a808c1803463800c01a31c0000000000030068c7000081d40460040ea0230600d18e001103a808c00818e0460c019c1c00600d18e0030068c7001803463800c01a31c0002075011830068c7001803463810000000160600d18e0030423801c0081d40470000000550600d18e0030068c7001803463801401a31c00600d18e0030068c7000081d40460c01a31c00600d18e040000002780042aa39c0c01a31c00600d18e0030068c7001803463810000000790600d18e0030068c7001803463800c01a31c00600d18e000103a808c1803463800021551ce0600d18e0030068c7000081d40460c108e0070600d18e040000000420000000220440ea0230600d18e0030068c7000042aa39c0c01a31c00008952ae00103a808e0000000c20c01a31c00600d18e000103a808c0081d40460c01a31c00600d18e0030068c7001803463800c008e0070600d18e00200170e541803463800440ea00e002075011c00000009a0000000220c01a31c00600d18e040000002e01803463801401a31c00600d18e000103a808c180346380000000000800000070830068c7020000000000040ea0230600d18e0030068c7020000000720c01a31c00600d18e000103a808c000000000000000000800000057030068c7000081d40460000000000600d18e000000000001803463800000000000600d18e000000000001803463800040ea02300000000000103a808c1803463800c01a31c00600d18e040000002681803463800c01a31c0023011b95030068c7000081d40470000000060600d18e000000000000081d40460040ea02380000000780103a808c0000000000040ea0230600d18e000103a808c18034638000112a55c80000000900105547381803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c70018034638100000003f0600d18e0030068c7020000000f20c01a31c00600d18e0030068c7001803463800c01a31c0002075011c0000000500000000000c01a31c00600d18e0030068c7000000000000021551ce0600d18e0030068c7000000000000c01a31c000207501180000000001803463800c01a31c0002075011830068c7000000000000c01a31c080000005f030068c7020000000900c01a31c00600d18e000044a9570088046e540040ea02300206a811830068c7020000000360c01a31c0002075011830068c7000021d4ab80021551ce04002e1ca80103a808c1803463810000000490600d18e000103a808c1803463800040ea023002075011830068c7001803463800040ea0230600d18e0030068c7001803463810000000160600d18e0030068c7001803463800040ea0230600d18e0030068c7000081d40460c01a31c00600d18e000103a808c18034638000112a55c0600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800021551ce00207501180103a808c1803463800c01a31c00600d18e000103a808c1803463810000000400600d18e0030068c70200000009e0c01a31c00600d18e0030068c7000042aa39d0000000040600d18e000103a808c18034638100000000980000006380103a808c18034638008005c3950008952ae030068c7001803463800c01a31c00600d18e0030068c70018034638008005c39504002e1ca830068c70018034638100000006b0c18951c3830068c7020000000830000000560600d18e0030068c7001803463800040ea023800000052030068c7001803463800c01a31c00600d18e000103a808c0081d40460c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0400000001c1803463800c01a31c0002075011830068c70018011c00e0c01a31c00600d18e0030068c7000081b80470000000390600d18e0030068c7000081d40460c01a31c00600d18e0030068c7000042aa39c0021551ce0600d18e0030068c7001803463800c01a31c00010aa8e740000000081803463800c01a31c0002075011830068c7001803463810000000290600d18e0030068c7001803463800040ea0230600d18e0030068c70200000005e0c01a31c0002075011830068c7020000001c60c01a31c00600d18e0030068c7001803463800c01a31c004002e1ca80103a808c0081d40460c01a31c00600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800040ea02380000000300103a808c1803463800c01a31c00600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800000000000010aa8e7030068c7001803463800040ea0230600d18e0030068c7020000001720c01a31c00600d18e0030068c7001803463800c01a31c000000000000103a808c180346381000000091002075011850c4a951c18011c00f0000000760600d18e040000002dc0081d40460c01a31c00600d18e000044a95701803463800c01a31c00600d18e000000000000081d40460c01a31c0002075011830068c700002254ab90000000440600d18e000103a808c0081d40460c01a31c00600d18e000103a808c1803463800c01a31c0800000048830068c7001843463800c01a31c0800000015830068c7000081d40460040ea0230600d18e0030068c700180346380000000000000000000400000011c1803463800c01a31c0002075011830068c7001803463800040ea023800000010830068c7020000000120c01a31c00600d18e0000c4a95701803463800c01a31c080000003f830068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c0002075011830068c7000000000000040ea02300207501180103a808c1803463800040ea0230600d18e0030023801c0000000000000000000600d18e000000000001803463800040ea0230600470038200170e541803463800040ea023002075011c0000003580081d40460c01a31c00600d18e0030068c7001803463800c01a31c006084700380103a808c1803463800040ea0230600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e040000002101803463800c01a31c004002e1ca830068c7020000000330000000220600d18e0030068c7000000000000c01a31c00600d18e0030068c7020000001840c01a31c000000000000000000001803463800c01a31c00600d18e0030068c7000000000000000000000600d18e0030068c7001803463800c01a31c0002075011830068c7001843463800000000000600d18e040000002b0006254ab80c01a31c00600d18e0030068c702000000041000000087002075011c0000000781803463800040ea02380000000f830068c7001803463800021551ce0600d18e0030423801c0081d40460c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c080000001b830068c7020000001c1000000010800000046030068c700002254ab80c01a31c00008950ee0008554738180346380000000000002075011830068c7001803463800c01a31c00600d18e000000000020000000840c01a31c00600d18e0030068c7000000000000c01a31c00600d18e0030068c7000000000000000000000600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800021551ce0600d18e0030068c700180346381000000043800000039400000004818034638000112a55c0600d18e0000855473a00000016c0c01a31c000000000000103a808c18011c00e0c01a31c00600d18e0030068c7000081d40460021551ce0600d18e0030068c70018034638100000000c0600d18e0400000000818034638010101c007002075011830068c7000081d40460c01a31c0000000000030068c7001803463800c01a31c080000000500000000000081d40460c008e00780000005100000000001803463800040ea0230600d18e000103a808c180346381000000077800000049830068c7000042aa39c00000000004286e00a80103a808e0000000540c01a31c0000000000030068c70000000000000000000000207501180103a808e0000000020c01a31c0800000007400000009c18034638100000006780000005880103a808c1803463801841551ce80000004b00103a808e0000000160c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030023801c1803463800c01a31c00600d18e0400000015c0042aa39c0c01a31c080000000880103a808c1803463801401a31d50600d18e0400000007418034638008005c3950600d18e0030068c7001803463800c01a31c00600d18e0030068c70018034638100000003b80000006f830068c7001803463800c01a31c00600d18e00200170e560000000e60c01a31c00008952ae030068c7001803463800c01a31c00600d18e0030068c7000081d40460021551ce0600d18e040000002b20000001b80c01a31c0002075011830068c7000081d40470000000630600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e000103a808c18034638100000000a002075011830068c7000081d40460021551ce0a18952ae030068c7000000000000c01a31c000207501180103a808c1803463800040ea0230600d18e000103a808e0000000161401a31c00600d18e000103a808e0000000e20c01a31c080000001781085547381803463800440ea0230600d18e000000000001803463800c008e0070600d18e04000000248180346380000000000000000000400000022a0000000a00c01a31c080000000c030068c7000081d40470000000b20600d18e0030068c7000081d40460c01a31c00600d18e0400000026000000000000000000080000004f030068c7001803463800c01a31c00600d18e000085547381803463800c21a31c00600d18e000000000001803463800c01a31c00600d18e0030068c7001803463810000000a80600d18e0030068c7001803463800c01a31c00600d18e0030068c7000081d40470000000560600d18e0400000008c0081d40460c01a31c00600d18e00200170e541803463800c01a31c0800000009030068c7000081d40460000000000010aa8e7030068c7001000b872a0c01a31c0800000021030068c7001803463800040ea0230600d18e0400000000a00000001d0000000170600d18e000000000001803463800c01a31c00600d18e000085547381803463800c01a31c000207501180103a808c0081d40470000000130600d18e040000002981803463800c01a31c00018aa8e7030068c7001803463800021151ce0600d18e0030068c7000081d40460c01a31c00600d18e0030068c7000081d40470000000400600d18e0030068c7020000000080040dc0230600d18e0030068c7001803463800c01a31c00600d18e00200170e541803463800040ea023060047003830068c7001803463800c01a31c000000000040000000801803463800c01a31c00c18ae0f5030068c7001803463800c01a31c000207501180103a808c1803463800c01a31c00600d18e0030068c7020000000180040ea0230600d18e0030068c7001803463800c01a31c0002075011830068c7020000000280c01a31c00600d18e000085547381803463800c01a31c00600d18e000044a95701803463800c01a31c00600d18e001103a808e00000010208005c3950600d18e0030068c70200000015e0c01a31c0002075011c00000008818011c00e0c01a31c00600d18e0030068c7001000b872a0c01a31c00600d18e000103a808c1803463800c01a31c0800000032030068c7002003463800c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c7000081d40460c01a31c080000004d830068c7000081d40470000000bc0600d18e000103a808c1803463800c01a31c0800000012830068c70200000007c0c01a31c00600d18e0030068c7001803463800c01a31c080000000e830068c7000081d40460c01a31c0800000021830068c7000081d40460c01a31c00600d18e040000001fc1803463810000000340600d18e000103a808e0000001100040ea0230600d18e000000000020000000fa0000000000600d18e0030068c700000000000000000000000000000030068c7001803463800c01a31c080000000a830068c7000081d40460040ea0230008952ae40000000241803463800c01a31c00600d18e0030068c7000000000000c01a31c00600d18e0030068c70018034638000000000000207501180000000001803463800c01a31c00600d18e040000000380081d40460040ea0230c18951c3830068c70000000000000112a55c000000000030068c700002254ab80c01a31c0000000000000000000018211c00e0c01a31c000000000000000000001803463800040ea0230600d18e0400000009418034638000212a55c800000053030068c7001803463800c01a31c00600d18e0030068c7000081d404600112a55c80000003f030068c70200000000a0c01a31c080000000b80103a808c0000000000c01a31c080000000880000000020000001380021551ce0600d18e040000002801803463800c01a31c00600d18e0400000013818034638008005c395000000000030068c700180346380000000000000000000030068c7001803463800c01a31c004207501180103a808e0000000a6000000000800000018030068c7001000b872a0c01a31c00010aa8e7030068c7001803463800c01a31c080000005d030068c7000081d40460040ea0230600d18e000103a808e0000001880c01a31c00600d18e0030068c7000081d40460040ea0230600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800040ea023800000026c0000000f41803463810000000de002075011c0000000ac0081d40460c01a31c080000001f830068c7001000b872a0000000000600d18e0030068c7000000000000021551ce80000005500000000001803463800c01a31c00600d18e0030068c7001803463800840ea0230600d18e0030068c7001803463800c01a31c00600d18e0030068c7020000000540c01a31c00600d18e0030068c7001803463800c01a31c0000000000000000000200000006200000000000000000040000000b01803463800c01a31c0002075011830068c7001803463800c01a31c000000000000044a95701803463800c01a31c0000000000030023801c1000b872a0000000000600d18e0030068c700180346380000000000800000020030068c70018011c00e0000000000600d18e000000000001803463800c01a31c0000000000030068c70200000009c0c01a31c0002075011830068c7001803463800c01a31c080000004b030068c7001803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e000103a808c1803463800040ea023002075011c0000000141803463800c01a31c0800000054830068c7001803463800c01a31c00600d18e000103a808e0000000b00040ea023800000000830068c7000081d40460c01a31c00600d18e0030068c7000000000010000000080600d18e040000000381803463800c01a31c0002075007030068c7000081d40460c01a31c00008952ae00085547381803463810000000950600d18e002103a808c1803463810000000320600d18e0030068c7020000000420041551ce0600d18e0030068c7000081d40460040ea0230600d18e040000002f40081d40460c01a31c00600d18e000103a808c1803463800c01a31c00600d18e00200170e541803463800040ea0230600d18e0030068c70018034638100000002902008a8ee00103a808e00000004e0c01a31c00600d18e0030068c70018211c00e0c01a31c00600d18e0030068c7000081d40460000000000600d18e0400000025018034638100000006b000000000030068c7000000000000c01a31c0800000031030068c7001803463800040ea0230600d18e000103a808e0000000060c11a31c000207501180103a808c1803463800c108e0070600d18e000000000020000000760040ea0230600d18e000000000000000000000040ea023002063811800855473800000000100000001b002075011830068c7001803463800c01a31c0000000000030068c7001803463800c01a31c080000001b030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c0800000015000000000200000001e0c01a31c080000004500085547380081d40460040ea02300000000000103a808e00000000a0c01a31c00600d18e0030068c7000081d404700000000c0600d18e040000002501803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0400000033818034638100000000f0600d18e0000855473a00000000b00000002b0600d18e0030068c7000081d40470000000bb0600d18e0030068c70018034638100000006c0600d18e0030068c7001803463800000000000600d18e0030068c7000081d40460000000000600d18e000103a808c00000000100000003a0600d18e0030068c7001803463800c01a31c000207501180000000001803463800040ea0230600d18e000103a808c18034638100000005f0600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c00600d18e000000000001803463800040ea0230600d18e0030068c7001803463800040ea0230600d18e0000000000000000000100000000f80000001640000000ce0000000b700000001500000000000000000000081d404600000000004002e1ca80103a808c0000000000c01a31c0000000000000000000000000000000000000000000000000000000020000000260000000000600d18e0030068c7001803463800021551ce0600d18e000000000001803463810000000360600d18e000103a808c000000001000000071000000000030068c7000081d40460c01a31c00600d18e040000000de0000001940c01a31c00600d18e0030068c7000081d40460c01a31c0000000000030068c7020000000020c01a31c00600d18e001103a808c1803463800c01a31c0800000004c0000001741803463800040ea0230600d18e000085547380081d40460c01a31c00600d18e0030068c7000081d40460000000000600d18e000085547380081d40470000000080600d18e000000000001803463810000000150600d18e040000003401803463800040ea0230600d18e000000000000081d40460000000000600d18e040000000041803463800c01a31c00600d18e040000000dc1803463800c01a31c008080e1d5030068c70018034638100000003800000000000103a808c1803463810000000470600d18e040000000ba0000001460021551ce0600d18e0030068c7000042aa39d00000001d0600d18e0030068c7001803463800c108e0070600d18e0030068c7001803463800c01a31c0002075011830068c7000081d404700000001e0600d18e00200170e541803463800c01a31c00600d18e0030068c70018034638004402372a0600d18e0030068c700180346381000000023002075011830068c70018011c00f0000000ae800000002030068c7000000000000c01a31c0000000000030068c7001803463800c01a31c00800d19ca800000000018034638100000001080000005a00000000000081d40460c01a31c000000000000000000000081d404700000000500000000040000000d40000000010000000a00600d18e0030068c7001803463800c01a31c000000000040000001b81803463800000000000600d18e040000001dc2003463800040ea0230600d18e0030068c7000081d40460c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030023801c18211c00e0c01a31c080000001780103a808c0081d404700000006200000000000000000001803463800c01a31c00600d18e0030068c7001803463810000000340600d18e0030068c7000042aa39c0c01a31c0800000000030068c7000000000000c01a31c00600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800c01a31c0002075011830068c70018034638100000001c80000000b030068c7001803463800c01a31c00600d18e0030068c7001803463800c11a31c00600d18e0030023801c1803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e040000001d41803463800040ea023000000000030068c7001803463800040ea0230600d18e000000000000000000000c01a31c000000000000000000000000000000040ea0230600d18e000000000001803463800c01a31c0000000000030068c7000081d40460c01a31c000000000000000000000000000000c01a31c00600d18e0030068c7000081d40460c01a31c000207501183006707000000000000040ea02300000000000000000000000000000000000000600d18e000000000001803463800c01a31c000000000000103a808c0081d40460c01a31c00600d18e0030068c7020000000420c01a31c0002075011830068c7001803463800c01a31c00600d18e0030068c700180346380000000000800000003830068c7020000000300c01a31c00010aa8e7030068c7001823463800c01a31c00600d18e000085547380000000000c01a31c080000005b830068c7001803463800c01a31c006304700380085547380000000000000000000600d18e000000000001803463800c01a31c000000000000103a808c1803463800c01a31c00010aa8e7030068c7000081d4046000000000000000000011008dcaa00000010a0000000000600d18e000000000000000000000c01a31c000000000000085547380000000000040ea02300000000000000000000081d40460c01a31c0060847003830068c70018034638008005c3950600d18e0030068c7000081d404600112a55c0600d18e0030068c7001803463800000000000600d18e0030068c7020000000cc0c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e0030068c7020000000320040ea0230600d18e0030468c7000000000000040ea0230600d18e040000001a01803463800c01a31c00600d18e0030023801c0081d40460c01a31c000207501180000000000000000000c01a31c00600d18e000000000000081d40470000000c90600d18e0030068c7001803463800040ea0230600d18e0030068c7000081d40460c01a31c080000001d40000003041803463800c01a31c00600d18e000085547380081d40460c01a31c0002075011830068c70018034638008505c39504002e1ca830068c7001803463800c01a31c080000001d830068c70018011c00e0040ea0230600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c0800000047400000036c1803463800c01a31c00600d18e000103a808c1803463800c01a31c004002e1cac0000001500081d404700000000d0600d18e040000000a40081d40460c01a31c080000003080103a808c0081d40460c008e0070600d18e0400000014c1803463800c01a31c080000000380000000020000000340c01a31c00600d18e0030068c7000081d40460040ea023002075011830068c7020000000300040ea0230600d18e000103a808c0081d40460c01a31c0800000004030068c7020000001960c01a31c000000000000000000020000001520421551ce0600d18e000103a808c00000000100000005c0600d18e0030068c7000000000000c01a31c0002067011830068c7001803463800c01a31c000000000000044a95720000000200c01a31c0002075011c000000124000000001000000004002075011830068c7001803463800c01a31c000000000000103a808c1803463800021551ce00000000000103a808c0000000000c008e0070600d18e000103a808c1803463800c01a31c0002075011c0000003640081d4047000000014002075011830068c7001803463800c01a31c0002075011830068c7020000000b40440ea0230600d18e040000002ae00000000a0c01a31c000000000000000000000081d40460040ea0230600d18e040000001281803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e000103a808c0081d40460040ea0230600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c0800000003830068c70018011c00f0000000060600d18e0060c5547a81803463800c01a31c00600d18e0030068c7001803463800040ea0230600d18e0030068c7001803463800c01a31c000000000000103a808c0000000000840ea0230600d18e000000000001803463800c01a31c00600d18e0030068c7000000000000c01a31c00000000000000000000180346380000000000000000000030068c7020000000320c01a31c000000000000000000000000000000000000000600d18e00000000000180346380000000000002075011830068c7001803463800c01a31c0000000000030023801c002254ab80000000000600d18e0030068c70018034638000000000000000000000103a808c18034638100000000f0600d18e000103a808c0081d4046000000000060047003830068c7000000000000c008e00780000000d030068c7000000000000c01a31c0000000000030068c7000000000000c01a31c080000005080103a808c180346380000000000800000000030068c7001803463800000000000600d18e0030068c7001803463800040ea02380000005a00000000001803463800c01a31c08000000000200170e541803463800000000000600d18e000000000001803463800040ea023000000000000000000018434638100000008600207501180103a808c000000000000000000000000000030068c7001803463800000000000600d18e000000000001803463800c01a31c0002075011830068c7001803463800c01a31c00010aa8e7030068c7001803463800000000000600d18e0030068c7001803463800000000000600d18e0030068c70018034638000000000000207501180103a80380000000000c01a31c00600d18e040000000301803463800c01a31c00600d18e0030068c7020000000180c018e1c0002075011830068c7001803463800c01a31c0800000056c00000015c0081d40460c01a31c00600d18e0030068c7001803463810000000050600d18e0030068c7001803463810000000000600d18e0030068c70018034638100000001c0c18ae0f5030068c7000081d404600000000080000001440000001c00000000000c01a31c00600d18e0030068c7020000000660c01a31c00600d18e000103a808c1803463800000000000600d18e000000000001803463800c01a31c0000000000030068c7001000b872a0040ea0230600d18e0030068c7001803463810000000b5800000037830068c7001803463810000000d30600d18e0030068c7001803463800021551ce002075011830068c7020000000f60040ea023000000000030068c7001803463800c01a31c00600d18e0030068c7001000b872a0c01a31c0000000000030068c70028034672a0000000000008952ae00103a808e000000014000000000000000000030023801c1803463800c01a31c00600d18e0000000000018034638100000008d0600d18e0030068c7020000000620040dc0230600d18e000103a808c18034638000000000000206381180000000000081d40460040ea02300207501180103a808c1803463800c01a31c004002e1ca830068c7001803463800c01a31c00600d18e0030068c7020000000dc0c008e007002075011830068c7001803463800c01a31c00600d18e000000000001803463800c01a31c00600d18e0030068c7000082aa39c0021551ce800000053830068c7001803463800c01a31c0800000006400000007c0000000000c01a31c000000000040000000b40000000000c01a31c004002e1ca830068c7020000000740c01a31c0000000000030068c7000000000000c01a31c000000000000000000000000000000000000000800d18e0030068c7000000000000c01a31c000000000000103a808c0000000000000000000600d18e000000000001803463800000000000600d18e00008554738000000000000000000002075011830068c7000081d40460c019c1c000000000000103a808c0081d40460040ea0230600d18e000103a808e00000003a0040ea0230600d18e0030068c70000000000100000001a00000000000000000000000000000c01a31c00600d18e040000001a41803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e0030068c7000000000000c01a31c00600d18e0030068c7000000000000000000000600d18e000000000000000000000000000000600d18e000000000001803463800c01a31c000000000000103a808c1803463800021551ce0600d18e000103a808c1803463800c01a31c00600d18e04000000264180346380000000000002075011830068c7001803463800c01a31c0000000000030068c7000081d40460c01a31c00020750118300638700180346380000000000002075011800000000020034638000212a55c06004700380000000000000000000c01a31c00008952ae40000001701803463800c01a31c00600d18e0030068c7000081d40460c01a31c0000000000030068c7000081d40460c01a31c00600470038000000000002254ab80c01a31c0002075011c0000001081803463800021551ce80000002c00000000000000000000c01a31c00600d18e0000000000018034638000000000000207501181103a808e0000000000c01a31c00600d18e0030068c7020000000220040ea0230600d18e0030068c7020000000060c01a31c00600d18e000000000001803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c080000003c40000002400062aa39c0040ea023800000046030068c70018034638008005c39580000003000103a808c1803463810000000d10600d18e0030068c7000081d40460c01a31c0002075011830068c7000081d404700000004400207501180103a808c1803463810000000c80600d18e0030068c7020000000e80c018e1c00600d18e00200170e541803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e0030068c7000042aa39c0c01a31c00600d18e000103a808c18011c00e08005c3950018aa8e700000000001803463800c01a31c00600d18e000000000000000000000000000000600d18e0030068c7000042aa39d0000000bf0008952ae02143700541803463800c01a31c00600d18e000103a808e00000017208005c3950600d18e00200170e541803463801831551ce0600d18e0030068c7001803463810000000c50600d18e00214170e540081d40460040ea02380000000a030068c70018034638100000003e000000000030068c7000081d404614312a55c002075011c0000000fc1803463800c01a31c00600d18e0030068c7000081d40460c11a31c0002075011830068c7001803463800040ea02380000000d00000000000081d40460c01a31c004002e1ca830068c7001803463810000000a80600d18e000103a808c00000000000000000080000000480103a808c0081d40460c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e0030068c7001803463810000000d204207501180000000001803463800040ea0230600d18e0030068c7001803463800000000000600d18e000103a808c1803463800c01a31c0002075011c0000002ae0000001200c01a31c00600d18e000103a808c0042aa39c0040ea0230600d18e0030023801c1803463800040ea023002075011c0000001c80081d40460000000000600d18e000103a808c1803463800c01a31c0042075007030068c7001803463800c01a31c00600d18e000000000001803463800c01a31c00600d18e00000000000180346380000000000000000000030068c7000000000000c008e0070600d18e0030068c7001803463800c01a31c0002075011830068c7001803463800c01a31c00600d18e0030068c7001803463800040ea02380000002f830068c7000042aa39c000000000800000045c00000006c1803463800021551ce00207501180103a808c1803463800c01a31c00600d18e000103a808c1803463801001a31c00600d18e0030068c7020000000260c01951c00600d18e0030068c7001803463800c01a31c00600d18e0030068c7001803463800021551ce80000000b80000000001803463800021551ce0600d18e040000000601803463800c01a31c00600d18e0000000000028625470e0c01a31c00600d18e0030068c70018034638000112a55c000000000030068c7000081d40460000000000600d18e0030068c7000000000000c01a31c000207501180000000001803463800c01a31c00600d18e0030068c7000081d40460c01a31c00600d18e040000000941803463800c01a31c00600d18e0030068c7001803463800000000000600d18e0030068c700180346380000000000800000038030068c7001803463800c01a31c00600d18e0030068c7001803463800c01a31c004207501180103a808c1803463800c01a31c00600d18e00200170e540000000000c01a31c00600d18e0030068c700180346380000000000002075011801031c08c0081d40460c01a31c00010aa8e7030068c7000000000010000000100600d18e0030068c7001803463810000000040600d18e0030068c70018032a3800c01a31c0002075011c0000000640081d40460040ea0230600d18e000103a808c0081d40460000000000600d18e000103a808e0000000980c01a31c00010aa8e740000000f00000000000040ea02380000000f830068c700000000000000000000000000000030068c70018034638000000000080000002180103a808c1803463800c01a31c00600d18e0030068c7001803463800c01a31c00600d18e000103a808c1803463800040ea0230600d18e0030068c7020000000700c01a31c00600d18e0030068c7001000b872a0c01a31c00600d18e0021037005418034638100000000d
def oracle (h : Nat) : Nat := press ((salts >>> (16*(h % 1353))) &&& 65535) fun s =>
  (hints >>> (37*((h/1353+s) % 4669))) &&& 137438953471
def dict : Nat := 0xe1c1ffffffffffff03c7ffffffe00000d1a1fbf7efdfbf7e03e7ffffffffc000c991ffffffffffff03b7fffff01fff80c589fbf7efdfbf7eff9ffffff0003fffc181fbf7efdfbf7e0387fffff0000000b161f7efdfbf7efd03e7ffffffffc000a951cf9f3e7cf9f303f7ffffffffff80a549e7cf9f3e7cf9ffdfffffffe03fffa141c78f1e3c78f103c7ffffffe000009931ffffffffffff0377fff80fffff809529f3e7cf9f3e7cff7ffff80fffffff9121f3e7cf9f3e7c0367fff80fffc0008d19efdfbf7efdfbff3ffff8001fffff8911cf9f3e7cf9f30337fff8001fff808509e3c78f1e3c78ff19fff800003fff8101f3e7cf9f3e7c0307fff8000000008101e3c78f1e3c780301fff8000000008101cb972e5cb9720307fff8000000008101c78f1e3c78f10307fff8000000008101c3870e1c387003c7ffffffe000008101c3870e1c38700387fffff00000008101c3870e1c38700367fff80fffc0008101c3870e1c38700347fff80fe000008101c3870e1c38700337fff8001fff808101c3870e1c38700327fff8001fc0008101c3870e1c38700311fff800003f808101c3870e1c38700307fff8000000008101c3870e1c38700301fff80000000070e1ffffffffffff01e7fc07ffffc00068d1bf7efdfbf7ef01f7fc07ffffff8064c9fffffffffffffddffc07ffe03fff60c1bf7efdfbf7ef01c7fc07ffe0000058b17efdfbf7efdf01f7fc07ffffff8054a8f9f3e7cf9f3efdfffc07ffffffff50a078f1e3c78f1e01e7fc07ffffc0004c99fffffffffffffdbffc07f01fffff48913e7cf9f3e7cf01b7fc07f01fff804488f9f3e7cf9f3efd9ffc07f0003fff4081bb76eddbb76e0187fc07f000000040813e7cf9f3e7cf0187fc07f000000040813a74e9d3a74e0187fc07f00000004080f9f3e7cf9f3e0187fc07f00000004080b972e5cb972e0187fc07f0000000408078f1e3c78f1e0187fc07f000000040803870e1c3870e01e7fc07ffffc00040803870e1c3870e01c7fc07ffe0000040803870e1c3870e01b7fc07f01fff8040803870e1c3870e01a7fc07f01fc00040803870e1c3870e0197fc07f0003f8040803870e1c3870e0187fc07f00000003871ffffffffffff00f60007ffffff803469f7efdfbf7efdfcfe0007ffffffff3061f7efdfbf7efd00e60007ffffc0002c59efdfbf7efdfbfcfe0007ffffffff28518f1e3c78f1e300f60007ffffff802449e7cf9f3e7cf9fcde0007ffe03fff2041e7cf9f3e7cf900c60007ffe000002041c78f1e3c78f100c60007ffe000002041b76eddbb76ed00c60007ffe000002041a74e9d3a74e900c60007ffe0000020418f1e3c78f1e300c60007ffe000002041870e1c3870e101c7fc07ffe000002041870e1c3870e100f60007ffffff802041870e1c3870e100e60007ffffc0002041870e1c3870e100d60007ffe03f802041870e1c3870e100c60007ffe000001c39fffffffffffffc7e00000fffffff18317efdfbf7efdf007600000fffff801428f1e3c78f1e3cfc7e00000fffffff1021f3e7cf9f3e7c006600000fffc000102176eddbb76edd006600000fffc000102172e5cb972e5c006600000fffc0001020f1e3c78f1e3c006600000fffc000102078f1e3c78f1e006600000fffc000102070e1c3870e1c01e7fc07ffffc000102070e1c3870e1c0167fc000fffc000102070e1c3870e1c00e60007ffffc000102070e1c3870e1c007600000fffff80102070e1c3870e1c006600000fffc0000c19efdfbf7efdfbfc3e0000001fffff0811cf9f3e7cf9f300360000001fff8008118f1e3c78f1e300360000001fff8008116eddbb76eddb00360000001fff8008114e9d3a74e9d300360000001fff8008113e7cf9f3e7cf00360000001fff8008112e5cb972e5cb00360000001fff8008110e1c3870e1c301b7fc07f01fff8008110e1c3870e1c30137fc00001fff8008110e1c3870e1c300f60007ffffff8008110e1c3870e1c300b60007f01fff8008110e1c3870e1c3007600000fffff8008110e1c3870e1c300360000001fff800409e7cf9f3e7cf9fc1e000000003fff0409e3c78f1e3c78fc18000000003fff0408f1e3c78f1e3cfc1e000000003fff0408e9d3a74e9d3afc1e000000003fff0408e1c3870e1c38fd9ffc07f0003fff0408e1c3870e1c38fd19fc0000003fff0408e1c3870e1c38fcde0007ffe03fff0408e1c3870e1c38fc9e0007f0003fff0408e1c3870e1c38fc7e00000fffffff0408e1c3870e1c38fc5e00000fe03fff0408e1c3870e1c38fc3e0000001fffff0408e1c3870e1c38fc1e000000003fff0408e1c3870e1c38fc18000000003fff02011e3c78f1e3c7fe0e03f80000007f02003c78f1e3c78ffe0e03f80000007f02001c3870e1c387ff8ffffff000007f02001c3870e1c387ff0ffff80000007f02001c3870e1c387fece03ffffe0007f02001c3870e1c387fe8e03fff000007f02001c3870e1c387fe6e03f80fffc07f02001c3870e1c387fe4e03f80fe0007f02001c3870e1c387fe3e03f8001fffff02001c3870e1c387fe2e03f8001fc07f02001c3870e1c387fe1e03f800003fff02001c3870e1c387fe0e03f80000007f02001c3870e1c387fe0c03f80000007f0001c3870e1c387000000000000000000001870e1c3870e10006000000000000000183060c1830600101fc0000000000000183060c18306000c60007ffe00000000183060c18306000860007f0000000000183060c183060004600000fe00000000183060c1830600000000000000000000142850a142850000000000000000000010e1c3870e1c3000600000000000000010a142850a14200060000000000000001060c183060c100c60007ffe000000001060c183060c100860007f00000000001060c183060c1004600000fe000000001060c183060c100360000001fff800001060c183060c100260000001fc0000001060c183060c10016000000003f800001060c183060c1000600000000000000010204081020400101fc0000000000000102040810204000360000001fff80000102040810204000260000001fc00000010204081020400010000000003f80000102040810204000000000000000000000e1c3870e1c3800000000000000000000c183060c18300101fc00000000000000c183060c18300010000000003f800000c183060c183000000000000000000000a142850a14280000000000000000000081020408102000c60007ffe00000000081020408102000860007f00000000000810204081020004600000fe0000000008102040810200010000000003f8000008102040810200000000000000000000070e1c3870e1c0006000000000000000060c183060c18006600000fffc000000060c183060c18004600000fe00000000060c183060c1800260000001fc000000060c183060c180010000000003f80000060c183060c18000000000000000000004081020408100101fc00000000000000408102040810006600000fffc0000000408102040810004600000fe00000000040810204081000260000001fc0000000408102040810000000000000000000003870e1c3870e000600000000000000003060c183060c0187fc07f000000000003060c183060c0107fc000000000000003060c183060c00860007f000000000003060c183060c006600000fffc00000003060c183060c004600000fe0000000003060c183060c00260000001fc00000003060c183060c000600000000000000002850a142850a000600000000000000002040810204080187fc07f000000000002040810204080101fc0000000000000020408102040800860007f000000000002040810204080010000000003f800000204081020408000000000000000000000810204081020187fc07f000000000000810204081020107fc0000000000000008102040810200860007f0000000000008102040810200360000001fff80000008102040810200260000001fc00000000810204081020016000000003f8000000810204081020006000000000000000000000000000001f7fc07ffffff80000000000000000001e7fc07ffffc000000000000000000001c7fc07ffe00000000000000000000001b7fc07f01fff8000000000000000000197fc07f0003f8000000000000000000187fc07f000000000000000000000000137fc00001fff8000000000000000000101fc0000000000000000000000000000f60007ffffff80000000000000000000e60007ffffc000000000000000000000c60007ffe00000000000000000000000860007f00000000000000000000000007600000fffff800000000000000000006600000fffc0000000000000000000004600000fe00000000000000000000000360000001fff80000000000000000000260000001fc00000000000000000000010000000003f8000000000000000000006000000000000
def t10 : Rows := ⟨0xae260881ec6e18454, 1⟩
def t9 : Rows := ⟨0xc52b8982207b1b86115000304ae260881ec6e18454000be2b8982207b1b861150002f0ae260881ec6e18454000bb2b8982207b1b861150002b8aa260881ec6e18454000ae29c982207b1b861150002b8a5260881ec6e18454000ae290982207b1b861150002b898254881ec6e18454000ae260932207b1b861150002b898248881ec6e18454000ae260882187b1b861150002b898220851ec6e18454000ae260881ec7a1b861150002b8982207b1b8611504d000ae260881ec6e1845410c002b8982207b1b8611503e000ae260881ec6e184540e8002b8982207b1b86115034000ae260881ec6e184540b8002b8982207b1b86115029000ae260881ec6e18454084002b8982207b1b8611501b000ae260881ec6e18454050002b8982207b1b8611500c000ae260881ec6e18454020002b8982207b1b86115005000ae260881ec6e1845400c002b8982207b1b86115002, 30⟩
def t8 : Rows := ⟨0x2b8982207b1b86116c00000ae260881ec6e18459000002b8982207b1b86115c00000ae260881ec6e18455000bb2b8a4260881ec6e150002b8a4260922207b1b854000bb2b898220851ec6e150002b898248882147b1b854000ae260882147b1e86e15000000ae260881ec6e1a054000002b8982207b1b86615000000ae260881ec6e19054000002b8982207b1b863150002f0ae294982207b18454000ae2949824c881ec61150002b89824c882187b18454000002b8982207b1c86115000000ae260881ec7018454000002b8982207b1bc61150002f8ae29c982206e18454000ae29c98254881b861150002b8a7260882146e18454000ae26088218851b86115000000ae260881f86e18454000002b8982207d1b86115000000ae260881f06e18454000c12b8aa2607b1b86115000304ae260931ec6e18454000ae2609524c7b1b861150002b89824c921ec6e18454000002b8982307b1b86115000000ae2608a1ec6e18454000002b8982247b1b861150002b8aa29c881ec6e18454000ae29ca52207b1b861150002b8a5290881ec6e18454000002b89c2207b1b86115000000ae268881ec6e18454000002b8992207b1b86115000314c1260881ec6e18454000c12f8982207b1b861150002f8bc260881ec6e18454000c12ec982207b1b861150002f0bb260881ec6e18454000002d4982207b1b86115000000b3260881ec6e18454000002c4982207b1b86115000000b0260881ec6e18454000c92b8982207b1b86115000320ae260881ec6e18454000c72b8982207b1b86115000318ae260881ec6e18454000c42b8982207b1b8611500030cae260881ec6e18454000c22b8982207b1b86115000300ae260881ec6e18454000bf2b8982207b1b861150002f4ae260881ec6e18454000ba2b8982207b1b861150002e4ae260881ec6e18454000b82b8982207b1b861150002dcae260881ec6e18454000b52b8982207b1b861150002ccae260881ec6e18454000b12b8982207b1b861150002c0ae260881ec6e18454000ae2b4982207b1b861150002b8ac260881ec6e18454000ae2ac982207b1b861150002b8a9260881ec6e18454000ae2a0982207b1b861150bb2b8a7260881ec6e18454000ae298982207b1b861150002b8a3260881ec6e18454000ae288982207b1b861150002b8a1260881ec6e18454000ae280982207b1b861150002b89f260881ec6e18454000ae278982207b1b861150002b89c260881ec6e18454000ae268982207b1b861150002b899260881ec6e18454000ae260972207b1b861150002b898258881ec6e18454000ae260942207b1b861150bb2b89824c881ec6e18454000ae260912207b1b861150002b898240881ec6e18454000ae2608f2207b1b861150002b898238881ec6e18454000ae2608d2207b1b861150002b898230881ec6e18454000ae2608a2207b1b861150002b898224881ec6e18454000ae2608821c7b1b861150c12b898220851ec6e18454000ae260882107b1b861150002b898220831ec6e18454000ae260882087b1b861150002b898220811ec6e18454000ae260882007b1b861150002b8982207e1ec6e18454000ae260881f47b1b861150002b8982207c1ec6e18454000ae260881ec791b861150002b8982207b1e06e18454000ae260881ec771b861150002b8982207b1d86e18454000ae260881ec751b861150002b8982207b1d06e18454000ae260881ec721b861150002b8982207b1c06e18454000ae260881ec6f1b861150002b8982207b1b86d18454000ae260881ec6e1b061150002b8982207b1b86b18454000ae260881ec6e1a861150002b8982207b1b86818454000ae260881ec6e19861150002b8982207b1b86418454000ae260881ec6e18c61150002b8982207b1b86118054000ae260881ec6e1845f150002b8982207b1b86116c54000ae260881ec6e18459150002b8982207b1b86115c54000ae260881ec6e18455150002b8982207b1b86115053000ae260881ec6e18454148002b8982207b1b86115051000ae260881ec6e1845413c002b8982207b1b8611504e000ae260881ec6e18454134002b8982207b1b8611504c000ae260881ec6e1845412c002b8982207b1b8611504a000ae260881ec6e18454120002b8982207b1b86115047000ae260881ec6e18454114002b8982207b1b86115044000ae260881ec6e1845410c002b8982207b1b86115042000ae260881ec6e18454100002b8982207b1b8611503f000ae260881ec6e184540f8002b8982207b1b8611503d000ae260881ec6e184540f0002b8982207b1b8611503b000ae260881ec6e184540e8002b8982207b1b86115039000ae260881ec6e184540dc002b8982207b1b86115036000ae260881ec6e184540d4002b8982207b1b86115034000ae260881ec6e184540cc002b8982207b1b86115031000ae260881ec6e184540c0002b8982207b1b8611502f000ae260881ec6e184540b8002b8982207b1b8611502d000ae260881ec6e184540ac002b8982207b1b8611502a000ae260881ec6e184540a4002b8982207b1b86115028000ae260881ec6e18454098002b8982207b1b86115025000ae260881ec6e1845408c002b8982207b1b86115022000ae260881ec6e18454084002b8982207b1b86115020000ae260881ec6e18454078002b8982207b1b8611501d000ae260881ec6e18454070002b8982207b1b8611501b000ae260881ec6e18454064002b8982207b1b86115018000ae260881ec6e18454058002b8982207b1b86115015000ae260881ec6e1845505000304ae2207b1b8611500e000002b8881ec6e18454038002b8982207b1b8611500e000ae260881ec6e1a054030002b8982207b1c8611500c000ae260881f86e18454030002b8982307b1b8611500c000ae29c881ec6e18454030002ec982207b1b8611500c2b898220851ec6e1845403000000ae2607b1b86115009000ae29c981ec6e18454024002b8982207b1b86115009000ae260881ec6e1845b020002b8982207b1b86615008000ae260881ec7018454020002b8982207d1b86115008000ae260931ec6e18454020002d4982207b1b86115008000ae2207b1b8611500c02000000ae260881b86115006000ae260932206e18454018002b8982207b1b86115006000ae260881ec6e18459014002b8982207b1b86415005000ae260881ec6f18454014002b898220851b86115005000c12b8981ec6e18454014002b89c2207b1b86115005000b3260881ec6e18454014bb2b8982207b1b86115005000ae2607b1b8611500801400000ae260881ec6115004000ae260882147b18454010002b8982207b1b86115004000ae260881ec6e1845700c002b8982207b1b86315003000ae29c982206e1845400c002b8982287b1b86115003000ae268881ec6e1845400c002c4982207b1b86115003000ae260881b8611500500c002ecae260881ec6e15002000ae260932207b18454008002b8982207c1b86115002000ae260891ec6e18454008002b8992207b1b86115002000b0260881ec6e18454008c12b8982207b1b86115002000ae260881ec6115003008002b8982207b1b86115001, 230⟩
def t7 : Rows := ⟨0x2b8982207b1b86117800000ae260881ec6e1845d000002b8982207b1b86117000000ae260881ec6e1985b000002b8982207b1c06116c00000ae260881f46e1845b000002d4982207b1b86116c00000ae260881ec6e1845b000002b8982207b1b86116800000ae260881ec6e19059000002b8982207b1bc6116400000ae260882146e1845900000304ae2607b1b86116400000ae270881ec6e18459000002cc982207b1b86116400000ae260881ec6e18458000002b8982207b1b86315c00000ae2608a1ec6e18457000002b89a2207b1b86115c00000b1260881ec6e18457000002b8982207b1b86115c00000ae260881ec6e18456000002b8982207b1b861154002ecae29c98220851b854000002ecae260881f06e15000000bb2b8992207b1b854000c12ec98220851ec6e15000000ae260881ec6e1a454000002b8982207b1c86815000000ae260881f86e1a054000002b8982307b1b86815000000ae260881ec6e1a054000002b8982207b1b86715000000ae260881ec7019854000002b8982207d1b86615000000ae260931ec6e19854000002d4982207b1b86615000000ae260881ec6e19854000002b8982207b1b86515000000ae260881ec6f19054000002b89c2207b1b86415000000b3260881ec6e19054000002b8982207b1b86415000000ae29c982206e18c54000002b8982287b1b86315000000ae268881ec6e18c54000002c4982207b1b86315000000ae260881ec6e18c54000002b8982207b1b86215000000ae260932207c18454000002b89924c881ec6115000000ae260881ec7318454000002b8982207e1c86115000000ae2608c1ec7218454000002b8a72207b1c86115000000bb260881ec7218454000002b8982207b1c86115000000ae260881ec7118454000002b8982207d1c06115000000b5260881ec7018454000002b8982207b1c06115000000ae260882146f1845400000304ae2607b1bc6115000000ae270881ec6f18454000002cc982207b1bc61150002ecae260881ec6f18454000002b8982207b1bc6115000000ae29c982286e18454000002c4a7260881b86115000000ae270882146e18454000002b8982207f1b86115000000ae2608c1f86e18454000002b8982207e1b86115000000ae260931f46e18454000002d4982207d1b86115000000ae260881f46e18454000002b8982247c1b86115000000ae264881f06e18454000002c0982207c1b86115000304ae260881f06e18454000002b8982207c1b86115000000c12b89c1ec6e18454000c12ec9824c7b1b86115000000b5260931ec6e18454000002b8a72307b1b86115000000bb2608c1ec6e18454000002b8982307b1b86115000000ae2608b1ec6e18454000002b89a2287b1b86115000000b12608a1ec6e18454000002b8982287b1b86115000000ae264891ec6e18454000002c0982247b1b86115000000ae260891ec6e18454000002b89d2207b1b86115000000b3270881ec6e18454000bb2b89c2207b1b86115000000ae270881ec6e18454000002b89b2207b1b86115000000b1268881ec6e18454000002b89a2207b1b86115000000b0264881ec6e18454000002b8992207b1b86115000000b6260881ec6e18454000002d4982207b1b86115000000b4260881ec6e18454000002cc982207b1b86115000000b2260881ec6e18454000002c4982207b1b86115000000b0260881ec6e18454000002bc982207b1b86115000000ae260881ec6e18454000ae2608c2147b1b86115000000ae2607b1b86115050000002b8981ec6e1845412400000ae260881ec6115046000002b8982207b1845410400000ae2607b1b86115038000002b8982206e184540c800000ae260881b8611502c000002b8881ec6e1845409c00000ae260881b86115024000002b8881ec6e1845407c00000ae2207b1b8611501a000002b8982207b1845405c00000ae2207b1b8611780e000002b8881ec6e1a45403800000ae2207b1cc611500e000002b8881fc6e1845403800000ae24c7b1b8611500e000002b88c1ec6e1845403800000bb2207b1b8611500e000002d4881ec6e1845403800000ae2207b1b8611500e000ae220851ec6e18454038002ec98220851ec6e1500c000ae29c882146e1845403000000ae2207d1b8611500c000bb29c881ec6e1845403000000ae2607b1b86117009000002b8981ec6e19c5402400000ae2607b1c46115009000002b8982146e1845402400000ae2607d1b86115009000002b89c1ec6e1845402400000b62607b1b86115009000bb2b8981ec6e1845402400000ae2607b1b86115009000002b87b1b8611500c02400000ae2607b1bc6115008000002b8982206e1845a01800000ae260881b86515006000002b8982206f1845401800000c12b8981b86115006000002b8982286e1845401800000ae274881b86115006000002d0982206e18454018002ecae260881b86115006000002b8982206e1845401800000ae2606e1845402006000bb2b898220851b85401400000ae260881b86315005000c12b8982146e1845401400304bb2607b1b86115005000002d4981ec6e1845401400000ae1ec6e1845403805000002b8982207b1845801000000bb2b8982207b15004000002b8982207b18c5401000000ae29c982206115004000002b8982207c1845401000000ae2608b1ec6115004000002b89b2207b1845401000000b2260881ec6115004000c12b8982207b1845401000000ae260881ec6115004000ae260881ec611500c01000000ae260881845401404000002b89c2206e1845400c00000ae2606e1845402403000bb2b89824c881ec5400800304bb260881ec6e15002000c12b89824c7b1845400800000ae2608a1ec6115002000ae2207b1b8611500e00800000ae260881845401802, 186⟩
def t6 : Rows := ⟨0x2b8881ec6e1a45e00000000ae2207f1b86117800000002d4881ec6e1845e00000000ae2607b1b86717000000002d8981ec6e1845c00000000ae260881b86516800000002d0982206e1845a00000000ae260881ec6316000000002b89822c7b1845800000000b2260881ec6116000000bb2b89824c881f054000002ecae260882146f15000000bb2b89c220851b85400000304bb260881f06e15000000bb2608c2147b1b85400000000ae2207b1cc6915000000002b8981ec7119c5400000000ae260881bc6515000000002b89d2206e1945400000000ae270881b86315000000c12b89824c7c1845400000000ae2608b1f06115000000002b89b22c7b1845400000000b226c881ec6115000000002b8881fc731845400000000ae2607d1c46115000000002d8981ec711845400000304ae260851bc6115000000c12ec981ec6f1845400000000b52607b1bc6115000000002b89d2286e1845400000000b4274881b86115000000c12b89c2146e18454000002b8a7230851b86115000000002b88c1fc6e1845400000304bb2707b1b86115000000002d89c1ec6e18454000002eca72307b1b86115000000002b87b1b86115011000002b8881ec6e1845403c00000bb220851ec6e1500e00000000ae1ec6f1845403800000ae2207c1b8611500e000002ec931ec6e1845403800000ae260881ec611500d000002eca7220851b85403000000002b8981b8611500a000002ecae260851b85402400000002b8981b86315009000002b8851b8611500c02400000bb1ec6e184540300900000000ae260881845401c00000c12ec981b8611500600000000b52606e1845401800000002b86e184540380600000304bb260851b85401400000ae2146e1845403805000002ec7b1b8611500e01400000bb2b8a7260881500400000304bb260881ec5401000000002b89c2206115004000002b8982307b1845401000000ae2207b1845403804000002ec982207b1500c01000000ae29c88184540300400000000ae260611500901000000bb2b898220540140400000304ae260611500501000000c12ec9824c7b15002000002ec881ec6e1500e00800000ae24c7b1845403802000002ecae260881500600800000c12b8981845401802, 73⟩
def t5 : Rows := ⟨0x304bb260931f05400000000c12ec982146f1500000000304bb270851b85400000000bb29c8c2146e1500000000000ae1b8611501200000000ae2146e1845404400000002ec7b1b8611501100000000ae2207b1845404000000002ec881ec6e1500f00000000ae24c7b1845403c00000002ec881f06e1500e00000000ae24c7c1845403800000002b8851bc611500e00000000bb1ec6f1845403800000002ec982207b1500d00000000ae29c88184540340000000000ae260611500b00000000bb2146e1500c02400000002ecae260881500700000000c12b8981845401c00000002ec6e184540380600000000bb2146e1500e01400000002ecae270881500400000000bb2608c1ec540100000000304ae270611500400000000ae29c8c1845401000000002ec881ec540380400000000bb29c881500c01000000002ecae260540240400000000ae18454030090100000000304bb260540140400000000ae184540380501000000002ec931ec540380200000000c12ec981500600800000002b8611500e01802, 35⟩
def t4 : Rows := ⟨0xbb1b8611501200000000002ec851b8540440000000000bb2207b1501000000000002ec931ec5403c0000000000bb24c7c1500e00000000002ec851bc540380000000000bb29c881500d00000000002ecae2605402c0000000000ae184540300b00000000002b8611500d0240000000000c12ec981500700000000002b8611500e01c0000000000ae1845403c0600000000002b861150100140000000000c12ec9c1500400000000002eca7230540100000000000ae184540440400000000002ec54030090100000000000bb1500e0140400000000002b861150120080000000000bb1500e01802, 21⟩
def t3 : Rows := ⟨0xae1845404c0000000000002ec540300b0000000000000bb1500d0240000000000002ec54038070000000000000bb1500f0180000000000002ec54040050000000000000bb150110100000000000002ec5404802, 8⟩
def t2 : Rows := ⟨0xbb15013, 1⟩
def t1 : Rows := ⟨0x0, 0⟩
def t0 : Rows := ⟨0x0, 0⟩
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z1 : ∀ i < t1.num, bound 1 (t1.get dict i) := by intro i hi; change i < 0 at hi; omega
def ok2 (i : Nat) := flag oracle dict t1 1 (t2.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b2_0 : span ok2 0 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z2 : ∀ i < t2.num, bound 2 (t2.get dict i) := by
  apply allRows (hn := z1) (code := oracle)
  intro i hi
  change i < 1 at hi
  change ok2 i = true
  exact (span_ok b2_0 i (by omega) (by omega))
def ok3 (i : Nat) := flag oracle dict t2 2 (t3.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b3_0 : span ok3 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b3_4 : span ok3 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z3 : ∀ i < t3.num, bound 3 (t3.get dict i) := by
  apply allRows (hn := z2) (code := oracle)
  intro i hi
  change i < 8 at hi
  change ok3 i = true
  exact (if h : i < 4 then (span_ok b3_0 i (by omega) (by omega)) else (span_ok b3_4 i (by omega) (by omega)))
def ok4 (i : Nat) := flag oracle dict t3 3 (t4.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_0 : span ok4 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_4 : span ok4 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_8 : span ok4 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_12 : span ok4 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_16 : span ok4 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b4_20 : span ok4 20 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z4 : ∀ i < t4.num, bound 4 (t4.get dict i) := by
  apply allRows (hn := z3) (code := oracle)
  intro i hi
  change i < 21 at hi
  change ok4 i = true
  exact (if h : i < 12 then (if h : i < 4 then (span_ok b4_0 i (by omega) (by omega)) else (if h : i < 8 then (span_ok b4_4 i (by omega) (by omega)) else (span_ok b4_8 i (by omega) (by omega)))) else (if h : i < 16 then (span_ok b4_12 i (by omega) (by omega)) else (if h : i < 20 then (span_ok b4_16 i (by omega) (by omega)) else (span_ok b4_20 i (by omega) (by omega)))))
def ok5 (i : Nat) := flag oracle dict t4 4 (t5.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_0 : span ok5 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_4 : span ok5 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_8 : span ok5 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_12 : span ok5 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_16 : span ok5 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_20 : span ok5 20 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_24 : span ok5 24 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_28 : span ok5 28 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b5_32 : span ok5 32 3 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z5 : ∀ i < t5.num, bound 5 (t5.get dict i) := by
  apply allRows (hn := z4) (code := oracle)
  intro i hi
  change i < 35 at hi
  change ok5 i = true
  exact (if h : i < 16 then (if h : i < 8 then (if h : i < 4 then (span_ok b5_0 i (by omega) (by omega)) else (span_ok b5_4 i (by omega) (by omega))) else (if h : i < 12 then (span_ok b5_8 i (by omega) (by omega)) else (span_ok b5_12 i (by omega) (by omega)))) else (if h : i < 24 then (if h : i < 20 then (span_ok b5_16 i (by omega) (by omega)) else (span_ok b5_20 i (by omega) (by omega))) else (if h : i < 28 then (span_ok b5_24 i (by omega) (by omega)) else (if h : i < 32 then (span_ok b5_28 i (by omega) (by omega)) else (span_ok b5_32 i (by omega) (by omega))))))
def ok6 (i : Nat) := flag oracle dict t5 5 (t6.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_0 : span ok6 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_4 : span ok6 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_8 : span ok6 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_12 : span ok6 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_16 : span ok6 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_20 : span ok6 20 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_24 : span ok6 24 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_28 : span ok6 28 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_32 : span ok6 32 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_36 : span ok6 36 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_40 : span ok6 40 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_44 : span ok6 44 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_48 : span ok6 48 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_52 : span ok6 52 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_56 : span ok6 56 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_60 : span ok6 60 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_64 : span ok6 64 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_68 : span ok6 68 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b6_72 : span ok6 72 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z6 : ∀ i < t6.num, bound 6 (t6.get dict i) := by
  apply allRows (hn := z5) (code := oracle)
  intro i hi
  change i < 73 at hi
  change ok6 i = true
  exact (if h : i < 36 then (if h : i < 16 then (if h : i < 8 then (if h : i < 4 then (span_ok b6_0 i (by omega) (by omega)) else (span_ok b6_4 i (by omega) (by omega))) else (if h : i < 12 then (span_ok b6_8 i (by omega) (by omega)) else (span_ok b6_12 i (by omega) (by omega)))) else (if h : i < 24 then (if h : i < 20 then (span_ok b6_16 i (by omega) (by omega)) else (span_ok b6_20 i (by omega) (by omega))) else (if h : i < 28 then (span_ok b6_24 i (by omega) (by omega)) else (if h : i < 32 then (span_ok b6_28 i (by omega) (by omega)) else (span_ok b6_32 i (by omega) (by omega)))))) else (if h : i < 56 then (if h : i < 44 then (if h : i < 40 then (span_ok b6_36 i (by omega) (by omega)) else (span_ok b6_40 i (by omega) (by omega))) else (if h : i < 48 then (span_ok b6_44 i (by omega) (by omega)) else (if h : i < 52 then (span_ok b6_48 i (by omega) (by omega)) else (span_ok b6_52 i (by omega) (by omega))))) else (if h : i < 64 then (if h : i < 60 then (span_ok b6_56 i (by omega) (by omega)) else (span_ok b6_60 i (by omega) (by omega))) else (if h : i < 68 then (span_ok b6_64 i (by omega) (by omega)) else (if h : i < 72 then (span_ok b6_68 i (by omega) (by omega)) else (span_ok b6_72 i (by omega) (by omega)))))))
def ok7 (i : Nat) := flag oracle dict t6 6 (t7.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_0 : span ok7 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_4 : span ok7 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_8 : span ok7 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_12 : span ok7 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_16 : span ok7 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_20 : span ok7 20 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_24 : span ok7 24 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_28 : span ok7 28 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_32 : span ok7 32 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_36 : span ok7 36 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_40 : span ok7 40 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_44 : span ok7 44 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_48 : span ok7 48 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_52 : span ok7 52 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_56 : span ok7 56 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_60 : span ok7 60 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_64 : span ok7 64 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_68 : span ok7 68 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_72 : span ok7 72 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_76 : span ok7 76 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_80 : span ok7 80 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_84 : span ok7 84 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_88 : span ok7 88 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_92 : span ok7 92 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_96 : span ok7 96 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_100 : span ok7 100 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_104 : span ok7 104 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_108 : span ok7 108 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_112 : span ok7 112 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_116 : span ok7 116 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_120 : span ok7 120 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_124 : span ok7 124 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_128 : span ok7 128 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_132 : span ok7 132 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_136 : span ok7 136 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_140 : span ok7 140 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_144 : span ok7 144 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_148 : span ok7 148 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_152 : span ok7 152 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_156 : span ok7 156 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_160 : span ok7 160 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_164 : span ok7 164 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_168 : span ok7 168 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_172 : span ok7 172 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_176 : span ok7 176 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_180 : span ok7 180 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b7_184 : span ok7 184 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z7 : ∀ i < t7.num, bound 7 (t7.get dict i) := by
  apply allRows (hn := z6) (code := oracle)
  intro i hi
  change i < 186 at hi
  change ok7 i = true
  exact (if h : i < 92 then (if h : i < 44 then (if h : i < 20 then (if h : i < 8 then (if h : i < 4 then (span_ok b7_0 i (by omega) (by omega)) else (span_ok b7_4 i (by omega) (by omega))) else (if h : i < 12 then (span_ok b7_8 i (by omega) (by omega)) else (if h : i < 16 then (span_ok b7_12 i (by omega) (by omega)) else (span_ok b7_16 i (by omega) (by omega))))) else (if h : i < 32 then (if h : i < 24 then (span_ok b7_20 i (by omega) (by omega)) else (if h : i < 28 then (span_ok b7_24 i (by omega) (by omega)) else (span_ok b7_28 i (by omega) (by omega)))) else (if h : i < 36 then (span_ok b7_32 i (by omega) (by omega)) else (if h : i < 40 then (span_ok b7_36 i (by omega) (by omega)) else (span_ok b7_40 i (by omega) (by omega)))))) else (if h : i < 68 then (if h : i < 56 then (if h : i < 48 then (span_ok b7_44 i (by omega) (by omega)) else (if h : i < 52 then (span_ok b7_48 i (by omega) (by omega)) else (span_ok b7_52 i (by omega) (by omega)))) else (if h : i < 60 then (span_ok b7_56 i (by omega) (by omega)) else (if h : i < 64 then (span_ok b7_60 i (by omega) (by omega)) else (span_ok b7_64 i (by omega) (by omega))))) else (if h : i < 80 then (if h : i < 72 then (span_ok b7_68 i (by omega) (by omega)) else (if h : i < 76 then (span_ok b7_72 i (by omega) (by omega)) else (span_ok b7_76 i (by omega) (by omega)))) else (if h : i < 84 then (span_ok b7_80 i (by omega) (by omega)) else (if h : i < 88 then (span_ok b7_84 i (by omega) (by omega)) else (span_ok b7_88 i (by omega) (by omega))))))) else (if h : i < 140 then (if h : i < 116 then (if h : i < 104 then (if h : i < 96 then (span_ok b7_92 i (by omega) (by omega)) else (if h : i < 100 then (span_ok b7_96 i (by omega) (by omega)) else (span_ok b7_100 i (by omega) (by omega)))) else (if h : i < 108 then (span_ok b7_104 i (by omega) (by omega)) else (if h : i < 112 then (span_ok b7_108 i (by omega) (by omega)) else (span_ok b7_112 i (by omega) (by omega))))) else (if h : i < 128 then (if h : i < 120 then (span_ok b7_116 i (by omega) (by omega)) else (if h : i < 124 then (span_ok b7_120 i (by omega) (by omega)) else (span_ok b7_124 i (by omega) (by omega)))) else (if h : i < 132 then (span_ok b7_128 i (by omega) (by omega)) else (if h : i < 136 then (span_ok b7_132 i (by omega) (by omega)) else (span_ok b7_136 i (by omega) (by omega)))))) else (if h : i < 164 then (if h : i < 152 then (if h : i < 144 then (span_ok b7_140 i (by omega) (by omega)) else (if h : i < 148 then (span_ok b7_144 i (by omega) (by omega)) else (span_ok b7_148 i (by omega) (by omega)))) else (if h : i < 156 then (span_ok b7_152 i (by omega) (by omega)) else (if h : i < 160 then (span_ok b7_156 i (by omega) (by omega)) else (span_ok b7_160 i (by omega) (by omega))))) else (if h : i < 176 then (if h : i < 168 then (span_ok b7_164 i (by omega) (by omega)) else (if h : i < 172 then (span_ok b7_168 i (by omega) (by omega)) else (span_ok b7_172 i (by omega) (by omega)))) else (if h : i < 180 then (span_ok b7_176 i (by omega) (by omega)) else (if h : i < 184 then (span_ok b7_180 i (by omega) (by omega)) else (span_ok b7_184 i (by omega) (by omega))))))))
def ok8 (i : Nat) := flag oracle dict t7 7 (t8.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_0 : span ok8 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_4 : span ok8 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_8 : span ok8 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_12 : span ok8 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_16 : span ok8 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_20 : span ok8 20 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_24 : span ok8 24 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_28 : span ok8 28 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_32 : span ok8 32 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_36 : span ok8 36 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_40 : span ok8 40 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_44 : span ok8 44 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_48 : span ok8 48 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_52 : span ok8 52 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_56 : span ok8 56 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_60 : span ok8 60 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_64 : span ok8 64 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_68 : span ok8 68 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_72 : span ok8 72 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_76 : span ok8 76 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_80 : span ok8 80 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_84 : span ok8 84 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_88 : span ok8 88 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_92 : span ok8 92 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_96 : span ok8 96 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_100 : span ok8 100 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_104 : span ok8 104 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_108 : span ok8 108 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_112 : span ok8 112 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_116 : span ok8 116 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_120 : span ok8 120 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_124 : span ok8 124 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_128 : span ok8 128 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_132 : span ok8 132 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_136 : span ok8 136 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_140 : span ok8 140 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_144 : span ok8 144 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_148 : span ok8 148 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_152 : span ok8 152 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_156 : span ok8 156 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_160 : span ok8 160 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_164 : span ok8 164 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_168 : span ok8 168 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_172 : span ok8 172 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_176 : span ok8 176 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_180 : span ok8 180 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_184 : span ok8 184 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_188 : span ok8 188 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_192 : span ok8 192 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_196 : span ok8 196 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_200 : span ok8 200 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_204 : span ok8 204 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_208 : span ok8 208 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_212 : span ok8 212 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_216 : span ok8 216 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_220 : span ok8 220 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_224 : span ok8 224 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b8_228 : span ok8 228 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z8 : ∀ i < t8.num, bound 8 (t8.get dict i) := by
  apply allRows (hn := z7) (code := oracle)
  intro i hi
  change i < 230 at hi
  change ok8 i = true
  exact (if h : i < 116 then (if h : i < 56 then (if h : i < 28 then (if h : i < 12 then (if h : i < 4 then (span_ok b8_0 i (by omega) (by omega)) else (if h : i < 8 then (span_ok b8_4 i (by omega) (by omega)) else (span_ok b8_8 i (by omega) (by omega)))) else (if h : i < 20 then (if h : i < 16 then (span_ok b8_12 i (by omega) (by omega)) else (span_ok b8_16 i (by omega) (by omega))) else (if h : i < 24 then (span_ok b8_20 i (by omega) (by omega)) else (span_ok b8_24 i (by omega) (by omega))))) else (if h : i < 40 then (if h : i < 32 then (span_ok b8_28 i (by omega) (by omega)) else (if h : i < 36 then (span_ok b8_32 i (by omega) (by omega)) else (span_ok b8_36 i (by omega) (by omega)))) else (if h : i < 48 then (if h : i < 44 then (span_ok b8_40 i (by omega) (by omega)) else (span_ok b8_44 i (by omega) (by omega))) else (if h : i < 52 then (span_ok b8_48 i (by omega) (by omega)) else (span_ok b8_52 i (by omega) (by omega)))))) else (if h : i < 84 then (if h : i < 68 then (if h : i < 60 then (span_ok b8_56 i (by omega) (by omega)) else (if h : i < 64 then (span_ok b8_60 i (by omega) (by omega)) else (span_ok b8_64 i (by omega) (by omega)))) else (if h : i < 76 then (if h : i < 72 then (span_ok b8_68 i (by omega) (by omega)) else (span_ok b8_72 i (by omega) (by omega))) else (if h : i < 80 then (span_ok b8_76 i (by omega) (by omega)) else (span_ok b8_80 i (by omega) (by omega))))) else (if h : i < 100 then (if h : i < 92 then (if h : i < 88 then (span_ok b8_84 i (by omega) (by omega)) else (span_ok b8_88 i (by omega) (by omega))) else (if h : i < 96 then (span_ok b8_92 i (by omega) (by omega)) else (span_ok b8_96 i (by omega) (by omega)))) else (if h : i < 108 then (if h : i < 104 then (span_ok b8_100 i (by omega) (by omega)) else (span_ok b8_104 i (by omega) (by omega))) else (if h : i < 112 then (span_ok b8_108 i (by omega) (by omega)) else (span_ok b8_112 i (by omega) (by omega))))))) else (if h : i < 172 then (if h : i < 144 then (if h : i < 128 then (if h : i < 120 then (span_ok b8_116 i (by omega) (by omega)) else (if h : i < 124 then (span_ok b8_120 i (by omega) (by omega)) else (span_ok b8_124 i (by omega) (by omega)))) else (if h : i < 136 then (if h : i < 132 then (span_ok b8_128 i (by omega) (by omega)) else (span_ok b8_132 i (by omega) (by omega))) else (if h : i < 140 then (span_ok b8_136 i (by omega) (by omega)) else (span_ok b8_140 i (by omega) (by omega))))) else (if h : i < 156 then (if h : i < 148 then (span_ok b8_144 i (by omega) (by omega)) else (if h : i < 152 then (span_ok b8_148 i (by omega) (by omega)) else (span_ok b8_152 i (by omega) (by omega)))) else (if h : i < 164 then (if h : i < 160 then (span_ok b8_156 i (by omega) (by omega)) else (span_ok b8_160 i (by omega) (by omega))) else (if h : i < 168 then (span_ok b8_164 i (by omega) (by omega)) else (span_ok b8_168 i (by omega) (by omega)))))) else (if h : i < 200 then (if h : i < 184 then (if h : i < 176 then (span_ok b8_172 i (by omega) (by omega)) else (if h : i < 180 then (span_ok b8_176 i (by omega) (by omega)) else (span_ok b8_180 i (by omega) (by omega)))) else (if h : i < 192 then (if h : i < 188 then (span_ok b8_184 i (by omega) (by omega)) else (span_ok b8_188 i (by omega) (by omega))) else (if h : i < 196 then (span_ok b8_192 i (by omega) (by omega)) else (span_ok b8_196 i (by omega) (by omega))))) else (if h : i < 216 then (if h : i < 208 then (if h : i < 204 then (span_ok b8_200 i (by omega) (by omega)) else (span_ok b8_204 i (by omega) (by omega))) else (if h : i < 212 then (span_ok b8_208 i (by omega) (by omega)) else (span_ok b8_212 i (by omega) (by omega)))) else (if h : i < 224 then (if h : i < 220 then (span_ok b8_216 i (by omega) (by omega)) else (span_ok b8_220 i (by omega) (by omega))) else (if h : i < 228 then (span_ok b8_224 i (by omega) (by omega)) else (span_ok b8_228 i (by omega) (by omega))))))))
def ok9 (i : Nat) := flag oracle dict t8 8 (t9.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_0 : span ok9 0 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_4 : span ok9 4 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_8 : span ok9 8 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_12 : span ok9 12 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_16 : span ok9 16 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_20 : span ok9 20 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_24 : span ok9 24 4 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b9_28 : span ok9 28 2 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z9 : ∀ i < t9.num, bound 9 (t9.get dict i) := by
  apply allRows (hn := z8) (code := oracle)
  intro i hi
  change i < 30 at hi
  change ok9 i = true
  exact (if h : i < 16 then (if h : i < 8 then (if h : i < 4 then (span_ok b9_0 i (by omega) (by omega)) else (span_ok b9_4 i (by omega) (by omega))) else (if h : i < 12 then (span_ok b9_8 i (by omega) (by omega)) else (span_ok b9_12 i (by omega) (by omega)))) else (if h : i < 24 then (if h : i < 20 then (span_ok b9_16 i (by omega) (by omega)) else (span_ok b9_20 i (by omega) (by omega))) else (if h : i < 28 then (span_ok b9_24 i (by omega) (by omega)) else (span_ok b9_28 i (by omega) (by omega)))))
def ok10 (i : Nat) := flag oracle dict t9 9 (t10.get dict i)
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem b10_0 : span ok10 0 1 = true := by decide +kernel
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem z10 : ∀ i < t10.num, bound 10 (t10.get dict i) := by
  apply allRows (hn := z9) (code := oracle)
  intro i hi
  change i < 1 at hi
  change ok10 i = true
  exact (span_ok b10_0 i (by omega) (by omega))
end Cut
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem reject (zs : List Sig) (hs : Steps raw zs) (hl : zs.length ≤ 10) (ho : target ∈ raw ++ zs) : False := by
  apply Cut.reject_of_bound _ zs hs hl ho
  intro hv m hm l
  have e : (Cut.t10.get Cut.dict 0).toFinset = raw.toFinset := by decide +kernel
  exact Cut.z10 0 (by decide) (by decide +kernel) m hm (e.symm ▸ l)
end PEqualNP.Outside.L_meta_29925.Check

namespace PEqualNP.Outside.L_meta_29925.C7Projection

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def step (w : List Bool) (g : Gate) : List Bool := w ++ [gateValue w g]
def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

theorem wires_eq_run (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) :
    run (a ++ b) w = run b (run a w) := List.foldl_append ..

@[simp] theorem step_length (w : List Bool) (g : Gate) :
    (step w g).length = w.length + 1 := by simp [step]

@[simp] theorem run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih, step_length, List.length_cons]
    omega

theorem run_preserve (gs : List Gate) (w : List Bool) (k : Nat) (h : k < w.length) :
    (run gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD k false = _
    rw [ih (step w g) (by simp; omega)]
    exact List.getD_append _ _ _ _ h

theorem getD_ofFn {n : Nat} (x : Fin n → Bool) (j : Fin n) :
    (List.ofFn x).getD j.val false = x j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

def Agree (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ k, k ≠ 0 → u.getD k false = v.getD k false

theorem agree_ofFn {n : Nat} {x y : Fin n → Bool}
    (h : ∀ j : Fin n, j.val ≠ 0 → x j = y j) : Agree (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro k hk
  by_cases hb : k < n
  · exact (getD_ofFn x ⟨k, hb⟩).trans ((h ⟨k, hb⟩ hk).trans (getD_ofFn y ⟨k, hb⟩).symm)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem step_agree {u v : List Bool} {g : Gate} (h : Agree u v)
    (he : gateValue u g = gateValue v g) : Agree (step u g) (step v g) := by
  refine ⟨by simp [h.1], ?_⟩
  intro k hk
  by_cases hb : k < u.length
  · exact (List.getD_append _ _ _ _ hb).trans
      ((h.2 k hk).trans (List.getD_append _ _ _ _ (h.1 ▸ hb)).symm)
  · change (u ++ [gateValue u g]).getD k false = (v ++ [gateValue v g]).getD k false
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [← h.1]; omega), h.1, he]

theorem gateValue_congr {u v : List Bool} {g : Gate} (h : Agree u v)
    (hg : 0 ∉ g.inputs) : gateValue u g = gateValue v g := by
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro j hj
  exact h.2 j (fun e => hg (e ▸ hj))

theorem run_agree {gs : List Gate} {u v : List Bool} (h : Agree u v)
    (hs : ∀ g ∈ gs, 0 ∉ g.inputs) : Agree (run gs u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step_agree h (gateValue_congr h (hs g (by simp))))
    exact fun g hg => hs g (by simp [hg])

def UniqueReader (C : Circuit) (i : Fin C.gates.length) : Prop :=
  ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i

theorem no_read_take {C : Circuit} {i : Fin C.gates.length} (h : UniqueReader C i) :
    ∀ g ∈ C.gates.take i.val, 0 ∉ g.inputs := by
  intro g hg hg0
  obtain ⟨j, hj, hget⟩ := List.mem_take_iff_getElem.mp hg
  have hj' : j < C.gates.length := by simp at hj; omega
  have hji : j < i.val := by simp at hj; omega
  have hh : C.gates.get ⟨j, hj'⟩ = g := by simpa using hget
  have := congrArg Fin.val (h ⟨j, hj'⟩ (hh.symm ▸ hg0))
  simp at this
  omega

theorem no_read_drop {C : Circuit} {i : Fin C.gates.length} (h : UniqueReader C i) :
    ∀ g ∈ C.gates.drop (i.val + 1), 0 ∉ g.inputs := by
  intro g hg hg0
  obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hg
  have hj' : i.val + 1 + j < C.gates.length := by simp at hj; omega
  have hh : C.gates.get ⟨i.val + 1 + j, hj'⟩ = g := by simpa using hget
  have := congrArg Fin.val (h ⟨_, hj'⟩ (hh.symm ▸ hg0))
  simp at this
  omega

theorem cut_wires (C : Circuit) (i : Fin C.gates.length) (u : List Bool) :
    C.wires u =
      run (C.gates.drop (i.val + 1)) (step (run (C.gates.take i.val) u) (C.gates.get i)) := by
  rw [wires_eq_run]
  change run C.gates u = run ((C.gates.get i) :: C.gates.drop (i.val + 1)) (run (C.gates.take i.val) u)
  rw [← run_append]
  have h := (List.take_append_drop i.val C.gates).symm
  rw [List.drop_eq_getElem_cons i.isLt] at h
  exact congrArg (fun gs => run gs u) h

def wire (C : Circuit) (k : Nat) {n : Nat} (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD k false

theorem cut_value (C : Circuit) (i : Fin C.gates.length) {n : Nat} (x : Fin n → Bool) :
    wire C (n + i.val) x =
      gateValue (run (C.gates.take i.val) (List.ofFn x)) (C.gates.get i) := by
  let u := run (C.gates.take i.val) (List.ofFn x)
  have hu : u.length = n + i.val := by
    simp [u, List.length_take]
  unfold wire
  rw [cut_wires C i]
  rw [run_preserve _ _ _ (by change _ < (step u _).length; simp [hu])]
  change (u ++ [gateValue u (C.gates.get i)]).getD (n + i.val) false = _
  rw [← hu, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp [u]

theorem wires_agree_of_cut_value {C : Circuit} (i : Fin C.gates.length)
    (hi : UniqueReader C i) {n : Nat} {x y : Fin n → Bool}
    (hxy : ∀ j : Fin n, j.val ≠ 0 → x j = y j)
    (hc : wire C (n + i.val) x = wire C (n + i.val) y) :
    Agree (C.wires (List.ofFn x)) (C.wires (List.ofFn y)) := by
  have hp := run_agree (agree_ofFn hxy) (no_read_take hi)
  have hv := step_agree hp (by simpa only [cut_value] using hc)
  simpa only [cut_wires C i] using run_agree hv (no_read_drop hi)

theorem eval_eq_of_cut_value {C : Circuit} (i : Fin C.gates.length)
    (hi : UniqueReader C i) (ho : C.output ≠ 0) {n : Nat} {x y : Fin n → Bool}
    (hxy : ∀ j : Fin n, j.val ≠ 0 → x j = y j)
    (hc : wire C (n + i.val) x = wire C (n + i.val) y) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) :=
  (wires_agree_of_cut_value i hi hxy hc).2 _ ho

theorem or_value_eq {g : Gate} {u : List Bool} {w : Nat}
    (hop : g.op = .or) (hl : g.inputs.length ≤ 2)
    (h0 : 0 ∈ g.inputs) (hw : w ∈ g.inputs) (hne : w ≠ 0) :
    gateValue u g = (u.getD 0 false || u.getD w false) := by
  unfold gateValue
  rw [hop]
  cases h : g.inputs with
  | nil => simp [h] at h0
  | cons a t =>
    cases t with
    | nil =>
      simp [h] at h0 hw
      exact (hne (hw.trans h0.symm)).elim
    | cons b t =>
      have : t = [] := by simpa [h] using hl
      subst t
      simp only [h, List.mem_cons, List.not_mem_nil, or_false] at h0 hw
      rcases h0 with rfl | rfl <;> rcases hw with hw | hw
      · exact (hne hw).elim
      · subst w
        simp [GateOp.eval]
      · subst w
        simp [GateOp.eval, Bool.or_comm]
      · exact (hne hw).elim

theorem unique_or_eq {C : Circuit} (i : Fin C.gates.length) {n : Nat} (hn : 0 < n)
    (hop : (C.gates.get i).op = .or) (hl : (C.gates.get i).inputs.length ≤ 2)
    {w : Nat} (h0 : 0 ∈ (C.gates.get i).inputs) (hw : w ∈ (C.gates.get i).inputs)
    (hne : w ≠ 0) (hwb : w < n + i.val) (x : Fin n → Bool) :
    wire C (n + i.val) x = (x ⟨0, hn⟩ || wire C w x) := by
  let u := run (C.gates.take i.val) (List.ofFn x)
  have hu : u.length = n + i.val := by
    simp [u, List.length_take]
  have hleft : u.getD 0 false = x ⟨0, hn⟩ := by
    exact (run_preserve _ _ _ (by simpa)).trans (getD_ofFn x ⟨0, hn⟩)
  have hright : wire C w x = u.getD w false := by
    unfold wire
    rw [cut_wires C i]
    rw [run_preserve _ _ _ (by change w < (step u _).length; simp [hu]; omega)]
    exact List.getD_append _ _ _ _ (hu.symm ▸ hwb)
  rw [cut_value, or_value_eq hop hl h0 hw hne, hright]
  exact congrArg (· || u.getD w false) hleft

theorem wire_eq_of_before_reader {C : Circuit} (i : Fin C.gates.length)
    (hu : UniqueReader C i) {n : Nat} {x y : Fin n → Bool}
    (hxy : ∀ j : Fin n, j.val ≠ 0 → x j = y j)
    {w : Nat} (hne : w ≠ 0) (hwb : w < n + i.val) :
    wire C w x = wire C w y := by
  have get (a : Fin n → Bool) :
      wire C w a = (run (C.gates.take i.val) (List.ofFn a)).getD w false := by
    have hw : w < (run (C.gates.take i.val) (List.ofFn a)).length := by
      simpa [List.length_take] using hwb
    unfold wire
    rw [cut_wires C i, run_preserve _ _ _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hw
  rw [get x, get y]
  exact (run_agree (agree_ofFn hxy) (no_read_take hu)).2 _ hne

theorem reader_stable_of_true {C : Circuit} (i : Fin C.gates.length)
    {n : Nat} (hn : 0 < n) (hF : FanInTwo C) (hu : UniqueReader C i)
    (hop : (C.gates.get i).op = .or) (h0 : 0 ∈ (C.gates.get i).inputs)
    {w : Nat} (hw : w ∈ (C.gates.get i).inputs) (hne : w ≠ 0) (hwb : w < n + i.val)
    {x y : Fin n → Bool} (hxy : ∀ j : Fin n, j.val ≠ 0 → x j = y j)
    (ht : wire C w x = true) : ∀ k : Nat, k ≠ 0 → wire C k x = wire C k y := by
  have ht' := (wire_eq_of_before_reader i hu hxy hne hwb).symm.trans ht
  have hlen := (hF (C.gates.get i) (List.get_mem _ _)).2
  have hor := unique_or_eq i hn hop hlen h0 hw hne hwb
  have hcut : wire C (n + i.val) x = wire C (n + i.val) y := by simp [hor, ht, ht']
  exact (wires_agree_of_cut_value i hu hxy hcut).2

def WireLE (u v : List Bool) : Prop :=
  u.length = v.length ∧ ∀ k, u.getD k false ≤ v.getD k false

theorem step_mono {u v : List Bool} {g : Gate} (h : WireLE u v)
    (hg : g.op = .and ∨ g.op = .or) : WireLE (step u g) (step v g) := by
  have he : gateValue u g ≤ gateValue v g := by
    unfold gateValue
    rw [Bool.le_iff_imp]
    rcases hg with hg | hg
    · simp only [hg, GateOp.eval, List.all_eq_true, List.forall_mem_map]
      intro H j hj
      exact Bool.le_iff_imp.mp (h.2 j) (H j hj)
    · simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map]
      intro H
      obtain ⟨z, ⟨j, hj, rfl⟩, hz⟩ := H
      exact ⟨_, ⟨j, hj, rfl⟩, Bool.le_iff_imp.mp (h.2 j) hz⟩
  refine ⟨by simp [h.1], ?_⟩
  intro k
  by_cases hb : k < u.length
  · change (u ++ [_]).getD k false ≤ (v ++ [_]).getD k false
    rw [List.getD_append _ _ _ _ hb, List.getD_append _ _ _ _ (h.1 ▸ hb)]
    exact h.2 k
  · change (u ++ [_]).getD k false ≤ (v ++ [_]).getD k false
    rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by rw [← h.1]; omega), h.1]
    cases k - v.length
    · simpa using he
    · simp

theorem run_mono {gs : List Gate} {u v : List Bool} (h : WireLE u v)
    (hs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) : WireLE (run gs u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step_mono h (hs g (by simp)))
    exact fun g hg => hs g (by simp [hg])

theorem wire_mono {C : Circuit} (hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    {n : Nat} {x y : Fin n → Bool} (h : ∀ j, x j ≤ y j) (k : Nat) :
    wire C k x ≤ wire C k y := by
  have hxy : WireLE (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro j
    by_cases hb : j < n
    · rw [getD_ofFn x ⟨j, hb⟩, getD_ofFn y ⟨j, hb⟩]
      exact h ⟨j, hb⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  exact (run_mono hxy hm).2 k

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def assignment (m : Nat) (j : Fin 7) : Bool := m.testBit j.val

theorem wire_true_at_60 {C : Circuit} {w : Nat}
    (hM : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (ht : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ wire C w x = true) :
    wire C w (assignment 60) = true := by
  obtain ⟨x, hx0, hx1, hx6, hxw⟩ := ht
  have hl (j : Fin 7) : x j ≤ assignment 60 j := by
    fin_cases j <;> simp [assignment, hx0, hx1, hx6]
    all_goals exact Bool.le_true _
  exact Bool.le_iff_imp.mp (wire_mono hM hl w) hxw

theorem reader_stable_60_61 {C : Circuit} (i : Fin C.gates.length)
    (hF : FanInTwo C) (hu : UniqueReader C i) (hop : (C.gates.get i).op = .or)
    (h0 : 0 ∈ (C.gates.get i).inputs) {w : Nat} (hw : w ∈ (C.gates.get i).inputs)
    (hne : w ≠ 0) (hwb : w < 7 + i.val) (ht : wire C w (assignment 60) = true) :
    ∀ k : Nat, k ≠ 0 → wire C k (assignment 60) = wire C k (assignment 61) :=
  reader_stable_of_true i (by decide) hF hu hop h0 hw hne hwb (by decide +kernel) ht

theorem output_ne_zero {C : Circuit}
    (hC : ∀ x, C.eval (List.ofFn x) = target x) : C.output ≠ 0 := by
  intro ho
  have h := hC (assignment 1)
  unfold Circuit.eval at h
  rw [ho, wires_eq_run, run_preserve _ _ _ (by simp)] at h
  change (List.ofFn (assignment 1)).getD (0 : Fin 7).val false = _ at h
  rw [getD_ofFn] at h
  exact (by decide : assignment 1 0 ≠ target (assignment 1)) h

theorem target_eq_of_reader_true {C : Circuit} (i : Fin C.gates.length)
    (hF : FanInTwo C) (hu : UniqueReader C i) (hop : (C.gates.get i).op = .or)
    (h0 : 0 ∈ (C.gates.get i).inputs) {w : Nat} (hw : w ∈ (C.gates.get i).inputs)
    (hne : w ≠ 0) (hwb : w < 7 + i.val)
    (hC : ∀ x, C.eval (List.ofFn x) = target x)
    {x y : Fin 7 → Bool} (hxy : ∀ j : Fin 7, j.val ≠ 0 → x j = y j)
    (ht : wire C w x = true) :
    target x = target y := by
  rw [← hC x, ← hC y]
  exact reader_stable_of_true i (by decide) hF hu hop h0 hw hne hwb hxy ht C.output
    (output_ne_zero hC)

theorem sensitive_cut_false {C : Circuit} (i : Fin C.gates.length)
    (hu : UniqueReader C i) (hC : ∀ x, C.eval (List.ofFn x) = target x)
    {x y : Fin 7 → Bool} (hxy : ∀ j : Fin 7, j.val ≠ 0 → x j = y j)
    (hx : target x = false) (hy : target y = true) (hz : wire C (7 + i.val) y = true) :
    wire C (7 + i.val) x = false := by
  cases he : wire C (7 + i.val) x
  · rfl
  · have heval := eval_eq_of_cut_value i hu (output_ne_zero hC) hxy (he.trans hz.symm)
    rw [hC, hC, hx, hy] at heval
    contradiction

def sensitiveMask (j : Fin 7) : Nat := (![0, 2, 68, 10, 18, 34, 64] : Fin 7 → Nat) j

theorem sensitiveMasks : ∀ j : Fin 7, j.val ≠ 0 →
    (∀ k, assignment (2 ^ j.val) k ≤ assignment (sensitiveMask j) k) ∧
    (∀ k : Fin 7, k.val ≠ 0 →
      assignment (sensitiveMask j) k = assignment (sensitiveMask j + 1) k) ∧
    target (assignment (sensitiveMask j)) = false ∧
    target (assignment (sensitiveMask j + 1)) = true ∧
    assignment (sensitiveMask j + 1) 0 = true := by decide +kernel

theorem reader_signature {C : Circuit} (i : Fin C.gates.length)
    (hF : FanInTwo C) (hM : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (hC : ∀ x, C.eval (List.ofFn x) = target x)
    (hu : UniqueReader C i) (hop : (C.gates.get i).op = .or)
    (h0 : 0 ∈ (C.gates.get i).inputs) {w : Nat} (hw : w ∈ (C.gates.get i).inputs)
    (hne : w ≠ 0) (hwb : w < 7 + i.val)
    (ht : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ wire C w x = true) :
    wire C (7 + i.val) (assignment 1) = true ∧
    wire C (7 + i.val) (assignment 60) = true ∧
    (∀ j : Fin 7, j.val ≠ 0 →
      wire C (7 + i.val) (assignment (2 ^ j.val)) = false) := by
  have hlen := (hF (C.gates.get i) (List.get_mem _ _)).2
  have hor := unique_or_eq i (n := 7) (by decide) hop hlen h0 hw hne hwb
  have high (x : Fin 7 → Bool) (hx : x 0 = true) : wire C (7 + i.val) x = true := by
    rw [hor]
    change (x 0 || wire C w x) = true
    rw [hx]
    rfl
  refine ⟨high _ (by decide), ?_, ?_⟩
  · rw [hor, wire_true_at_60 hM ht]
    exact Bool.or_true _
  · intro j hj
    obtain ⟨hmono, he, hfalse, htrue, hzero⟩ := sensitiveMasks j hj
    have hs := sensitive_cut_false i hu hC he hfalse htrue (high _ hzero)
    have hr := wire_mono hM hmono (7 + i.val)
    rw [hs] at hr
    cases h : wire C (7 + i.val) (assignment (2 ^ j.val))
    · rfl
    · rw [h] at hr
      contradiction

end PEqualNP.Outside.L_meta_29925.C7Projection

namespace PEqualNP.Outside.L_meta_29925.Bridge
open Check C7Projection PEqualNP.CircuitLowerBounds
def row (s : Bool) (j : Fin 64) : Nat :=
  if s then ([3,3,3,3,3,3,3,6,6,6,6,6,6,6,12,12,12,12,12,12,12,24,24,24,24,24,24,24,48,48,48,48,48,48,48,65,65,65,65,65,65,65,96,96,96,96,96,96,96,60,61,3,6,12,24,48,96,65,3,3,3,3,3,3] : List Nat).getD j.val 0 else ([21,37,41,42,74,82,84,21,37,41,42,74,82,84,21,37,41,42,74,82,84,21,37,41,42,74,82,84,21,37,41,42,74,82,84,21,37,41,42,74,82,84,21,37,41,42,74,82,84,0,0,2,4,8,16,32,64,1,2,4,8,16,32,64] : List Nat).getD j.val 0
def tab (f : Fin 64 → Bool) : B :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn
lemma get_tab (f : Fin 64 → Bool) (j : Fin 64) : (tab f).getLsbD j.val = f j := by
  simp only [tab,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def table (f : (Fin 7 → Bool) → Bool) : Sig :=
  (tab fun j => f (assignment (row true j)), tab fun j => f (assignment (row false j)))
def col (C : Circuit) (n : Nat) := table (wire C n)
def env (C : Circuit) (n : Nat) := List.ofFn (fun k : Fin n => col C k.val)
def rd (C : Circuit) (n q : Nat) := if q < n then col C q else zero
def obs (s : Bool) (j : Fin 64) (a : Sig) := (if s then a.1 else a.2).getLsbD j.val
lemma obs_table (s : Bool) (j : Fin 64) (f : (Fin 7 → Bool) → Bool) :
    obs s j (table f) = f (assignment (row s j)) := by cases s <;> exact get_tab _ _
lemma ext_obs {a b : Sig} (h : ∀ s j, obs s j a = obs s j b) : a=b := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact h true ⟨i,hi⟩
  · exact h false ⟨i,hi⟩
lemma obs_zero (s : Bool) (j : Fin 64) : obs s j zero = false := by cases s <;> simp [obs,zero]
lemma obs_one : ∀ (s : Bool) (j : Fin 64), obs s j one = true := by decide +kernel
lemma obs_bb (s : Bool) (j : Fin 64) (t : Bool) (a b : Sig) :
    obs s j (bb t a b) = (if t then obs s j a || obs s j b else obs s j a && obs s j b) := by
  cases s <;> cases t <;> simp [obs,bb]
lemma rd_rep (C : Circuit) (n q : Nat) : represented (env C n) (rd C n q) := by
  unfold rd
  split
  next h => exact Or.inl (List.mem_ofFn.mpr ⟨⟨q,h⟩,rfl⟩)
  next => exact Or.inr (fun h => h.1 rfl)
lemma prefix_eq (C : Circuit) (j : Fin C.gates.length) (x : Fin 7 → Bool) (q : Nat) :
    (run (C.gates.take j.val) (List.ofFn x)).getD q false =
    if q < 7+j.val then wire C q x else false := by
  let v := run (C.gates.take j.val) (List.ofFn x)
  have len : v.length = 7+j.val := by simp [v,List.length_take]
  change v.getD q false = _
  split
  next h =>
    have hq : q < v.length := len ▸ h
    unfold wire
    rw [cut_wires C j]
    change _ = (run _ (step v _)).getD q false
    rw [run_preserve (C.gates.drop (j.val+1)) (step v (C.gates.get j)) q (by simp only [step_length]; omega)]
    exact (List.getD_append _ _ _ _ hq).symm
  next h => exact List.getD_eq_default _ _ (by omega)
lemma obs_rd (C : Circuit) (j : Fin C.gates.length) (s : Bool) (u : Fin 64) (q : Nat) :
    obs s u (rd C (7+j.val) q) =
    (run (C.gates.take j.val) (List.ofFn (assignment (row s u)))).getD q false := by
  rw [prefix_eq,rd]; split
  next => exact obs_table _ _ _
  next => exact obs_zero _ _
def gateFold (r : Nat → Sig) (g : Gate) : Sig := match g.op with
  | .or => (g.inputs.map r).foldr (bb true) zero
  | _ => (g.inputs.map r).foldr (bb false) one
lemma obs_fold (s : Bool) (u : Fin 64) (r : Nat → Sig) (d : Bool) (ns : List Nat) :
    obs s u ((ns.map r).foldr (bb d) (if d then zero else one)) =
    (if d then ns.any (fun i => obs s u (r i)) else ns.all (fun i => obs s u (r i))) := by
  induction ns with
  | nil => cases d <;> simp [obs_zero,obs_one]
  | cons n ns ih => cases d <;> simp_all only [List.map_cons,List.foldr_cons,obs_bb,Bool.false_eq_true,ite_true,ite_false,List.any_cons,List.all_cons]
lemma col_gate (C : Circuit) (j : Fin C.gates.length)
    (hm : (C.gates.get j).op=.and ∨ (C.gates.get j).op=.or) :
    col C (7+j.val) = gateFold (rd C (7+j.val)) (C.gates.get j) := by
  apply ext_obs
  intro s u
  rw [col,obs_table,cut_value]
  rcases hm with hm | hm
  · simp only [gateValue,gateFold,hm,GateOp.eval,List.all_map,Function.comp_def,reduceCtorEq,if_false,id_eq]
    symm
    simpa only [Bool.false_eq_true,ite_false,obs_rd] using obs_fold s u (rd C (7+j.val)) false (C.gates.get j).inputs
  · simp only [gateValue,gateFold,hm,GateOp.eval,List.any_map,Function.comp_def,if_true,id_eq]
    symm
    simpa only [ite_true,obs_rd] using obs_fold s u (rd C (7+j.val)) true (C.gates.get j).inputs
lemma stable_rd {C : Circuit} (hs : ∀ q : Nat, q ≠ 0 → wire C q (assignment 60) = wire C q (assignment 61))
    (q n : Nat) (hne : q ≠ 0) : stable (rd C n q) = true := by
  unfold rd
  split
  next =>
    apply beq_iff_eq.mpr
    change obs true (49 : Fin 64) (col C q) = obs true (50 : Fin 64) (col C q)
    simp only [col,obs_table]
    exact hs q hne
  next => decide
lemma mask_col {C : Circuit} {w : Nat}
    (h60 : wire C w (assignment 60) = true) (h61 : wire C w (assignment 61) = true)
    (hlo : ∀ j : Fin 7, j.val ≠ 0 → wire C w (assignment (2^j.val)) = false) :
    maskOK (col C w) = true := by
  have low : ∀ j : Fin 64, (0xfc00000000000000 : B).getLsbD j.val = true →
      ∃ i : Fin 7, i.val ≠ 0 ∧ row false j = 2 ^ i.val := by decide +kernel
  have eq : (col C w).2 &&& 0xfc00000000000000 = 0 := by
    have zb : ∀ u : Fin 64, (0 : B).getLsbD u.val = false := by decide +kernel
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [BitVec.getLsbD_and,zb ⟨j,hj⟩]
    cases ht : (0xfc00000000000000 : B).getLsbD j
    · exact Bool.and_false _
    · obtain ⟨i,hi,e⟩ := low ⟨j,hj⟩ ht
      have hb := obs_table false ⟨j,hj⟩ (wire C w)
      rw [e,hlo i hi] at hb
      change (obs false ⟨j,hj⟩ (col C w) && true) = false
      exact (Bool.and_true _).trans hb
  have a : obs true 49 (col C w) = true := (obs_table ..).trans h60
  have b : obs true 50 (col C w) = true := (obs_table ..).trans h61
  change (obs true 49 (col C w) && obs true 50 (col C w) && _) = true
  simp only [Bool.and_eq_true,beq_iff_eq]
  exact ⟨⟨a,b⟩,eq⟩
lemma init_env (C : Circuit) : env C 7 = raw := by
  have h : ∀ j : Fin 7, col C j.val = table (fun x => x j) := by
    intro j; unfold col; congr 1; funext x
    unfold wire; rw [wires_eq_run,run_preserve _ _ _ (by simpa using j.isLt)]
    exact getD_ofFn ..
  unfold env
  calc
    _ = List.ofFn (fun j : Fin 7 => table (fun x => x j)) := by congr 1; funext j; exact h j
    _ = _ := by decide +kernel
lemma output_col {C : Circuit} (hc : ∀ x, C.eval (List.ofFn x) = C7Projection.target x) :
    col C C.output = Check.target := by
  have fe : (fun x : Fin 7 → Bool => wire C C.output x) = C7Projection.target := funext hc
  exact (congrArg table fe).trans (by decide +kernel)
lemma env_succ (C : Circuit) (n : Nat) : env C (n+1) = env C n ++ [col C n] := by
  unfold env; rw [List.ofFn_succ',List.concat_eq_append]; rfl
lemma steps_collection (C : Circuit)
    (h : ∀ j : Fin C.gates.length, StepOK (env C (7+j.val)) (col C (7+j.val))) :
    ∃ zs, Steps raw zs ∧ zs.length = C.gates.length ∧ raw ++ zs = env C (7+C.gates.length) := by
  suffices all : ∀ (l u : Nat), l+u=C.gates.length → ∃ zs, Steps (env C (7+l)) zs ∧
      zs.length=u ∧ env C (7+l) ++ zs = env C (7+C.gates.length) by
    simpa only [Nat.add_zero,init_env] using all 0 _ (Nat.zero_add _)
  intro l u
  induction u generalizing l with
  | zero =>
    intro e
    exact ⟨[],trivial,rfl,by simp_all⟩
  | succ u ih =>
    intro e
    obtain ⟨zs,hs,hl,he⟩ := ih (l+1) (by omega)
    have prev : env C (7+(l+1)) = env C (7+l) ++ [col C (7+l)] := env_succ _ _
    rw [prev] at hs he
    exact ⟨_::zs,⟨h ⟨l,by omega⟩,hs⟩,by simp [hl],by simpa only [List.append_assoc,List.singleton_append] using he⟩
lemma output_member {C : Circuit} (hc : ∀ x, C.eval (List.ofFn x)=C7Projection.target x) :
    Check.target ∈ env C (7+C.gates.length) := by
  have hn : C.output < 7+C.gates.length := by
    by_contra! bad
    have hh := hc (assignment 3)
    unfold Circuit.eval at hh; rw [wires_eq_run,List.getD_eq_default] at hh
    · exact (by decide : false ≠ C7Projection.target (assignment 3)) hh
    · simpa only [run_length,List.length_ofFn] using bad
  exact List.mem_ofFn.mpr ⟨⟨C.output,hn⟩,output_col hc⟩
end PEqualNP.Outside.L_meta_29925.Bridge

namespace PEqualNP.Outside.L_meta_29925.Bridge

open PEqualNP.CircuitLowerBounds
open Check (Sig zero one proper represented stable maskOK permit bb StepOK)

private lemma bb_unit (d : Bool) (a : Sig) :
    bb d a (if d then zero else one) = a := by
  rcases a with ⟨p, n⟩
  cases d
  · change (p &&& BitVec.allOnes 64, n &&& BitVec.allOnes 64) = (p, n)
    rw [BitVec.and_allOnes, BitVec.and_allOnes]
  · simp [bb, zero]

private lemma permit_arm (d : Bool) (r : Nat → Sig) (a b : Nat)
    (hs : ∀ q, q ≠ 0 → stable (r q) = true)
    (hg : a = 0 → d = true ∧ b ≠ 0 ∧ maskOK (r b) = true) :
    (stable (r a) || (d && maskOK (r b))) = true := by
  by_cases ha : a = 0
  · obtain ⟨hd, _, hb⟩ := hg ha
    simp [hd, hb]
  · simp [hs a ha]

private lemma pair_permit (d : Bool) (r : Nat → Sig) (a b : Nat)
    (hs : ∀ q, q ≠ 0 → stable (r q) = true)
    (hg : 0 ∈ [a, b] → d = true ∧
      ∃ w, w ∈ [a, b] ∧ w ≠ 0 ∧ maskOK (r w) = true) :
    permit d (r a) (r b) = true := by
  have left : (stable (r a) || (d && maskOK (r b))) = true := by
    apply permit_arm _ _ _ _ hs
    intro ha
    obtain ⟨hd, w, hw, hn, hm⟩ := hg (by simp [ha])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact (hn ha).elim
    · exact ⟨hd, hn, hm⟩
  have right : (stable (r b) || (d && maskOK (r a))) = true := by
    apply permit_arm _ _ _ _ hs
    intro hb
    obtain ⟨hd, w, hw, hn, hm⟩ := hg (by simp [hb])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨hd, hn, hm⟩
    · exact (hn hb).elim
  simp [permit, left, right]

private lemma fold_stepOK (d : Bool) (r : Nat → Sig) (av : List Sig)
    (l : List Nat) (hrep : ∀ q, represented av (r q))
    (hs : ∀ q, q ≠ 0 → stable (r q) = true)
    (hguard : 0 ∈ l → d = true ∧
      ∃ w, w ∈ l ∧ w ≠ 0 ∧ maskOK (r w) = true)
    (hfan : l.length ≤ 2) :
    StepOK av ((l.map r).foldr (bb d) (if d then zero else one)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · left
    right
    cases d <;> simp [proper]
  · left
    simpa only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, bb_unit] using hrep a
  · right
    refine ⟨d, r a, r b, hrep a, hrep b, pair_permit d r a b hs hguard, ?_⟩
    simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, bb_unit]
  · simp only [List.length_cons] at hfan
    omega

lemma gateFold_stepOK (g : Gate) (r : Nat → Sig) (av : List Sig)
    (hrep : ∀ q, represented av (r q))
    (hs : ∀ q, q ≠ 0 → stable (r q) = true)
    (hguard : 0 ∈ g.inputs → g.op = .or ∧
      ∃ w, w ∈ g.inputs ∧ w ≠ 0 ∧ maskOK (r w) = true)
    (hfan : g.inputs.length ≤ 2)
    (hop : g.op ∈ [.and, .or]) :
    StepOK av (gateFold r g) := by
  rcases g with ⟨op, l⟩
  change op ∈ [.and, .or] at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl
  · have hg : 0 ∈ l → false = true ∧
        ∃ w, w ∈ l ∧ w ≠ 0 ∧ maskOK (r w) = true := by
      intro h
      cases (hguard h).1
    simpa [gateFold] using fold_stepOK false r av l hrep hs hg hfan
  · have hg : 0 ∈ l → true = true ∧
        ∃ w, w ∈ l ∧ w ≠ 0 ∧ maskOK (r w) = true :=
      fun h => ⟨rfl, (hguard h).2⟩
    simpa [gateFold] using fold_stepOK true r av l hrep hs hg hfan

end PEqualNP.Outside.L_meta_29925.Bridge

namespace PEqualNP.Outside.L_meta_29925
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem guard_impossible (C : Circuit) (i : Fin C.gates.length) (w : Nat)
    (fan : FanInTwo C) (sz : C.size = 10)
    (hm : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    (reject : ∀ zs : List Check.Sig, Check.Steps Check.raw zs → zs.length ≤ 10 →
      Check.target ∈ Check.raw ++ zs → False)
    (hc : ∀ x, C.eval (List.ofFn x) = C7Projection.target x)
    (h0 : 0 ∈ (C.gates.get i).inputs) (hu : C7Projection.UniqueReader C i)
    (hop : (C.gates.get i).op = .or) (hw : w ∈ (C.gates.get i).inputs)
    (ne : w ≠ 0) (bound : w < 7+i.val)
    (ht : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ C7Projection.wire C w x = true) :
    False := by
  have high := C7Projection.wire_true_at_60 hm ht
  have stable := C7Projection.reader_stable_60_61 i fan hu hop h0 hw ne bound high
  have sig := C7Projection.reader_signature i fan hm hc hu hop h0 hw ne bound ht
  have orEq := C7Projection.unique_or_eq i (n := 7) (by decide) hop (fan _ (List.get_mem _ _)).2 h0 hw ne bound
  have low (j : Fin 7) (hj : j.val ≠ 0) :
      C7Projection.wire C w (C7Projection.assignment (2^j.val)) = false := by
    have h := sig.2.2 j hj
    rw [orEq] at h
    exact (Bool.or_eq_false_iff.mp h).2
  have mask := Bridge.mask_col high ((stable w ne).symm.trans high) low
  have conditions (j : Fin C.gates.length) := hm _ (List.get_mem _ j)
  have step (j : Fin C.gates.length) :
      Check.StepOK (Bridge.env C (7+j.val)) (Bridge.col C (7+j.val)) := by
    rw [Bridge.col_gate C j (conditions j)]
    apply Bridge.gateFold_stepOK
    · exact Bridge.rd_rep _ _
    · exact fun q hq => Bridge.stable_rd stable q _ hq
    · intro hz
      have eq := hu j hz
      subst j
      exact ⟨hop,w,hw,ne,by simpa only [Bridge.rd,if_pos bound] using mask⟩
    · exact (fan _ (List.get_mem _ _)).2
    · simpa only [List.mem_cons,List.not_mem_nil,or_false] using conditions j
  obtain ⟨zs,hs,len,he⟩ := Bridge.steps_collection C step
  exact reject zs hs (by change C.gates.length = 10 at sz; omega) (he ▸ Bridge.output_member hc)

theorem no_c7_10_or_under_and (C : Circuit) (i k : Fin C.gates.length) (w : Nat)
    (fan : FanInTwo C) (hsz : C.size = 10)
    (hcomp : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x) =
      ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)))
    (h0i : 0 ∈ (C.gates.get i).inputs)
    (h0u : ∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j=i)
    (hor : (C.gates.get i).op = .or) (_hand : (C.gates.get k).op = .and)
    (_hik : i.val < k.val) (_hk : 7+i.val ∈ (C.gates.get k).inputs)
    (hwi : w ∈ (C.gates.get i).inputs) (hw0 : w ≠ 0) (hwlt : w < 7+i.val)
    (hwtrue : ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
      (C.wires (List.ofFn x)).getD w false = true) : False := by
  have nn := Binary.no_not C fan hsz hcomp
  have hm (g) (hg : g ∈ C.gates) : g.op = .and ∨ g.op = .or := by
    have hx := (fan g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    exact hx.elim Or.inl (fun h => h.elim Or.inr (fun eq => (nn g hg eq).elim))
  exact guard_impossible C i w fan hsz hm Check.reject hcomp h0i h0u hor hwi hw0 hwlt hwtrue
end PEqualNP.Outside.L_meta_29925

theorem PEqualNP.Outside.L_meta_29925 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 13 ∈ (C.gates.get i).inputs ∧ 13 ≠ 0 ∧ 13 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 13 false = true)) := by
  rintro ⟨C,i,k,_,fan,sz,comp,h0,hu,hor,hand,hik,hk,hw,hn,hl,ht⟩
  exact PEqualNP.Outside.L_meta_29925.no_c7_10_or_under_and C i k 13 fan sz comp h0 hu hor hand hik hk hw hn hl ht
