import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29856.Binary

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

end PEqualNP.Outside.L_meta_29856.Binary

namespace PEqualNP.Outside.L_meta_29856.Check

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
def fetch (bits data i : Nat) : Nat := (data >>> (bits*i)) &&& (2^bits - 1)
def press (n : Nat) (f : Nat → α) : α := Nat.casesOn n (f 0) (fun j => f j.succ)
private theorem eq_press {α : Type} (n : Nat) (f : Nat → α) : press n f = f n := by cases n <;> rfl
def strictV : List Sig → (List Sig → Bool) → Bool
  | [], f => f []
  | s::w, f => press s.1.toNat fun a => press s.2.toNat fun b =>
    strictV w fun l => f ((BitVec.ofNat 64 a, BitVec.ofNat 64 b)::l)
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

structure Archive where
  rows : Nat
  headers : Nat
  count : Nat
  buckets : Nat
def Archive.get (t : Archive) (dict i : Nat) : List Sig :=
  press (fetch 90 t.rows i) fun z => recon dict 9 z

def digest (v : List Sig) : Nat := v.foldl (fun acc a =>
  let z := (a.1.toNat + 303 * a.2.toNat) % 1073741789
  acc + (z*z % 1073741789)) 0

def seek (p : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => false
  | n+1 => p (s+n) || seek p s n
private theorem seek_wit (p : Nat → Bool) (s : Nat) : ∀ n, seek p s n = true → ∃ i, p i = true
  | 0, h => by contradiction
  | n+1, h => by
    rcases Bool.or_eq_true_iff.mp h with hp | hq
    · exact ⟨_,hp⟩
    · exact seek_wit p s n hq

def hit (dict : Nat) (t : Archive) (v : List Sig) : Bool :=
  let bucket := digest v % t.buckets
  let h := fetch 20 t.headers bucket
  seek (fun i => Nat.blt i t.count && v.isPerm (t.get dict i)) (h >>> 6) (h &&& 63)
private theorem hit_sound {dict t v} (h : hit dict t v = true) :
    ∃ i < t.count, v.Perm (t.get dict i) := by
  obtain ⟨i,hi⟩ := seek_wit _ _ _ h
  have ⟨hb,hp⟩ := Bool.and_eq_true_iff.mp hi
  exact ⟨i,Nat.blt_eq.mp hb,List.isPerm_iff.mp hp⟩

def noneLive (k : Nat) (v : List Sig) : Prop :=
    v.Nodup → ∀ m ≤ k, ¬Live m 0 v.toFinset

private theorem no_step {dict t v k} (h : stepTest k 0 v (fun _ => false) (fun w => !(hit dict t w)) = false)
    (next : ∀ i < t.count, noneLive k (t.get dict i)) : noneLive (k+1) v := by
  intro hv m hm live
  have b : ∀ w, w.Nodup → ∀ l ≤ k, Live l 0 w.toFinset → (!(hit dict t w)) = true := by
    intro w hn l hl live'
    cases hh : hit dict t w with
    | false => rfl
    | true =>
      obtain ⟨i,hi,hp⟩ := hit_sound hh
      have eq : w.toFinset = (t.get dict i).toFinset := by ext x; simpa using (hp.mem_iff (a:=x))
      rw [eq] at live'
      exact False.elim (next i hi (hp.nodup_iff.mp hn) l hl live')

  have bad' := reduced_step (t:=0) live hm hv rfl b b
  exact (show False from by
    have e : stepTest k 0 v (fun w => !(hit dict t w)) (fun w => !(hit dict t w)) =
        stepTest k 0 v (fun _ => false) (fun w => !(hit dict t w)) := by simp [stepTest]
    rw [e,h] at bad'; contradiction)

def flag (dict : Nat) (next : Archive) (k : Nat) (v : List Sig) : Bool :=
  strictV v fun l => !(stepTest k 0 l (fun _ => false) (fun w => !(hit dict next w)))

def span (p : Nat → Bool) (s : Nat) : Nat → Bool
  | 0 => true
  | n+1 => p (s+n) && span p s n
private theorem span_ok {p : Nat → Bool} {s : Nat} : ∀ {n}, span p s n = true →
    ∀ i, s ≤ i → i < s+n → p i = true := by
  intro n; induction n with
  | zero => intros; omega
  | succ n ih =>
    intro h i hi hj
    obtain ⟨h1,h2⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : i=s+n
    · simpa [he] using h1
    · exact ih h2 i hi (by omega)

private theorem allRows {dict : Nat} {t next : Archive} {k : Nat}
    (hc : ∀ i < t.count, flag dict next k (t.get dict i) = true)
    (hn : ∀ i < next.count, noneLive k (next.get dict i)) :
    ∀ i < t.count, noneLive (k+1) (t.get dict i) := by
  intro i hi
  have z := hc i hi
  rw [flag,strictV_eq] at z
  exact no_step (by simpa using z) hn

def tableDict : Nat := 0xf1e1ffffffffffff03e7ffffffffc000e9d1ffffffffffff03f7ffffffffff80e5c9ffffffffffffffdfffffffe03fffe1c1ffffffffffff03c7ffffffe00000d9b1ffffffffffff03f7ffffffffff80d5a9fbf7efdfbf7effffffffffffffffd1a1fbf7efdfbf7e03e7ffffffffc000cd99ffffffffffffffbffffff01fffffc991ffffffffffff03b7fffff01fff80c589fbf7efdfbf7eff9ffffff0003fffc181ffffffffffff0387fffff0000000c181fbf7efdfbf7e03c7ffffffe00000c181fbf7efdfbf7e03a7fffff01fc000c181fbf7efdfbf7e0397fffff0003f80c181fbf7efdfbf7e0387fffff0000000b971ffffffffffff03f7ffffffffff80b569f7efdfbf7efdffffffffffffffffb161f7efdfbf7efd03e7ffffffffc000ad59efdfbf7efdfbffffffffffffffffa951cf9f3e7cf9f303f7ffffffffff80a549e7cf9f3e7cf9ffdfffffffe03fffa141f7efdfbf7efd03c7ffffffe00000a141e7cf9f3e7cf903c7ffffffe00000a141cf9f3e7cf9f303c7ffffffe00000a141c78f1e3c78f103e7ffffffffc000a141c78f1e3c78f103d7ffffffe03f80a141c78f1e3c78f103c7ffffffe000009d39ffffffffffffff7ffff80fffffff9931ffffffffffff0377fff80fffff809529f3e7cf9f3e7cff7ffff80fffffff9121fbf7efdfbf7e0367fff80fffc0009121f7efdfbf7efd0367fff80fffc0009121f3e7cf9f3e7c03e7ffffffffc0009121f3e7cf9f3e7c0377fff80fffff809121f3e7cf9f3e7c0367fff80fffc0008d19efdfbf7efdfbff3ffff8001fffff8911ffffffffffff0337fff8001fff808911efdfbf7efdfb0337fff8001fff808911cf9f3e7cf9f303b7fffff01fff808911cf9f3e7cf9f30377fff80fffff808911cf9f3e7cf9f30337fff8001fff808509f3e7cf9f3e7cff1ffff800003fff8509ebd7af5ebd7aff1ffff800003fff8509e7cf9f3e7cf9ff1ffff800003fff8509e3c78f1e3c78ff9ffffff0003fff8509e3c78f1e3c78ff5ffff80fe03fff8509e3c78f1e3c78ff3ffff8001fffff8509e3c78f1e3c78ff19fff800003fff8301ffffffffffffff0ffff80000007f8301dfbf7efdfbf7ff8ffffff000007f8301dfbf7efdfbf7ff4ffff80fe0007f8301dfbf7efdfbf7ff2ffff8001fc07f8301dfbf7efdfbf7ff0ffff80000007f8101fbf7efdfbf7e0307fff8000000008101f3e7cf9f3e7c0387fffff00000008101f3e7cf9f3e7c0347fff80fe000008101f3e7cf9f3e7c0327fff8001fc0008101f3e7cf9f3e7c0307fff8000000008101ebd7af5ebd7a0307fff8000000008101e3c78f1e3c780387fffff00000008101e3c78f1e3c780347fff80fe000008101e3c78f1e3c780327fff8001fc0008101e3c78f1e3c780311fff800003f808101e3c78f1e3c780301fff8000000008101cf9f3e7cf9f30307fff8000000008101cb972e5cb9720387fffff00000008101cb972e5cb9720327fff8001fc0008101cb972e5cb9720317fff800003f808101cb972e5cb9720307fff8000000008101c78f1e3c78f10387fffff00000008101c78f1e3c78f10347fff80fe000008101c78f1e3c78f10327fff8001fc0008101c78f1e3c78f10317fff800003f808101c78f1e3c78f10307fff8000000008101c3870e1c3870ff3ffff8001fffff8101c3870e1c3870ff19fff800003fff8101c3870e1c3870ff09fff80000007f8101c3870e1c387003f7ffffffffff808101c3870e1c387003e7ffffffffc0008101c3870e1c387003c7ffffffe000008101c3870e1c387003a7fffff01fc0008101c3870e1c38700397fffff0003f808101c3870e1c38700387fffff00000008101c3870e1c38700377fff80fffff808101c3870e1c38700367fff80fffc0008101c3870e1c38700357fff80fe03f808101c3870e1c38700347fff80fe000008101c3870e1c38700337fff8001fff808101c3870e1c38700327fff8001fc0008101c3870e1c38700317fff800003f808101c3870e1c38700311fff800003f808101c3870e1c38700307fff8000000008101c3870e1c38700301fff80000000078f1ffffffffffff01f7fc07ffffff8074e9fffffffffffffdfffc07ffffffff70e1ffffffffffff01e7fc07ffffc0006cd9fffffffffffffdfffc07ffffffff68d1bf7efdfbf7ef01f7fc07ffffff8064c9fffffffffffffddffc07ffe03fff60c1ffffffffffff01c7fc07ffe0000060c1bf7efdfbf7ef01e7fc07ffffc00060c1bf7efdfbf7ef01d7fc07ffe03f8060c1bf7efdfbf7ef01c7fc07ffe000005cb9fffffffffffffdfffc07ffffffff58b17efdfbf7efdf01f7fc07ffffff8054a8f9f3e7cf9f3efdfffc07ffffffff50a1fbf7efdfbf7e01e7fc07ffffc00050a17efdfbf7efdf01e7fc07ffffc00050a17af5ebd7af5e01e7fc07ffffc00050a0f9f3e7cf9f3e01e7fc07ffffc00050a078f1e3c78f1e01f7fc07ffffff8050a078f1e3c78f1e01e7fc07ffffc0004c99fffffffffffffdbffc07f01fffff4891ffffffffffff01b7fc07f01fff804891bf7efdfbf7ef01b7fc07f01fff8048917efdfbf7efdf01b7fc07f01fff8048913e7cf9f3e7cf01f7fc07ffffff8048913e7cf9f3e7cf01b7fc07f01fff804489fffffffffffffd9ffc07f0003fff4489fbf7efdfbf7efd9ffc07f0003fff4488f9f3e7cf9f3efddffc07ffe03fff4488f9f3e7cf9f3efdbffc07f01fffff4488f9f3e7cf9f3efd9ffc07f0003fff42813e7cf9f3e7cfff8ffffff000007f42803c78f1e3c78fffcfffffffe0007f42803c78f1e3c78fffaffffff01fc07f42803c78f1e3c78fff8ffffff000007f4081fbf7efdfbf7e0187fc07f00000004081bf7efdfbf7ef0187fc07f00000004081bb76eddbb76e01c7fc07ffe000004081bb76eddbb76e0187fc07f000000040817af5ebd7af5e0187fc07f000000040813e7cf9f3e7cf01c7fc07ffe0000040813e7cf9f3e7cf01a7fc07f01fc00040813e7cf9f3e7cf0197fc07f0003f8040813e7cf9f3e7cf0187fc07f000000040813a74e9d3a74e01a7fc07f01fc00040813a74e9d3a74e0197fc07f0003f8040813a74e9d3a74e0187fc07f00000004080f9f3e7cf9f3e0197fc07f0003f804080f9f3e7cf9f3e0187fc07f00000004080b972e5cb972e01c7fc07ffe000004080b972e5cb972e0197fc07f0003f804080b972e5cb972e0187fc07f0000000408078f1e3c78f1e01c7fc07ffe00000408078f1e3c78f1e01a7fc07f01fc000408078f1e3c78f1e0197fc07f0003f80408078f1e3c78f1e0187fc07f000000040803870e1c3870efd8ffc07f000007f40803870e1c3870e0387fffff000000040803870e1c3870e01f7fc07ffffff8040803870e1c3870e01e7fc07ffffc00040803870e1c3870e01d7fc07ffe03f8040803870e1c3870e01c7fc07ffe0000040803870e1c3870e01b7fc07f01fff8040803870e1c3870e01a7fc07f01fc00040803870e1c3870e0197fc07f0003f8040803870e1c3870e0187fc07f00000003c79fffffffffffffcfe0007ffffffff3871ffffffffffff00f60007ffffff803469f7efdfbf7efdfcfe0007ffffffff3061ffffffffffff00e60007ffffc0003061f7efdfbf7efd01e7fc07ffffc0003061f7efdfbf7efd00f60007ffffff803061f7efdfbf7efd00e60007ffffc0002c59efdfbf7efdfbfcfe0007ffffffff2851efdfbf7efdfb00f60007ffffff802851cf9f3e7cf9f300f60007ffffff802851bf7efdfbf7ef00f60007ffffff802851af5ebd7af5eb00f60007ffffff8028518f1e3c78f1e301f7fc07ffffff8028518f1e3c78f1e300f60007ffffff802449f7efdfbf7efdfcde0007ffe03fff2449efdfbf7efdfbfcde0007ffe03fff2449e7cf9f3e7cf9fddffc07ffe03fff2449e7cf9f3e7cf9fcfe0007ffffffff2449e7cf9f3e7cf9fcde0007ffe03fff2241bf7efdfbf7effece03ffffe0007f22419f3e7cf9f3e7feee03ffffffc07f22419f3e7cf9f3e7fece03ffffe0007f2041f7efdfbf7efd00c60007ffe000002041e7cf9f3e7cf900e60007ffffc0002041e7cf9f3e7cf900d60007ffe03f802041e7cf9f3e7cf900c60007ffe000002041c78f1e3c78f101c7fc07ffe000002041c78f1e3c78f100e60007ffffc0002041c78f1e3c78f100d60007ffe03f802041c78f1e3c78f100c60007ffe000002041bf7efdfbf7ef00c60007ffe000002041b76eddbb76ed01c7fc07ffe000002041b76eddbb76ed00e60007ffffc0002041b76eddbb76ed00c60007ffe000002041af5ebd7af5eb00c60007ffe000002041a74e9d3a74e901c7fc07ffe000002041a74e9d3a74e900d60007ffe03f802041a74e9d3a74e900c60007ffe0000020418f1e3c78f1e301c7fc07ffe0000020418f1e3c78f1e300e60007ffffc00020418f1e3c78f1e300d60007ffe03f8020418f1e3c78f1e300c60007ffe000002041870e1c3870e1fcce0007ffe0007f2041870e1c3870e102c603ffffe000002041870e1c3870e101e7fc07ffffc0002041870e1c3870e101d7fc07ffe03f802041870e1c3870e101c7fc07ffe000002041870e1c3870e100f60007ffffff802041870e1c3870e100e60007ffffc0002041870e1c3870e100d60007ffe03f802041870e1c3870e100c60007ffe000001c39fffffffffffffc7e00000fffffff1831ffffffffffff007600000fffff8018317efdfbf7efdf0177fc000fffff8018317efdfbf7efdf00f60007ffffff8018317efdfbf7efdf007600000fffff801429f7efdfbf7efdfc7e00000fffffff1429f3e7cf9f3e7cfc7e00000fffffff1428f9f3e7cf9f3efc7e00000fffffff1428f1e3c78f1e3cfd7ffc000fffffff1428f1e3c78f1e3cfcfe0007ffffffff1428f1e3c78f1e3cfc7e00000fffffff12217efdfbf7efdffe6e03f80fffc07f12207cf9f3e7cf9ffeee03ffffffc07f12207cf9f3e7cf9ffe6e03f80fffc07f1021f7efdfbf7efd006600000fffc0001021f3e7cf9f3e7c0167fc000fffc0001021f3e7cf9f3e7c00e60007ffffc0001021f3e7cf9f3e7c006600000fffc00010217efdfbf7efdf006600000fffc00010217af5ebd7af5e006600000fffc000102176eddbb76edd00e60007ffffc000102176eddbb76edd007600000fffff80102176eddbb76edd006600000fffc000102172e5cb972e5c0167fc000fffc000102172e5cb972e5c007600000fffff80102172e5cb972e5c006600000fffc0001020f1e3c78f1e3c0167fc000fffc0001020f1e3c78f1e3c00e60007ffffc0001020f1e3c78f1e3c007600000fffff801020f1e3c78f1e3c006600000fffc000102078f1e3c78f1e0167fc000fffc000102078f1e3c78f1e00e60007ffffc000102078f1e3c78f1e007600000fffff80102078f1e3c78f1e006600000fffc000102070e1c3870e1cfc6e00000fffc07f102070e1c3870e1c026603f80fffc000102070e1c3870e1c01e7fc07ffffc000102070e1c3870e1c0177fc000fffff80102070e1c3870e1c0167fc000fffc000102070e1c3870e1c00f60007ffffff80102070e1c3870e1c00e60007ffffc000102070e1c3870e1c007600000fffff80102070e1c3870e1c006600000fffc0000c19fffffffffffffc3e0000001fffff0c19efdfbf7efdfbfd3ffc00001fffff0c19efdfbf7efdfbfcbe0007f01fffff0c19efdfbf7efdfbfc7e00000fffffff0c19efdfbf7efdfbfc3e0000001fffff0a113e7cf9f3e7cffe3e03f8001fffff0a111e3c78f1e3c7febe03fff01fffff0a111e3c78f1e3c7fe7e03f80fffffff0a111e3c78f1e3c7fe3e03f8001fffff0811efdfbf7efdfb00360000001fff800811cf9f3e7cf9f30137fc00001fff800811cf9f3e7cf9f300360000001fff800811af5ebd7af5eb00360000001fff8008118f1e3c78f1e30137fc00001fff8008118f1e3c78f1e300b60007f01fff8008118f1e3c78f1e3007600000fffff8008118f1e3c78f1e300360000001fff8008117efdfbf7efdf00360000001fff8008116eddbb76eddb007600000fffff8008116eddbb76eddb00360000001fff8008114e9d3a74e9d30137fc00001fff8008114e9d3a74e9d3007600000fffff8008114e9d3a74e9d300360000001fff8008113e7cf9f3e7cf0137fc00001fff8008113e7cf9f3e7cf00b60007f01fff8008113e7cf9f3e7cf007600000fffff8008113e7cf9f3e7cf00360000001fff8008112e5cb972e5cb0137fc00001fff8008112e5cb972e5cb00b60007f01fff8008112e5cb972e5cb00360000001fff8008110e1c3870e1c3fc3e0000001fffff08110e1c3870e1c3023603f8001fff8008110e1c3870e1c301f7fc07ffffff8008110e1c3870e1c301b7fc07f01fff8008110e1c3870e1c30177fc000fffff8008110e1c3870e1c30137fc00001fff8008110e1c3870e1c300f60007ffffff8008110e1c3870e1c300b60007f01fff8008110e1c3870e1c3007600000fffff8008110e1c3870e1c300360000001fff800609fffffffffffffe1e03f800003fff0608fdfbf7efdfbffe9e03fff0003fff0608fdfbf7efdfbffe5e03f80fe03fff0608fdfbf7efdfbffe3e03f8001fffff0608fdfbf7efdfbffe1e03f800003fff0409efdfbf7efdfbfc1e000000003fff0409ebd7af5ebd7afc1e000000003fff0409e7cf9f3e7cf9fc9e0007f0003fff0409e7cf9f3e7cf9fc5e00000fe03fff0409e7cf9f3e7cf9fc3e0000001fffff0409e7cf9f3e7cf9fc1e000000003fff0409e3c78f1e3c78fd19fc0000003fff0409e3c78f1e3c78fc9e0007f0003fff0409e3c78f1e3c78fc5e00000fe03fff0409e3c78f1e3c78fc3e0000001fffff0409e3c78f1e3c78fc18000000003fff0408f9f3e7cf9f3efc1e000000003fff0408f1e3c78f1e3cfd1ffc0000003fff0408f1e3c78f1e3cfc9e0007f0003fff0408f1e3c78f1e3cfc5e00000fe03fff0408f1e3c78f1e3cfc3e0000001fffff0408f1e3c78f1e3cfc1e000000003fff0408e9d3a74e9d3afd1ffc0000003fff0408e9d3a74e9d3afc9e0007f0003fff0408e9d3a74e9d3afc3e0000001fffff0408e9d3a74e9d3afc1e000000003fff0408e1c3870e1c38ff9ffffff0003fff0408e1c3870e1c38ff19fff800003fff0408e1c3870e1c38fe1803f800003fff0408e1c3870e1c38fdfffc07ffffffff0408e1c3870e1c38fddffc07ffe03fff0408e1c3870e1c38fd9ffc07f0003fff0408e1c3870e1c38fd5ffc000fe03fff0408e1c3870e1c38fd3ffc00001fffff0408e1c3870e1c38fd1ffc0000003fff0408e1c3870e1c38fd19fc0000003fff0408e1c3870e1c38fcfe0007ffffffff0408e1c3870e1c38fcde0007ffe03fff0408e1c3870e1c38fcbe0007f01fffff0408e1c3870e1c38fc9e0007f0003fff0408e1c3870e1c38fc7e00000fffffff0408e1c3870e1c38fc5e00000fe03fff0408e1c3870e1c38fc3e0000001fffff0408e1c3870e1c38fc1e000000003fff0408e1c3870e1c38fc18000000003fff02019f3e7cf9f3e7fe8e03fff000007f02019f3e7cf9f3e7fe4e03f80fe0007f02019f3e7cf9f3e7fe0e03f80000007f02011e3c78f1e3c7fe8e03fff000007f02011e3c78f1e3c7fe4e03f80fe0007f02011e3c78f1e3c7fe2e03f8001fc07f02011e3c78f1e3c7fe1e03f800003fff02011e3c78f1e3c7fe0e03f80000007f02009d3a74e9d3a7fe8e03fff000007f02009d3a74e9d3a7fe4e03f80fe0007f02007cf9f3e7cf9ffe4e03f80fe0007f02007cf9f3e7cf9ffe2e03f8001fc07f02007cf9f3e7cf9ffe0e03f80000007f02005cb972e5cb97fe4e03f80fe0007f02005cb972e5cb97fe2e03f8001fc07f02003c78f1e3c78fff0ffff80000007f02003c78f1e3c78ffe8e03fff000007f02003c78f1e3c78ffe4e03f80fe0007f02003c78f1e3c78ffe2e03f8001fc07f02003c78f1e3c78ffe0e03f80000007f02001c3870e1c387ffefffffffffc07f02001c3870e1c387ffcfffffffe0007f02001c3870e1c387ff8ffffff000007f02001c3870e1c387ff4ffff80fe0007f02001c3870e1c387ff2ffff8001fc07f02001c3870e1c387ff0ffff80000007f02001c3870e1c387fefe03ffffffffff02001c3870e1c387feee03ffffffc07f02001c3870e1c387fece03ffffe0007f02001c3870e1c387feae03fff01fc07f02001c3870e1c387fe9e03fff0003fff02001c3870e1c387fe8e03fff000007f02001c3870e1c387fe7e03f80fffffff02001c3870e1c387fe6e03f80fffc07f02001c3870e1c387fe5e03f80fe03fff02001c3870e1c387fe4e03f80fe0007f02001c3870e1c387fe3e03f8001fffff02001c3870e1c387fe2e03f8001fc07f02001c3870e1c387fe1e03f800003fff02001c3870e1c387fe0e03f80000007f02001c3870e1c387fe0c03f80000007f0001f3e7cf9f3e7c00860007f00000000001ebd7af5ebd7a00060000000000000001e7cf9f3e7cf900260000001fc0000001e3c78f1e3c7800860007f00000000001e3c78f1e3c78004600000fe000000001e3c78f1e3c7800260000001fc0000001e3c78f1e3c7800000000000000000001c78f1e3c78f100260000001fc0000001c78f1e3c78f10016000000003f800001c78f1e3c78f100060000000000000001c3870e1c38700101fc00000000000001c3870e1c387000000000000000000001b366cd9b366c0147fc000fe000000001b366cd9b366c00060000000000000001af5ebd7af5eb00060000000000000001a3468d1a34680101fc00000000000001a3468d1a3468000000000000000000018f1e3c78f1e30107fc000000000000018b162c58b16200860007f000000000018b162c58b16200060000000000000001870e1c3870e100c60007ffe000000001870e1c3870e100860007f00000000001870e1c3870e1004600000fe000000001870e1c3870e10006000000000000000183060c1830600101fc0000000000000183060c18306000c60007ffe00000000183060c18306000860007f0000000000183060c183060006600000fffc000000183060c183060004600000fe00000000183060c18306000260000001fc000000183060c1830600010000000003f80000183060c1830600006000000000000000183060c183060000000000000000000017af5ebd7af5e0006000000000000000166cd9b366cd9005600000fe03f80000166cd9b366cd90006000000000000000162c58b162c580010000000003f80000162c58b162c5800000000000000000001468d1a3468d1004600000fe000000001468d1a3468d10006000000000000000142850a1428500101fc0000000000000142850a142850000000000000000000013e7cf9f3e7cf004600000fe000000001366cd9b366cd00a60007f01fc0000001366cd9b366cd000600000000000000013264c993264c0127fc00001fc00000013264c993264c00060000000000000001264c993264c900960007f0003f800001264c993264c9000600000000000000012244891224480111fc0000003f800001224489122448000000000000000000010e1c3870e1c300360000001fff8000010e1c3870e1c300260000001fc00000010e1c3870e1c30016000000003f8000010e1c3870e1c3000600000000000000010a142850a14200360000001fff8000010a142850a14200260000001fc00000010a142850a1420016000000003f8000010a142850a14200060000000000000001060c183060c10187fc07f00000000001060c183060c10107fc00000000000001060c183060c100c60007ffe000000001060c183060c100860007f00000000001060c183060c1004600000fe000000001060c183060c100360000001fff800001060c183060c100260000001fc0000001060c183060c10016000000003f800001060c183060c1000600000000000000010204081020400301fff8000000000001020408102040020003f80000000000010204081020400101fc0000000000000102040810204000c60007ffe00000000102040810204000860007f00000000001020408102040004600000fe00000000102040810204000360000001fff80000102040810204000260000001fc00000010204081020400010000000003f8000010204081020400006000000000000000102040810204000000000000000000000f1e3c78f1e3c0107fc00000000000000f1e3c78f1e3c00860007f00000000000f1e3c78f1e3c00060000000000000000e1c3870e1c380010000000003f800000e1c3870e1c3800000000000000000000c993264c99320117fc0000003f800000c993264c993200060000000000000000c183060c18300187fc07f00000000000c183060c18300101fc00000000000000c183060c183000860007f00000000000c183060c1830004600000fe000000000c183060c183000360000001fff800000c183060c183000260000001fc0000000c183060c18300010000000003f800000c183060c183000000000000000000000b162c58b162c004600000fe000000000b162c58b162c00060000000000000000a142850a14280010000000003f800000a142850a14280000000000000000000089122448912200960007f0003f800000891224489122000600000000000000008102040810200101fc0000000000000081020408102000c60007ffe00000000081020408102000860007f00000000000810204081020007600000fffff800000810204081020004600000fe00000000081020408102000260000001fc00000008102040810200010000000003f800000810204081020000600000000000000008102040810200000000000000000000078f1e3c78f1e0016000000003f80000070e1c3870e1c006600000fffc000000070e1c3870e1c004600000fe00000000070e1c3870e1c00260000001fc000000070e1c3870e1c0006000000000000000068d1a3468d1a00260000001fc000000068d1a3468d1a0006000000000000000060c183060c180101fc0000000000000060c183060c1800c60007ffe00000000060c183060c1800860007f0000000000060c183060c18006600000fffc000000060c183060c18004600000fe00000000060c183060c1800260000001fc000000060c183060c180010000000003f80000060c183060c180006000000000000000060c183060c18000000000000000000004891224489120127fc00001fc00000004891224489120006000000000000000040810204081001c7fc07ffe0000000004081020408100101fc0000000000000040810204081000860007f00000000000408102040810006600000fffc0000000408102040810004600000fe00000000040810204081000260000001fc00000004081020408100010000000003f80000040810204081000060000000000000000408102040810000000000000000000003870e1c3870e0187fc07f000000000003870e1c3870e0107fc000000000000003870e1c3870e00860007f000000000003870e1c3870e000600000000000000003060c183060c0187fc07f000000000003060c183060c0107fc000000000000003060c183060c00860007f000000000003060c183060c006600000fffc00000003060c183060c004600000fe0000000003060c183060c00360000001fff8000003060c183060c00260000001fc00000003060c183060c0016000000003f8000003060c183060c000600000000000000002850a142850a0187fc07f000000000002850a142850a0107fc000000000000002850a142850a00860007f000000000002850a142850a00060000000000000000204081020408fc18000000003fff0000204081020408fc0800000000007f00002040810204080187fc07f000000000002040810204080101fc0000000000000020408102040800860007f00000000000204081020408006600000fffc0000000204081020408004600000fe00000000020408102040800260000001fc00000002040810204080010000000003f8000002040810204080006000000000000000020408102040800000000000000000000183060c183060187fc07f00000000000183060c1830600860007f00000000000183060c1830600060000000000000000102040810204006600000fffc0000000102040810204004600000fe00000000010204081020400260000001fc0000000102040810204000600000000000000000c183060c18300360000001fff8000000c183060c18300260000001fc00000000c183060c183000600000000000000000810204081020187fc07f000000000000810204081020107fc0000000000000008102040810200e60007ffffc000000008102040810200860007f00000000000081020408102004600000fe00000000008102040810200360000001fff80000008102040810200260000001fc00000000810204081020016000000003f8000000810204081020006000000000000000004081020408100c60007ffe00000000004081020408100860007f00000000000040810204081004600000fe00000000004081020408100060000000000000000000000000000ff8ffffff000007f0000000000000000ff09fff80000007f0000000000000000fe3e03f8001fffff0000000000000000fe1803f800003fff0000000000000000fe0803f80000007f0000000000000000fc7e00000fffffff0000000000000000fc3e0000001fffff0000000000000000fc18000000003fff0000000000000000fc0800000000007f000000000000000003c7ffffffe0000000000000000000000387fffff000000000000000000000000301fff8000000000000000000000000020003f800000000000000000000000001f7fc07ffffff80000000000000000001e7fc07ffffc000000000000000000001c7fc07ffe00000000000000000000001b7fc07f01fff80000000000000000001a7fc07f01fc00000000000000000000197fc07f0003f8000000000000000000187fc07f000000000000000000000000167fc000fffc00000000000000000000147fc000fe0000000000000000000000137fc00001fff8000000000000000000127fc00001fc00000000000000000000111fc0000003f8000000000000000000107fc000000000000000000000000000101fc0000000000000000000000000000f60007ffffff80000000000000000000e60007ffffc000000000000000000000d60007ffe03f80000000000000000000c60007ffe00000000000000000000000b60007f01fff80000000000000000000a60007f01fc000000000000000000000960007f0003f80000000000000000000860007f00000000000000000000000007600000fffff800000000000000000006600000fffc0000000000000000000005600000fe03f800000000000000000004600000fe00000000000000000000000360000001fff80000000000000000000260000001fc00000000000000000000016000000003f8000000000000000000010000000003f8000000000000000000006000000000000
def t0 : Archive := ⟨0x205711915993e444e8, 0x1, 1, 1⟩
def t1 : Archive := ⟨0x205711915993e444e804800815c4645664f9113a0040020579dc4645664f9113a000815c4645664f9113a06b00205711915993e444e81800091e05711915993e444e80020571191631664f9113a000815c4645664f9113a08a00205711915993e444e8018008e605711915993e444e800205711915993e444e81ec00815c4645664f9113a04400253815c4645664f9113a0008fe05711915993e444e800205711bd645664f9113a0008ca05711915993e444e8002057b1c4645664f9113a000815c46d9915993e444e80020571191599614f9113a000815c4645865993e444e800205711915993e444e802800815f2711915993e444e800205711915993e444e831c00815c4645664f9113a00200205711b1645664f9113a000815c4645664f9113a031002057edc4645664f9113a000815c4645664f9113a09900205711915993e444e814c00815c4645664f9113a0a4, 0x7020064300000005c20054200000004c200481004410000000000003c200381000000000000341002c2002420018300000001410000000000000000010100043000010000000000, 30, 30⟩
def t2 : Archive := ⟨0x2057edc4645664f9113a0b100247815c46d9664f9113a000815c4645664f9113a036815c4645664f928444e814e05711b6645664f9113a053815c4645664f9113a0990080000205711915a13e444e8815f97b1c4645664f9113a205711b1645664f9113a060815ec711915993e444e81560571191631664f9113a004815c470991631664f9113a253815c4645664f9113a0c7815c4645664f9113a0a422a057b1c46f5915993e444e8815ec71191599614f9113a20571191599614f9113a04f8e605711915993e444e8292057c5e7711915993e444e8815e7711915993e444e801800815c4645664f9113a0cb00205711b66c5664f9113a000815c4645664f9113b4e8815c4645664f9113a09902a45815c46458c5993e444e800205711915bd664f9113a205711bd645664f9113a09494e05711915993e444e801247815c4645664f9113a099815c46456f5993e444e80c6057c9c4645664f9113a0068e605711915993e444e822e0579dc4645664f9113a032815e7711915993e444e822a05711915993e444e826412815fb711915993e444e801a0571192645664f9113a0028e60579dc4645664f9113a232815c4645664f9113a0c7815c4645664f9113a05300a05711bc6c5915993e444e893647815c4645664f9113a205711c16f5915993e444e8815c46d9915993e444e81ac00815c4645664f9113a09b00205711915993e444e81da057b1c4645865993e444e8815c4645664f9113a07b18205711915994f4f9113a060815f2711915993e444e82280097a05711915993e444e88fa39815c4645664f9113a23f815c46458c5993e444e88e6057c9c4645664f9113a205711b1645664f9113a099815fb711915993e444e822800815c4645664f9113a060815c4645664f9113a05302a32815c4645664f9113a0048e6057edc4645664f9113a2057edc4645664f9113a05781e05711915993e444e800a05711915993e444e81803100205711a2645664f9113a247815c4645664f9113a05393605711b1645664f9113a222815c4645664f9113a06b815c4645664f9113a0530480000205711935993e444e894e3f815c4645664f9113a20571191631664f9113a0a4815c46d9915993e444e802205711915993e444e81ac02815c470591619664f9113a205711915993e444e818044815c4699915993e444e822a448fe05711915993e444e800205711915993e444e817250815c46f5915993e444e8815c46f5915993e444e801800815c46c591619664f8e8815f171191599614f9113a20571191599614f9113a00600205711bc645664f9113a205711b1645664f9113a04a815c46c5915993e444e814e53815c4645664f9113a0a400205711915993e44ce801205809f2711915993e444e8815c4645664f9113a0991ee05711915993e444e81ac0a815c4645664f9113a0040040000205711915993e444e9815e771191631664f9113a20571191599614f9113a0d0816027edc4645664f9113a000815c4645905993e444e88fe32815c4645664f9113a205711b6645664f9113a0c700205711915993e444e826647815c4645664f9113a06b815c46f5915993e444e822800815c4645664f9113a43183e05711915993e444e802a0571191599404f9113a00a815ec711915993e444e82860571191599614f9113a08a815da711915993e444e829205711915993e444e81ac128e605711bd645664f9113a205711915993e444e8264318e60571191599614f9113a000815fb7c9915993e444e80024d815c4645664f9113a2057c9c46458c5993e444e800205645664f9113a01202a0571191599554f9113a0c700205711915993e444e82a400815f2711664f9113a00e94e0579dc4645664f9113a000815c4645664f913444e8815fb71191631664f9113a205715c4645664f9113a002815c46d9915993e444e801205711c26d9915993e444e88ca05711915993e444e82920571191619664f9113a006815c464d915993e444e80100094e47711915993e444e8815c4645664f9113a09911205711b1645664f9113a06b0000082dc4645664f9113a205711915993e444e81ec5394e057c9c4645664f9113a000815c4649915993e444e800205711915993e444e81280096205711915993e444e894e057edc4645664f9113a000815c4669915993e444e800205711915993e444e814e05711915993e444e831c0286205711915993e444e82920571191619664f9113a08a00205711915993e444e812e057119a645664f9113a031815c4645664f9113a0530c632815e7711915993e444e88e60571191619664f9113a2057b1c4645664f9113a04681602711bd645664f9113a20571191619664f9113a07f00205719c4645664f9113a00091e32711915993e444e8815c4645664f9113a0c702a05711915993e444e80100200207815c4645664f9113a23e8ca05711915993e444e800232711915993e444e804a05711915993e444e829001815f879dc4645664f9113a205711915993e444e814c448ca057c9c4645664f9113a2057e5c46458c5993e444e891e05711915993e444e831e3f815c46d9915993e444e80025b815c4645664f9113a232815fb711915993e444e8815c4645664f9113a07b1ae05711bd6458c5993e444e8815c46458c599614f9113a205711915993e444e831c12815c4645664f9113a00a01000815c4645664f9113a06b815f87c9c4645664f9113a20571191619664f9113a005815f17b1c4645664f9113a2057b1c4645664f9113a006815fb711915993e444e821a05711915993e444e81ac3191e05711915993e444e8012057c9c4645664f9113a0330020f815c4645664f9113a000815c4645665013e444e8815c46d9915993e444e829000815f2711914f9113a00494e05711bd645664f9113a205711915993e444e80480494e0571191599614f9113a205711b1645664f9113a0c7815c46f5915993e444e829800815c464566501113a00a815c4645664f9113a099182057b1c4645664f9113a08a815c4645664f9113a06b1123f815c4645664f9113a00200205711915993e444e81ba39815ec711915993e444e8815c46458c619664f9113a205711b1645664f9113a00400205711915993e444e80220579dc46d9915993e444e800205711915993e444e833e53815c4645664f9113a0ad82605711915993e444e801232815c46f5915993e444e8815c46f5915993e444e816400815c5711915993e444e88ca0571191599614f9113a23f815c4645664f9113a00a815c4645664f9113a0a400800815c4679915993e444e894e0571191619664f9113a2478fe05711915993e444e8815f2711b6645664f9113a205711915993e444e831c7b0023f815f2711914f9113a2057edc46d9915993e444e88fe05711915993e444e804a05711915993e444e8180539120571191619664f9113a000815c4645664f9113a0c7815c4645664f911424e829205711915993e444e82900a00205711915993e444e820400815ec79d915993e444e8815c4689915993e444e814e05711915993e444e831c31815e7711915993e444e800a47815c4645664f9113a0a4815c4645664f9113a07b01000815c464566444e801002815c4679915993e444e81123f815c46c5915993e444e8815c4645664f9113a0a40480000205721915993e444e88ca0571191619664f9113a000815c4709915993e444e8002057c9ec645664f9113a205711915993e444e831c44815c4645664f9113a031012057c9c4645664f9113a002815ec71191631664f9113a20579dc4645664f9113a00a815fb711915993e444e80080091605711915993e444e8815f871191619664f9113a000815c464586599113a005815c4645664f9113a06b18247815e7711915993e444e8815c46c5915993e444e829605711b1645664f9113a0a4815c4645664f9113a08a01800002057119159940444e8815e7711915993e444e804a39815c4645664f9113a006815c4645664f9113a04401205711915993e444e826453815f2711915993e444e802a05711bd6d9915993e444e800205711925993e444e800a53815ec711915993e444e8815c46d991599614f9113a000815c4645664f9113c40a815fb711915993e444e802a47815f2711915993e444e882e05711915993e444e801a39815c4645664f9113a0d08fe05711915993e444e81ee05711915a9664f9113a01291e057edc4645664f9113a2057c9c4645664f9113a01200239815ec71191599113a20579dc46c5915993e444e894e05711915993e444e825239815c4645664f9113a08a815fb711915993e444e8048008ca05711915993e3a002815c46d9915993e444e81f63f815c4645664f9113a031815c4645664f914444e801a0571191631664f9113a06d8ca057b1c4645664f9113a205711915993e444e82907b815f2711b1645664f9113a000815c4645664f933444e8815c46f5915993e444e800a057edc46c5915993e444e8815c4645664f9113a0991ae0571191599614f9113a002815c46d991619664f9113a000815c4645664f9113a0a500205711915993e444e82900000205711915993e450e800205711915993e444e816800815c4645674f9113a00293a39815c4645664f9113a23f815c4645664f9113a044815c4645664f9113a0a40c4008a205711915993e444e8815c4645664f9113a0c718247815c4645664f9113a019815c46f5915993e444e802a0571191599614f9113a00a815e7711915993e444e81ec00815c4645664f91a3a0120020577dc4645664f9113a20571191631664f9113a00600205711915993e444e822c0000205711915993e444eb91e05711bd645664f9113a247815c4645665853e444e8815c4645664f9113a0a411000815f2711bd6453e444e8815c46f5915993e444e804a0571191599614f9113a012815c4645664f9113a0600120579dc4645664f9113a031815f2711915993e444e81ee05711915993e444e81ac53815c4645865993e444e800a3f815c4645664f9113a0cb815c46458c5993e444e822a057edc4645664f9113a07b94e05711915993e444e8018008fa05711915993e444e800205711915a9664f9113a239815c46458c5993e444e800000815c4645664f9113c400815c4645665213e444e800205711915993e444ed01800815c464d664f9113a004815c46f5b1645664f9113a2057c9c4645664f9113a031815c46c591599614f9113a20579dc4645664f9113a044815fb711915993e444e80c60571191619664f9113a00a8e605711915993e444e80e000815c4645664f9163a00a816007edc4645664f9113a2057b1c46d9915993e444e894e05711915993e444e822800815c4645664f9113a4e8815c4645664f9113a0c72640000205711925993e444e891e0571191619664f9113a2538e605711915993e444e8815c46458c5993e444e82a000815f2711916193e444e8815f2711915993e444e81100000209711915993e444e8815c4645664f9113a4e80c60571191619664f9113a0128ca05711915993e444e801a0571191599484f9113a044815fb711915993e444e811000815c4699915993e444e8815c4645685993e444e802a3f815c4645664f9113a06000205711915993e491113a205711915993e444e82640400000815c4645664f91a3a205711915993e491113a031815c46c591619664f9113a000815c4645664f9113a0198ca05711915993e444e822a05711bd645664f9113a07b815c4645665853e444e81ec00815f9711915993e444e88e632815c4645664f9113a000815c46453e444e801804815ec711915993e444e800a05711915993e44d113a00400205711915993e444e815605711915993e444e831c53815c4645664f9113a0a418000002057119159d3e444e800205715915993e444e800a057fdc46c5915993e444e8815c46f5915993e444e80c60571191599614f9113a031815c4645664f9113a00600400815c4645664f9113a00e815ec711915993e444e802a0579dc4645664f9113a076815c4645664f9113a0530120571195645664f9113a012815c46c5915993e444e837247815ec711915993e444e800205711915993e444e81f605711bd645664f9113a04494e0571191631664f9113a20579dc4645664f9113a060815c4645665853e444e811000815c4645664f9113a0ad8fe05711915993e444e8266057b1c4645664f9113a01200205711915993e444e819e0571191619664f9113a07b815c6711915993e444e801205711b6645664f9113a006815c4645664f9113a0c71ac0000205711915993e458e800000815c6645664f9113a25e815fb711915993e444e8815f2711915993e444e8180008fe39711915993e444e8815c4645865993e444e80c6057edc4645664f9113a060815ec711b1645664f9113a205711915993e444e829099815c4645735993e444e822800815ec711b664566444e8002057fdc4645664f9113a232815c46458c5993e444e894e05711915993e444e833605711b6645664f9113a08a815c4645664f9113a06b01000815c4645685993e444e88e605711b6645664f9113a205755c4645664f9113a08a8fe05711915993e444e814e0571191619664f9113a04400205711915993e444e837205711915993e444e801802815e7711915993e444e826605711a6645664f9113a06094e32815c4645664f9113a259815ec711915993e444e8815c4705b1645664f9113a24e815c46d9915993e444e8815c4645664fd3e444e801a05711915993e444e829053815c46458c5993e444e82fa448ca05711915993e444e80020571195645664f9113a2057b1c4645664f9113a07b815f2711915993e444e826605711915993e444e80280696e3f815c4645664f9113a205711915993e444e822802815fb711915993e444e826628815c4645664f9113a05300205711915993e444e813e39815c4645664f9113a00200205711915993e444e828605711bd645664f9113a06094247815c4645664f9113a20571191599614f9113a06091e05711915993e444e801a3f815c4645664f9113a06b815ec711915993e444e80c605711915993e444e804806816007b1c4645664f9113a00000205715915993e444e89620579dc4645664f9113a20579dc4645664f9113a053815c4645664f9113a08a02800815c46f5b65993e444e800205711915993e444e82500081dc4645664f9113a0028e605711915993e444e802a47815c4645664f9113a08a815c4645664f9113a0c701205711b66458c5993e444e8815ec711915993e444e811205711915993e444e82906b00247815fb711664f9113a2478e605711915993e444e8815c4645664f9113a08a04a05711b1645664f9113a006815f2711915993e444e814c00815c4645664f9113f4e800205711c1645664f9113a239815c4645664f9113a012815fb711915993e444e814e05711bc645665853e444e80020571191599524f9113a000815c4645664f9113a0b1815c4645865993e444e818000815c4645664f9113a04694e05711b6645664f9113a24e91e05711915993e444e8815c464590599614f9113a205711b1645664f9113a08a815c46f5915993e444e826400815c4645664f9113a09000205711915993e444e81b60571191599614f9113a099815e7711915993e444e81ae39815c4645664f9113a06300205711b66453e444e802239815c46c5915993e444e8815c4645665693e444e822a05711915993e444f13a00a00205711915e9664f9113a25b815f2711915993e444e8815c46458c5993e444e80080083dc4645664f9113a00a0020575dc4645664f9113a23f815c4645664f9113a0c7815f2711915993e444e81ae05721c4645664f9113a006815c4645664f9113a07b01a057edc4645664f9113a06b8ca05711b6645664f9113a00094205711915993e444e8002057c5c4645664f9113a000815c4645664fd113a006815c46458c5993e444e802a53815c4645664f9113a0020020571191619665853e3a2598e605711915993e444e8815c464590619664f9113a000815c4645664f9113a09c815c4645664f9113a03101a05711bd645664f9113a053815c4645665853e444e814e3f815c4645664f9113a00491e0571191631664f9113a20571191619664f9113a099002057c9915993e444e804800815c4645664f9113a0d0815c4645664f9113a0c729205711915993e444e82287b8e605711915993e444e81ee0571191631664f9113a01200205711915993e444e80c800815c4645664f9113a08a00205711aa645664f9113a2057b1c4645664f9113a06094e05711915993e444e802a458fe05711915993e444e800205711915993e4b9113a000815c4645664f9113a05700205711916193e444e801a05711915993e444e81100600205739c4645664f9113a00087605711915993e444e8815c4645664f9113a08a0c400815c4645664f9113a07f94e47815c4645664f9113a20577dc4645664f9113a0c7815c4645664f9113a0a4012057edc4645664f9113a0cf8e605711915993e444e80c61d815c4645664f9113a0318ca05711915993e444e80080082e05711915993e444e8815c46c591631664f9113a253815c4645664f9113a01200205711915993e444eb3a20579dc4645664f9113a0c70000081dc4645664f9113a20579dc4645664f9113a08100205711b66458c599113a247815c4645664f9113a0640024e815c4645664f9113a000815c4645664f9113a0a8815c4645664f9113a08a11205711bd645664f9113a06b815c4645865993e444e814c00815c46457f5993e444e8815c4645665853e444e81ae39815c4645664f9113a04400247815915993e444e806400815c4645664f9113ac048ca05711915993e444e802a057c9c4645664f9113a0c794e05711b1645664f9113a000815c4645664f914444e800205711915993e444e80160579dc4645664f9113a004815fb711915993e444e831e478ca05711915993e444e800205711915993e444f13a205711915993e444ed3a00600205809c4645664f9113a232815c4645664f9113a0120000083dc4645664f9113a2057b1c4645664f9113a099815c4645664f91a444e804a057c9c4645664f9113a004815c4645665853e444e81ba3f815c4645664f9113a0a4815c46458c5993e444e81ee3f815c4645664f9113a05a815fb711915993e444e8012057b1c4645664f9113a0a9815c4645865993e444e81ae32815c46c5915993e444e896653815c4645664f9113a00000205711664f9113a00e00205711915994b4f9113a20571191631664f9113a031815c4645664f9113a00a00605711915993e4cd113a0a400205711955993e444e804a53815c4645664f9113a07b00205711915993e444e80e205711915993e444e81800600209711915993e444e801205711b6645664f9113a0028fe0579dc4645664f9113a2057b1c4645664f9113a0530020571191631864f9113a00091e3f711915993e444e8815c46f5915993e444e831e0571191631664f9113a044815c4645664f916444e802a0571191599614f9113a0c794e05711915993e444e80c40000205711914f9113a00800000815c4645664f9113b400815c4645664f9113a0a600205711915993e444e83340091205711915993e444e800205711915993e444e81923f815f2711915993e444e8815c4645664f9113a08a18205711b6645664f9113a00a00205769c4645664f9113a23f815fb711915993e444e8815e7711915993e444e829239815c4645664f9113a060815ce711915993e444e81800000205645664f9113a01991e05711b6645664f9113a232815c4645664f9113a07b00205711915dd664f9113a205711bd645664f9113a004815c4709bd645664f9113a253815c4645664f9113a044815c4645665853e444e801205711b6645664f9113a01200205711915993e444e816605711915993e444fd3a053815d7711915993e444e82660571191599424f9113a012815f2711915993e444e829000815c4645664f91a444e88ca05711915993e444e80c6057edc4645664f9113a0a4815ec711915993e444e81ae05711915993e444e826406815c4645865993e444e831c00815f8711915993e444e800205711915993e444e8218000020571191599113a005815c46d9b1645664f9113a00086205711915993e444e8815c4645664f9113a00a00800815c4645664f9113a0338ca05711915993e444e811247815c4645664f9113a00200000815c4655664f9113a2057c9e7711915993e444e800205711915993e444e82fa05711915993e444e82648a00205711664f9113a00a01a0571191619664f9113a00400205719915993e444e801205711915993e444e804802815fb79dc4645664f9113a239815c4645664f9113a099815c4645664f92e444e82640000205711915993e44ce88fe05711bd645664f9113a00082dc4645664f9113a0068fe0571191599614f9113a00091e05711664f9113a00600205711915993e444e80060571191599524f9113a06b91e05711915993e444e802a05711915993e444e814c06815c4645664f9113a0310060571191631664f9113a060815c4645735993e444e81ee057edf2711915993e444e8815c4645664f9113a01202a05711b1645664f9113a00200205711915cd664f9113a000815c4645664f916444e8815c46d9915993e444e81ee53815c4645664f9113a07600205711b664566444e800a05711bd645664f9113a0a491e05711915993e444e804a0571191599614f9113a0a400205711915a93e444e804a5e94e05711915993e444e800205711915993e4a1113a205711b1645664f9113a06f815c4645664f9113a08a14c008ca0579dc4645664f8e80020571193645664f9113a253815c4645664f9113a06000205755c4645664f9113a000815c4645665093e444e8815ec711915993e444e831e0571191599554f9113a07b8e605711915993e444e814e05711b1645664f9113a00a815c46d9915993e444e80c605801c46d9915993e444e8815d2711915993e444e81ee057119159d664f9113a002815c46458c5993e444e81723f815c4645865993e444e891e05711b1645664f9113a000815c4645665553e444e800205749c4645664f9113a232815c4645664f9113a09b815e7711bd645664f9113a205711b1645664f9113a012815c4645664f9113a06b01a0579dc4645665853e444e8815c46d9915993e444e8112057b1c4645664f9113a004815c464590631664f9113a00088a05711915993e444e8815c4645664f9113a07b00a057e5f2711915993e444e8815c46458c5993e444e826400815c464566509113a012815c4645865993e444e829232815c4645664f9113a0608fa0571191599614f9113a2057c9c46f5915993e444e8815f271191599614f9113a205711915993e444e82286b815c46d9915993e444e80da057edc46f5915993e444e8815c46a9915993e444e81ae057edc4645665853e444e8815c4645664f9113a03100800815c4645664fd3e444e88e605711915993e444e81ae05739c4645664f9113a06b815c4645664f9113a07b02800815c4645664f9113a06f815f2711915993e444e803a53815c4645664f9113a09988a05711915993e444e811000815c4645664f911424e891e05711915993e444e81ee0579dc4645865993e444e8815c4645664f9113a07b04a05711915993e444e811002815c4645664f9113a0310280000205711915a93e444e8815f2711915993e444e819e0571191631664f9113a0538fe057b1c4645664f9113a247815c4645664f9113a031815c46456652d3e444e814e05711915dd664f9113a099815f271191619664f9113a2057fde7711915993e444e8815c4645664f9113a03104a057edc4645865993e444e8815c4645664f9113a04402a32815c4645664f9113a099815c46c5915993e444e81ee05711915993e444e831c068fe05711915993e444e82525894e05711915993e444e894e05711915993e444e814c00815c4645664f9113a06391e05711915993e444e8112057b1c4645664f9113a0a493632815c4645664f9113a205711bd645665853e444e800205711915995a4f9113a205711915993e444e811012815c46c5915993e444e80c40082605711915993e444e8815ff7edc4645664f9113a0008e632711915993e444e8815c46d9915993e444e818000002057119159942444e800205711915a13e444e802800815c8645664f9113a006815c4645664f9113a00601205711915993e444e831c8a815c46458c5993e444e81ae39815c4645664f9113a0c7815c4645664f92e444e831c00815c4645675993e444e800232815c4645865993e3a205711b1645664f9113a04496e53815c4645664f9113a2588ca05711915993e444e8815ec79dc4645664f9113a232815c4645664f9113a05300259815c4645664f9113a205711915993e444e8228048ca05711915993e444e812e53815c4645664f9113a06b8e605711915993e444e801000815c8711915993e444e800205711915993e444e81ee05711bc6d9915993e444e8815c46f591619664f9113a000815c46456653d3e444e8815c46457f5993e444e831e0571191619665853e444e8815f27b1c4645664f9113a205711915993e444e818002815c4645664f9113a07b0c6057edec711915993e444e800000815c4645664fd113a205711915993e444eb3a00491639815c4645664f9113a205711b6645664f9113a0999423f815c4645664f9113a00081600711915993e444e8815c46457a5993e444e82923f815c4645664f9113a006815c4645664f9113a06002a3f815c4645664f9113a09c815c4645664f9113a07b11232815c4645664f9113a06b0020579dc46c5915993e3a25e91e05711915993e444e8815c4645664f9113a05300605711bd645664f9113a0dc91e05711915993e444e81820571191599614f9113a0dc00205711915993e444e81120579dc4645664f9113a0908fe05711915993e444e822a05711915993e444e81801200205711b65993e444e802a0571191631664f9113a0c7815c4645664f9113a0a401a05711915993e444e81103100205711915993e450e801a3f8e605711915993e444e8, 0xd1810d141000000d101000000d0c1000000d0420cfc200000000000cf030ce430ce010cd82000000cd410ccc20cc81000000000000000000000cbc30cb810cb410cb01000000cac1000000ca810ca02000000c9820c9410c8c2000000c8810c7c30c7810c6c30c68100000000000c641000000c5c20c5810c5410c5010c482000000c3c30c3810c302000000c2820c241000000c2010c1c10c1810c141000000c101000000c0c10c0420c0010bfc1000000bf81000000bf410bf010bec1000000be42000000bdc20bd030bcc10bc810bc41000000bc010bbc10bb030bac1000000ba030b982000000b9410b883000000b7840b702000000b6820b6020b5c1000000b5810b4c3000000b4030b3820b3410b3010b2c10b2420b1c2000000b1810b1410b101000000b08200000000000b04100000000000afc20ae850ae4100000000000ae01000000ad43000000ac83000000ac41000000ac010abc1000000ab810ab0200000000000aac10aa030a9820a9020a8c10a8810a8410a7c20a7810a7020000000000000000a6c10a681000000a602000000a582000000a4c3000000a4810a3c30a3810a3020a28200000000000000000000000000a2410a2010a1c10a1420a1010a0c1000000a081000000a0410a00109fc10000009f42000000000009f0109ec10000009e4209d830000009d4100000000000000009cc209c420000009c010000009b8209b4109b01000000000009a8209a4109a01099c109942000000990100000098c10984209801097c100000097810974109701096c1096810964100000000000960109582095410950100000094c1000000000009403093c10930300000092c1000000000009242091c209142090c2090030000008fc1000000000008f8108f4108f0108e8208e4108e010000008dc108d4208cc208c81000000000008c41000000000008c01000000000008bc108b8108b0208ac1000000000008a420898308941088c208803087c10878100000000000874100000000000000000000086830000008641086010858208502084c1084810000008441083c20000000000083810834108301082c10828108202081c10818100000080c30804200000000000800107fc107f8107f4107f0107e8207e02000000000007d8207d0207cc107c8107c410000007bc207b4207ac2000000000007a42079830794107901078c100000078810784100000078010000007782000000000000000000000000007702076820764107601075c107581074c3074810744107401073c10000000000000000738107341072c20728100000072410720100000071c107181000000714107101070c10000007042000000700106f4306ec206e8106e4106e010000006dc1000000000006d8106d410000006cc20000006c420000006c0106bc106b8106ac30000000000000000000006a810000006945000000000006901068c1068810680200000000000000000000067c10000000000067810670200000066c1000000000006642065c20000000000065810000006541064c206481064410640106382000000634100000062830620206143000000610100000060c10608106041060010000005f8205f4105ec205e810000005e41000000000005dc20000005d4205d0105c8205c0205bc105b8105b4105b0105ac105a8105a020000000000059c10000000000059810594100000058c205881057c305781056c3056420000005601055c100000055810000005541055010000000000000000000005443053c2000000000005381000000534100000052c205281052410520100000051c1050c4050810500204f4304e8300000000000000004e020000004dc104d8104d0204cc10000004b8504b4104ac20000004a81049c30494200000048c20488104802047820000000000047020468200000045c30000004542044c2044810444104401043c1043810000004284000000424100000041c20000004181000000414104101040c1040810000000000040020000003fc103f8103ec30000000000000000000003e810000003e4103e0103d82000000000003d4103cc203c8103c410000003bc203b4203b010000003ac1000000000003a810000000000000000394503901038820380200000037c10374203683000000000003641035830354103501034c103481034020334300000033010000000000032820324103201031c1000000318103141030c2000000308100000030410000002f8302f4102f0102ec1000000000002e810000002e410000002e0102dc102d8102d0202c8202c0202bc102b420000002b0102a82029c30000000000000000298102941028c2028810284102801027c1027810000000000000000268402641025c20258102541024c202481000000244102383000000000002206021c10000002103020c1020810000002002000000000001fc101f8101ec301e81000000000001e020000001dc101d420000001cc201c8101c020000001bc101b8101b410000001ac201a4201a01019c10194201901018c101842000000180100000017c101781017410000000000017010000001682016410000000000015c20158100000000000150200000014c10148101441013c2000000000001342012c200000012810000001241011c201142000000000001101010c1010030000000fc100f4200ec20000000e0300dc100d810000000d410000000cc2000000000000c810000000c020000000bc100b03000000000000ac100a810000000a4100a01009c10000000000009420084400801007c100781000000074100701006820000000641000000000000000006010050400000000000000000000004c1004420040100343000000000000000002c20024200000000000020100143000c200042000000000100000, 839, 839⟩
def t3 : Archive := ⟨0x205711915993e468e800000815c46453e444e81c000815c4645664f9133a0a400205721664f9113a00a01800815c46c5915993e4a0e800247815c45993e444e815c00815c5645664f9113a00600205711b764566509113a000815f3715915993e444e80022c815c4645664f9113a000815c4645865993e444e80020571191599113a00a01400815c4645664f9143a00a00205645664f9113a05a02800815c4645664f9113a08a00205711b65993e444e8164008e605711915993e458e800230815c4645664f9113c400815e3645664f9113c40a00000815c464566501163a000002057c9c46453e44ce800209711b1645664f9113a000815c464d664f9113a0440020579dc4645664f91a3a000815c7645664f9113a00500205711b0645664f9113a000815c5645664f9113a03200205719c4645664f9113a000815c4655664f9113a07b002057edc4645664f91a3a000815f26453e444e80480400205711915994b4f9113a000815c46d99159952444e800205711955993e444e8048008e628711915993e444e800000815c7645664f9113a0008fe057edf26453e444e8002057119159940444e80c400815c46d9914f9153a00800205711915cd664f9113a0008ca05711915993e3a06d00205645664f9113a0a406400815c46458d5a13e444e800205711a8645664f9113a000815c4645865993e44ce800205711915993f444e802800815c4645664f9133a08a00205711955993e444e81800094e0f711915993e444e800205711915993e444e815000815c8645664f9113a03100209815c464d664f9113a0008fe05719915993e444e800205711b16453e444e802000815c4645664f924444e800205711915993e444f13a000815c6711915993e44ce800205719915993e444eb3a000815c85993e444e80380600205711915993e444e827400815c45993e444e83340600247815c4645664f9163a000815c4645665753e444e800205711915993e444e910400815c4645664f9113a005002057edf26f5914f9113a00083dc464566501113a00a0020b711915993e444e829000815c6645664f9113a06b00207711915993e444e814c008ea05711915993f444e80023f815c4645664f9113ac00815c464566509113a00400247875c4645664f9113a00091e3f711664f9113a00600000815c4645664f9113a00081591619664f9113a019002057c9c46457f4f9113a000815c66f5915993e444e800205645664f9113a08a06400815c45a13e444e80280600250815f2711914f9113a00091e28711915993e444e800205711915993e444ef02000815c4645664f9113c40400205719915993e444eb01000815c464566444ec3a00500205711915993e444eb1ac00815c4645664f9113a07d000008c9915993e444e8064008e609711915993e444e80020579dc4645664f9113a000815c4645664f9113a8320020578dc4645664f9113a000815c4645664f9133a00500205711915993f4f9113a000815f2645664f9113a03800205655664f9113a01904800815c46f5915993e444eb0020d815c4645664f9113a000815fb711915993e444e8002056c5915993e444e81300082dc4645865993e444e800000815c4645684f9163a00082dc4645664f9113a08a00205711664f9113a031038000020f711915993e444f100000815c4645664f9133a000815c4645664f911408e800205711915993e444e8360008ce09711915993e444e800205711915993e444f10f400815915993e468e80480a0020571192599614f9113a000815c464566444e81100500205711915993e450e811000815c6645664f9113a0990020571191599424f91a3a00000205711915b13e444e8002057a1c6645664f9113a00083dc4645665013e444e80023f815c4645674f9113a00090605711915993e444e8002057f1c4645664f9113a000815c4645684f9113a03100239815c46453e444e802000815e7711915993e44ce800207815c4645674f9113a0008ca0f711915993e444e8002057118c5993e444e82a800815c4655664f9113a0a4002057119159942444e80e00094e07711915993e444e800205711915993e444e81840092609711915993e444e80020f711915993e444e833400815fb711915993e44ce800205711935993e44d113a000849c4645664f9113a00e00232645664f9113a01202800815c4645674f9113a06b00205711915993e444eb26400815c4645664f9113a0360023f815c4645664f9113a400815c464566509113a00a0023271191599424f9113a000815c46f5b6599113a00200247825c4645664f9113a000815c4645664f9113a08100205711b65993e444e812800002057113e444e80280800000815915993e444e806400815c46d9914f9113a06500205711915993f444e811000815c4645664f9113c40a00205711bd645674f9113a000815f2711664f9113d00e00205711915993e444fa06400815ca711914f9113a00800205719915993e444e831c0083dc4645684f9113a00a002057c9ec6d991599113a000815f0711915993e444e800205711915993e444e91ac00815c46d992599113a0020020573dc4645664f9113a00000205711955993e468e800205711bd669664f9113a000815c4645664f9163a0060020579d915993e444e80640091e05711664f9113a0cb00247815c44f9113a00601000816007c9915993e444e800205711915993e444e822400815c4645665213e444e80020571192645674f9113a000815c4655865993e444e800205711bd645664f9113a400815c66d9915993e444e800205711955993e444e822800815fb645664f9113a0190000082dc4645664f9113a000815c46d991599113a0a500205711915fd664f9113a000815c4645664f9113acc700247815c46453e444e802000815c4645664f9123a00600250815c4645664f9113a000815c4645664f911418e8002057c9c66453e444e801000815c4645865993e444ec0020571991631664f9113a000815c46453e444e81bc04000008c9c4655664f9113a000815f2749915993e444e80023f815c4645664f91a3a00083e05711915993e444e800205711915993e444e810400815ec711935993e444e8002057119159d3e444e826400002056456c4f9113a01900205711bd6d93e444e80200082de7711915993e444e80020571dc4645664f9113a000815c46d9915993e444eb0020b711915993f4f9113a000815c4645665093e444e800205711914f913444e801800815c4651865993e444e80020b7edc4645664f9113a000815c4645664f914444e800205711915993e444e830c00815c4645664f91a3a06b002057c9c46453e444eb01000815c46458c5993e444eb00205711a1645664f9113a000815c4645664f9113a49900205711915993e444e801c00815c4645664f9113b40200205711bd645664f91a3a0008ca07711915993e444e800205711b8645664f9113a000815c464d664f9113a0080020571191599634f9163a000815f6711915993e444e800205711916193f4f9113a00083df2711915993e444e8002057c9c4645774f9113a000815c4645674f9113a0c70025391dfb711664f9113a00091e05645664f9113a04c002057119159913444e801400815d4711915993e444e800205711915993e444ec0140000205711955993e444e800205711c164566444e801400815c46d99159d3e444e800205711915993e444e805c0081dc5645664f9113a00200209711915993e444e801800815c4645664f9113a4c700205711b65993e444e82a400815915993e444e80480e002057119259d3e444e800800815c464566509113a04400250815915993e444e8064008c9c4645664f9113a01900000815c4645664f9113b000815c46458c59d3e444e800205711915993e468e826400815c4651664f9113a00500205761c4645664f9113a00091a05711915993e444e80020f815915993e444e806400815e7711955993e444e8002057119159942469113a000815c4645664f9113a0df00205715915993e444e814c00815c4645684f9113a05900205711915993e444f111000815c4645665493e444e800205711915993e444e821c00815fb7c9914f9113a00400205711b6645664f9113a400815ce645664f9113a0120023f815c4645664f9113a000815fb711955993e444e800205711915993e444e82f8008ca05711b6645663a002002077119159d664f9113a000815c464966444e80100200205711915993e444e82c40000205711945993e444e800000815c4645664f91e3a000815c4645664f9113ace800207815c4645664f9113a000815c46c5915993e444ed0020571191631664f9113a40083dc4645664f9113a09a0021c815c4645664f9113a000815c5645664f9113a04600205719915993e444e801000815c4645664f91a3a09000205711915993e444e81ac0000205711914f9113bc0800205711b1645864f8e801800815c46453e444e8020060020571191599113a0a501000815ec71191599113a005002057b1c4645664f9143a000815c46d99163186444e800205711915a9614f9113a000815c4645664f91a3a0c700232815f8711915993e3a000815c46f5915993e444e80023b83dc4645664f9113a000815c4709915993e444e80023f815c4645664f9133a000815c4645664f9113ac2d0020b711915993e451113a000815c4645664f9113ac0400232711915993e444e82400083dc4645664f9113a07b00205711b66c58c599113a000815c4645664f9133ace800205729b66453e444e802000815c4645664f9113a01900205711b6645664f91a3a000815c46d9914f9113a07000000815955993e444e80640083dc4645664f9113a01200205711915993e444fa3a000815ed721915993e444e8002077c9c4645664f9113a000815c4649915993e444e800205711b66c566444e829400815c6645664f9133a004002478c9fb711664f9113a000815c4645664f9133a06b00205711b164586598e801400815c46458c5993e468e800205711915a93e444e812c0090207711915993e444e8002057b1c4645664fd113a000815c464d664f9113a03100253815c5645664f9113a0008fe18711915993e444e800205711915dd664f9113a00083dc4645664f9113a06000205711b66a9664f9113a000815f27b1914f9113a05500000815c4645664f9113dc00815f271166505113a00e00205711bd645664f9133a000815c4645664f9113a09900205711915993e44ceb01000815e8711915993e444e80023f815915993e444e80640087e05711915993e444e800000815915993e478e806400815c46d9664f9163a00a00205711915993e444e93a000815c4645905993e444e8002057a5c4645664f9113a000815c6645664f9113a00a002057119159961501113a000815c46456c4f9113a01900205645664f9113a06b06400815c4645674f9113a00400239815c4645664f9113b400815c4645664f9113a0b900205711914f9113a05701000815c4645664f9113c44200205711bc645865993e3a00086605711915993e444e800205711915993f444e8020008ca057119159d3e3a0020025e815c4645664f9113a00081603711915993e444e800205655664f9113a01202800815c4645664f9183a00e00205775c4645664f9113a000815c4645664f9113a09000209711915993e444e804c00815c4655665093e444e80023f82dc4645664f9113a000815c8645665853e444e800247815c45993f4f9113a000815bd645664f9113a01900205711915993e4e5113a400815c4645664f9133a09900000815c8645664f9113b400815c4645664f9113ac0a002057a1c4645664f9133a000815c4645664f9113a42d00205711915993e444e9010000020571193599113a00200205711915993e444e831c00815c46458e5993e444e800205711915993e444ed080008ca0571191598e80100200205721915993e450e801800815c45993e450e8028060020b711915993e444e81ac00815915993e444fa3a01900000825c464d664f9113a000815c46d9915993e444e800205711915a93e444e819c00815c464566444e80cc0200207711915993e444e81ec00815c4649664f9113a0020020b711bd645664f9113a000815c4645684f9113a04a00207711915993e444e804800815f2711914f9113a0040020571191631664f9113a000815fb711a65993e444e800205711915993e444e90f40091e05711915993e444ed00205645664f9113a09906400815c4645664f9133a0c700205711915993e444e829400815c46453e455113a00800232815c5645664f9113a000815c464566501113a0a900205721915993f444e801800825c4645664f9113a0c8002057e5c45993e444e803800815c46d966444e80280200205711664fd113a00a0180083dc4645664f9113a0a400207711915993e444e81800000205645664f9113a05b00205711915993e458e80040093605711915993e444e800205711c3645664f9113a000815c4645664f91a3a00400205711915993e458e814c0000205711934f9113a008002057119159d3e444e802800815c46d9915993e44ce8002057b1c464566509113a000815c4599614f9113a00e0020571191599113a031014008c205711915993e444e800205711915993e450e80c400815e3645664f9113a00a00234815c4645664f9113a00097a05645664f9113a0190023f815c4655664f9113a000815c46dd915993e444e800205711915993e448e8004008c605711915993e444e80020b711915993e444e826400815c4669664f9113a00a00205711915993e448e814c00815f2711914f9133a004002057b1c4645664f9113c400815c46458c5993e44ce800247815c46d98c599113a00098605711915993e444e8002057c9c46453e444e81b800815c468d915993e444e800000835c4645664f9113a000815c4645664f9113a40a00247815fb5993e444e806400815c4645685853e444e800205711915993e445013a000815915993e444e831c19002057c9c4645865853e3a000815f4711915993e444e800205711955993e444e81ac0000205711664f9113d00e00205711915993e444e80b8008be05711915993e444ed00205711b1649664f9113a00083dc4645865993e444e800205711915993e444e833800815c4645865dd3e444e80020f711915993e444e82280088205711915993e444e800205719915993e444e811000815c5645675993e444e800205711915993f444e80c400815c46d93e444e802808002056d9915993e444e806400815c4645845993e444f100205711bd655664f9113a000815c4645664f9113c42f0000081dc4645674f9113a000815f2711914f9113a0630020b711915993e444e831c0081591631664f9113a019002057b1e76d991599113a000815c4655664f9113a0190024881dc4645664f9113a000815ec711b6599113a0a900205711915995f4f9113c400815c4645875993e458e800205711915993e444eb11000815c46f99159d3e444e800253815c4645664f9163a000815c4645664f9113a0e00020b711b6645664f9113a000815c4645664f91a3a00a0024d815915993e444e80640082605719915993e444e800205711915993e4e5113a000815c4645664f9113a05d00205711915993e444e80b400815c4645664f9113a0040020b71191631664f9113a000815c4645664f918444e8002057e1c45993e444e803800815c4655664f9113a09900209711915993e444e8004008c9c4645664f9113a03800232815c4645664f8e80080083dc4645664f9113c4e800207711915993e444e829000815fb739915993e444e800209711915993e444e814c00815c464566501163a00a00259815c4645664f9113a000815c46d9685993e444e800239815915993e444e80e400815c4645664f91e3a019002057c9c5645664f9113a000815c4645664f9113b40600209815c4645664f9113ac0087605711915993e444e900205711bf645664f9113a000815c45993e444e8204060025391dc46d9664f9113a000815f27b1916193e444e800250815915993e444e816c00815c45993e444e819c0e00000815664f9113a019018008de05711915993e444e800205711b664566444e826c000020f711915993e444e800205711664f9113c40a018008d20b711915993e444e800205711915995e4f9113a000815c4645664f9113a03d00205711915993e444e811400815c4645665653e444e800205721c4645664f9113b4008e605711925993e444e8002057119159d3e444e811000815c4645664f9133a00400205711915993e445053a000815f871191599113a03400222815c4645664f9113a000815c46453e444e80200100205711915993e444e81b800815c4645664f9163a00300205711914f9113a05302000815c4655664f9113a0c700205711b65993e459113a00081dc4645865993e444e800205711915993e4ad113a00083de7711915993e444e800207711915993e444e82280000205711915993e458f10020f7edc4645664f9113a000815c4645664f9113a44400205711915993e444e819800815c46d9955993e444e800232815c4645664f8e822c0091e05645664f9113a03900000815c46453f444e802000815c4645664f9113a0380020571191599404f9163a000815c464566509113a031002057c9c85993e444e80380083e05711664f9113a0060020571191631734f9113a000815c4645664f9113c42400205711915993e44ce811400815c46558c5993e444e8002055993e444e80480a01800815c4645664f9113a00a0024e815c46453e444e819400815c4645664f9113a06300253825c4645664f9113a000815c46c5916193e3a06f00205645664f9113a0190100000205715b664566444e800205711915993e44ce81b8008ca05711915993e458e80024183dc4645664f9113a000815c4645664f9113c4310021e815c4645664f9113a000815c46456a4f9113a00200205711915993e444e816c00815c4645664f92e3a00200205711915993e4450e3a000815c6645664f913444e8002057b1c45993e444e82a80083dc4645664f9113a06100205711915993e444f10e8008ca1d711915993e444e800247815c4649664f9113a000815c5645664f9113a07b00205711915993e444e825000815c5645664f9113a0120020f711915993e444e8204008ea05711915993e444e800205711b7655664f9113a0000020f645664f9113a01900205711915a13e458e802800815c46d9914f9113bc080020b711915993e444e801000815c4645664f91a3a0440020f711915993e444f102800815c4645664f9113a0e400205711915993e44ce802800815c4645664f913444eb00205711915993e44ce818c0091e32711b65993e444e800253815c46453e444e8020008fe05645664f9113a05b00205715915993e444e81800082dc4645664f9113b40600000815c464566511113a000815c4645665293e444e800209815f2711914f9113a00000207711915993e444e800205711915993e4bd113a000815c4645664f91143ce800256815c4645664f9113a000819c4645664f9113a0060020571993645664f9113a000815c4645664f9113a00e00207711915993e444e81f4008c9c4645664f8e80480200205801c4645664f9113a000815c46f9915993e444e800000815c459941444e80380081de7711915993e444e800205711915993e445003a000815c464566501113a00200205711915993e444e821800815c464566444e826c04002057b1c6645664f9113a000815c46c5915a93e444e800205711915993e444e81cc00815bd645664f9113a05b002077edc4645664f9113a000815915993e444e80640a00205711916193e444ed0180087605711915993e444e800205739c4645664f9113a000815c4645664f9113a0db002057c9c45a13e444e803800815c464d665853e444e80020f645664f9113a012028008ca05711915993e4a0e800205721915993e444e800800815c464d915993e444eb00205711915993e444e817800815d2711915993e444e800205711915993e444ec3a0008a205711915993e444e800205711915d1664f9113a000815c4645664f9113a00b0020571191599574f9113a000815ec711915993e444eb00232825c4645664f9113a000815c4645664f9113a05800205711915993e444e837000815c4655915a93e444e800000815c5645674f9113a000889c4645664f9113a01200205711955993e444e801000815c46456859940444e80020b711915993e444e802800815f2711915993e458e800205711b6689664f9113a000815c46453e444ef3a00800205711915993e444e811000815c46fd955993e444e8000008159159944444e806400815c46d9915994f444e800205711664f9113a01901800815c46b9915993e444f100205711915993e444e831400815c4645664f91a444e800205711925993e444e801800815c46c9935993e444e800232815c46453e444e802000815c46c59159940444e800205711b6699664f9113a0008ea0b711915993e444e8002478fdc45993e444e832c00815c5645664f9113a0a400205711915c5664f9113a000815c46456650116444e8002057c9c46453e44d113a000815c86c5915993e444e800000815c46d9684f9113a000815c45993e444e80380200205711915993e444e837400815ec7119159d3e444e8002057c9c4705914f9113a000815f7711915993e444e800209815c4645664f9113a000815e6711915993e444e800205711915993e44ce8110008e605711915a93e444e80023f83dc4645664f9113a000815c4645664f9113a0b500205711915bd664f9113a40095a0b711915993e444e800205785c4645664f9113a000815f275d915993e444e800205711915993e444f73a000815c4645684f9113a00200205711916216a4f9113a000815ec711915993e444e9002057b5c4645664fd113a00083dc4645664f9113a06b00247815b65993e444e806400815c5711b664566444e800205711955993e444e802800815c5645865993e444e800205711b664d3e444e802000815c5645664f9113a08a00205711685993e444e803800815c464586599113a0a7002057119159961444e801400815c4645665853e450e8002057c9c464d914f9113a0008ca05645664f9113a04c00209815c4645664f9133a000815c4645664f9163a07b0020f711bd645664f9113a000815915993e444e81641200205645664f9113a0440640000205711915993e450ed00205711915993e444e818800815fa711915993e444e8002097c9c4645664f9113a000815c4645664f9163a01200205711916193e444e80380093a32711915993e444e80020d711b6645664f9113a000815c4645664f926444e8002057b1c46d9b1599113a000815c4645664f9113a09b0020f711915993e444e806400815c46457e5993e444e800205711915993e444ed00400815c8645664f9113b4e800205711b15993e444e80380091e05711915a93e444e800205711915993e444ed14c00815c4645664f9163a06000239815c464566501113a000815c4679915993e444e800205719915993e444e80c400815c4645664f9113a042002057b1c4645664f91a3a00082dc4645664f9113a0440020571191599614fd113a00091e05711664f9113b4060023f815f27b1914f9113a000815c4645664f9113ac2400239815c8645664f9113a000815c46c5915a13e444e8002057119c645664f9113a00000205711915993f444ed0020f711915993e444e826400815f2711b1645864f8e8002057c9c46453e444e802000815c4645664fd143a00600205711915993e444e817000815c4645664f9113ac3100205711915a13e459113a000815c464d66444e80100200205711915993e44d113a0008fe07711915993e444e800000815c5645664f9113a000815c4705915993e444e800209711935993e444e8010008ca05711915993e3a0320024e815c4645664f9113a000815c464d664f9113a0a6002057c9ec6f5914f9113a0000020571191599113a0a700205711915993e444f70e000815f871191599113a00500207711915993e444e81ac00815fe711915993e444e800247815c464566501113a000815f277d915993e444e800236815c4645664f9113a000815c57119159d3e444e800205711915993e444e825800815e7715915993e444e80020f711915993e444e831c00815c4645664f9113a0a200205711915993e4d5113a000815d5711915993e444e800209711915993e444e81ec00815c45993e444e81fc0a00205711915993e444e82f00081602711664f9113a00e00000825c6645664f9113a000815fb715915993e444e800253815c4645664f9113b400815f2645664f9113a0cf00247815c8645664f9113a00081dc46f5915993e444e800205711915993e444e835400825c4645664f9113a0120020f711b6645664f9113a000815c464d915993e444e800205711915bd664f9113a000815c4655664f9113a044002057119159d3e444e80c400815c464566511113a01900239815c45993e444e803800815c464d3e444e80200400205711664f9113d0e803800815c4645664f9113a0d10020f71191631664f9113a000815ec711915993e444e80020771192645664f9113a000815c4655664f91a444e800209711915993e444e81800000209711915993e444eb00205711915993e444e909000815f2711915e93e444e800000815c46453e444e816000815fc715915993e444e800205711915993e458e829000815c4645113a0060100200000815c85993e444e8038008e605711915a13e444e800205711915993e444e90c400815c46453e444e81ec0800000815c464568501113a000815c46456a4f9113a00600205711915993e448e829000825c46453e444e80180400205711b66453f444e802000815c46453e444e80480800207711915993e444e826400815f2645664f9113a04b00205711915993e444e90e800819c4645664f9113a0010020571193645664f9133a000819c4645664f9113a05300205711915993e4ed113b400815c464567444e801402002057119159961509113a000815c4645845993e444e800205711915993e444e80bc00815c46ed915993e444e8002057edc46453e444e81600000205711915993e444ea0024e815915993e444e806400815c4645664f9113a008002057b1c4645664f9133a000815c4645664f9113a0af00205711b664566444e81b400815915993e444e81281200205711914f9113a0600200091e057b1c46d966444e800205645664f9113a03802800815c4645665853e444f100205711915993e444e81dc00815c4645664f9113f8e80020571191619664f9163a000815c46456657d3e444e800205711915993e444e82200091e05711664f9113a00e0024781600711664f9113a000815c4645664f9163a08a0020571191635664f9113a000815c4645895993e444e80000083dc45993e444e801800815e7711915993e444ea002478fdfb711664f9113a0008e63271191619664f8e800205711915993e444e82b800815c4645664f91a3a03100207711915993e444e831c0091e05711915a13e444e800205711915993e444e81f000815c46456653d3e444e800232815c4645664f9113b400815c464d664f9113a09c00205711935993e444e800800815ec645664f9113a01900232815c4645864f8e801800815c4645664f9113a0b6002057119159940444e80180081dc46d9915993e444e800207711925993e444e800800815c46c5915993e490e80020771191631664f9113a000815c8645664f9113a006002057f5c464d664f9113a000825c4645664f9113a0a400205711915993e444e81b00000205711684f9113a00e00205711915993e458f13a000815c4649664f9113a0530020f711915993e444e801000815c4645664f9133a07c0020b7b1c4645664f9113a000002097c9c46453e444e800205711915e9664f9113a00091e3271191619664f8e800205711915993e479113a0008ca0571191619663a00500205711915993e444e82600000205711915993e458e8002057119b645664f9113a000815c5711915993e444e800205711916196f4f9113a000815c4645664f9113a08400212815c45993e444e803800815c46453e444e82900800205711ae645664f9113a400815c4645665713e444e8002057119159d3e444e81b400825c4645865993e444e800205711915993e444e80900000205711915993e448e800205711b164d664f9113a000825c4645664f9113a08a002057119159963501113a000815d1711915993e444e80020579dc4645664f9163a000815c4645664f9113a03100205795c4645664f9113a000815c4645664f9113a04f002057edc4645664f9163a000825c6711915993e444e80023f815c5645664f9113a0008e63279dc4645664f8e8002057c9915a93e444e804800815c4645664f9113a03a00205711664f9113a00e01800815c46cd915993e468e800221815c4645664f9113a00081e05715915993e444e800205711915993e4a5113a00094e05711925993e444e800205715915993e444e81ac00815c4645864f9113a008002057c9c4645664f9113b400849f2711664f9113a00e002057c9ec6453e444e801000815c4645664f9113a0ca00205711914f9113a08a02000815ec711955993e444e80020f711915993e444e802800815c4645684f9113a00600205711915993e444e830800815c8711664f9113a00e0025f815c4645664f9113a000815f9711664f9113a0aa00205711915993e44ce80c400815c464566444e80140200205711915993e450e800800815c56f5915993e444e800205711915a942444e804800815915993e479113a019002057c9c4645664f9113d000815c46f591599113a0a700205711915993e458e82040000232815c4645663a00500207711915993e444e80100082dc8645664f9113a0060024e815ec71191599113a00090a05711915993e444e800223815c4645664f9113a000815c46f1914f9113a0700023281dc4645664f8e80080091e057119e5993e444e80020b711664f9113a00a01800815e775d915993e444e800205711915993e458f102800815c46456a59942444e80020571592645664f9113a00091e3279dc4645664f8e800205711915e5664f9113a00000209711915993e444e800205711915993e444e81c400815e0711915993e444e8002057e5c46d991599113a000815c4645664fd113a00200205645664f9113a031064008e605711935993e444e800205711ad645664f9113a000815c5645664f9113a09900205721916193e444e801800825e7711915993e444e80020571191631865853e3a0008ca05711915993e3a04600205711864f9113a00a01800815c4645664f9113a04d0020b815c4645664f9113b400825fb711915993e444e800226815c4645664f9113a00083e05711915993e458e800205711b3645664f9113a000815c4645664f9113a08300205711916197a4f9113a000815c46c591599113a00500205711b1645664f9143a000815915993e458e80480a00000825c4645664f9133a00081a05711915993e444e800000815c46453e444e80200082dc4645664f9113a0310020571991599614f9113a00083d915993e444e80640a00205711915993e444ed1ec008e205711915993e444e800232815c4649664f9113a000815c46457d5993e444e800205711914f9113a07d02000815c4645664f9113b41200205711ae645664f9113a000815e7711914f9113a00800249815c464d664f9113a000815c46a5915993e444e800205715915993e444e831c00815c46d966501113a00a00207711915993e444e80280097205711915993e444e800205711914fd3e444e802000815c4645664f9113a03f0020571191599614f9113ac00815d6711915993e444e80020d815c46453e444e802000815fb711914f9113a00800247815c464d664f9113a0008f205711915993e444e800205711915993e444ed18000815c46c5915993f444e800205711bc645664f9113a000815c46456659142444e80024c815c4645664f9113a0008d605711915993e444e800205715b6645664f9113a000815c4645664f9113a06d00255815c6645664f9113a000815c4645664f9113a05900205715925993e444e8008008e605711915994b444e800205711915a93e444e814c0083dc4645664f9113a044002057c9664f9113a01203800815c4645805993e444e80020571591631664f9113a000815c4645835993e444eb00205711915ed664f9113a000815c4645785993e444e800205711914f9113b40601000815c465191599113a00500000815915993e444e813000815c4645664f92c444e8002057b1c46456653d113a000815c4645664f9143b4e800205779c4645664f9113a000815c4649675993e444e80020571191619664f9333a000815c46453e444e80d80800253815c45993e444e833800815c4645664f9113a03500205711955993e444e80c400815c45993e444e80cc0e00247815c45993e444e8020008fe05711915993e458e80020571191599444f9113a000815c464566509113a002002057119163166555113a000815c4645675853e444e800239815c464566444e8014008e605711915993e450e800205711915993e444e81e00096247711915993e444e80023f875c4645664f9113a000815c46d9914f9113a05800205711915993e444f100800815c46458b5993e444e800260815c4645664f9113a000815c4645664f9163a06b00205711915993e450e819000815c46d991631113a00800205711b65993e444e83340000205721915993e450e800205711915993f444ed3a000815c4599414f9113a00e002057119159940444e800400815c4645665853e444e900205765c4645664f9113a000815f8711664f9113a082002057119159940444e814c00815d7711915993e444e800205711bd645664f9163a00091e3f711b65993e444e800252815c4645664f9113a000815c4645664f9113a0e300253815c46456a4f9113a000815c8645664f9113a001002057c9c4649664f9113a000815c45993e444e82a00a00205721915993e444e814c008e605711915993f444e800205711b65a13e444e802800815c4645664f9113b4a4002057119160d664f9113a400815c4645685993e444f10020571191599113a07f01400815c4645664f9143a07f00205711b664567444e80080091e05721664f9113a006002057c995645664f9113a000815f27119159941444e800000815c8645664fd113a00091e0571191599113a00500247815c4645664f9143a00081dc4645664f9113a04400000815c45993f444e802800815c464d664f9113a00600205711b164566509113a000815c4645665953e444e800205711915993e458e826400815c4645665853e468e800205711915853e444e81c000815c5645664f9113a00400205711b1645664f9113c40081591599444f9113a01900225815c4645664f9113a0008ca05715915993e3a00200205711915993e444fd3a0008fe05711915bd3e444e800205711915993e444e811c00815c46e5915993e444e800205711915993e444e82a800815f2711664f9183a00e0020579dc4645664f9333a0008c9c4645664f9113a0cf00205711915993e459113c4008fe09711915993e444e80020571191619664f9113b400815c664566444e80100200205711915993e444e82340000205711915a942444e8002057119564566509113a000815c46cd955993e444e800205711915993e444ed22800815c4675915993e444e800205645685993e444e804800815c4669915993e444e900209711915993e444eb3a00094e057119159940444e800205711914f9113a00e0100091e05711915993f444e80020d711915993e444e802000815c46e9915993e444e800205711664f9113a00e004008ca057119159d664f8e8002057b1ce645664f9113a000815c4645664f91a3a04b00209719915993e444e801000815c45993e444e814c0e002057b5c4645664f9113a000825c4645664f9113a06b002057b1d2645664f9113a00094e05721915993e444e800205711915993e444e812800815c464566444eb0100200205711bd6456f4f9113a000815c4645664f9163a0c700239815c464566521113a000815c4649664f9113a07b00209711bd645664f9113a000815c46456a4f9113a05a00205711915a13e444e800400815c4645684f9113a0530023f815c46453e444e80200096a05711915993e444e800205711915993e4450a3a000815c4645664f9113a8e800209711915993e444eb010008ca05711915a93e444e800205711925993e444e804800815c46d9915993e458e80024b815c4645664f9113a000815df711915993e444e800205711c0645664f9113a000815c46453e444e81ac080020571191631664f9163a000815f9711915993e444e800205711925993e444e818000815c4645664f9113a0cf00207711915993e444e826c008e6057119159942444e800205715915993e444e802800815c4645664f9113a04c0020f7b1c4645664f9113a000815c4645665853e444e800205711bd6453e444e802000815c4645664f9113a08200239815c4645664f9113c400815c4709914f9113a00800209711915993e444e826400002057119159940444f100206711915993e444e82900000212711664f9113a00e002057119159d113a00400800815c46458a5993e444e800205711b5645664f9113a000815c464566444e80180500000815c4645664f9153a000815c4645664f9113a0e600205711915993e450e80180094e05711664f9113a00e00205711915993e468e819c00815c4645665513e444e8002057119160d664f9113a000815c4645664f9113c4200020579dc4645664f9113b40000205711915993e444f400243815c4645664f9113a000815f2711664f9113a0ce00232815c464566501113a000815c4645664f9113a04b00205711915993f4f9113b400815c4645875a13e444e80024a815c4645664f9113a000815fb711915993e444ed0024e8fdc4645664f9113a000815c8711915993e450e80020571191599614f9133a00094e05711915a13e444e800255815c4645664f9113a00000207715915993e444e800205711914f9113a099020008c9c4645664f9113a0670020a815c464566444e801400002057119259d3e444e800232815c8645664f9113a000825c4645664f9113a0c700247815c464566509113a00095205711915993e444e800205711b664566444e800800815c4645664fd113a00600248815c4649664f9113a000815c46c9915993e444e80000091e057113e444e802000815c464568501113a00a00247815c4645664f9113c400815c4645665893e450e800205711915993e444e803000815f271191444e80100200205711915993e444e829c00825c46d9915993e444e800205711915993e444e82a400815fb7c9664f9113a00e00205719915993e444e800800815c4669915993e444e8002057c9c46456a4f9113a000825f2711914f9113a00400205721c4645664fd113a000825c46458c5993e444e8002057c9c46453e444e82980081591599614f9113a01900205711915a93e468e804800815f8711915993e444e800205711925993e444e829000815c46453e444e831c080020571191599554f9113a000815fd719915993e444e800205711b2645664f9133a000815c4645664f9113a0d6002077b1c4645664f9113a000815c4645664f9163a00400205711915993e444eb0080083dc45993e444e80280600205711915a9664f91a3a000815c4645665893f444e800205721915993e444e815c00815c46d9914f9113a00800205711915993e444e819c008c9c46456a4f9113a01200205711915993e448e80100000205711915a13e444f10020b71191599614f9113a0008ca05711664f9113a00e00205801c46453e444e816000815c5645664f9113a04400227815c4645664f9113a000815c46c591631864f8e800205711916313e444e8020000020b711915993e444ed00205711915993e444e805000815c4645664f9113a0bb00205711915a1404f9113a0000020f711915993e458e80020b711915993e450e80180097605711915993e444e80020571192619664f9113a000815f9711916193e444e800000819c4645664f9113a000815c4649664f9113a08a00205711915993e444ed104008ca05711915a13e444e800000815664f9113a01203800815c66c5915993e444e800232815f2711916193e3a000815c4645664f9113a051002057c9c464566501113a000815c4645664f911424e800205711684f9113a00e0280083dc4645664f9113a03100205711915993e451113b40000205711916193e444ed002057119159d3e444e800800815ec755915993e444e8002057c9c8645664f9113a000815c46b1915993e444e800205711aa645664f9113a00000205645684f9113a0120020571191619113a00601400815c4645864f9143a00600205711b1645664f9113ac000020d711914f9113a00800205711915a93e444e81ec0082dc4645664fd113a006000008ca057119159d3e3a000815c464566509113a00600205711915995a4f9113a000815c4695915993e444e800205711915993e444eb0f80096e05711664f9113a0ce00205711915a93e444e804800815c4645664f9163a00a002057a9c4645664f9113a000815c4655664f9113a0cf00205711915993e444e900800815ef711915993e444e800000815915993e444e80e400815c4645664f9113c40600205711915bd3e444e801000815c4645665913e468e800205711935993e444e800400815c46456a5993e444e80020571195599614f9113a000815c464d664f9113a05300205711915993e448e802800825c4645664f9113a00400205711915a93e444e818000815c4645664f9113a0a600205711916193f444e8018008e605711914f9113a0650024d815915993e444e813000815c4645705993e444e800205711915993e4b5113a000815f2711914f9113a09c00205711915993e444e82fc00815c4645664f9113a0e200239815f27b191599113a00000205711925993e444e800205711b66c566444e800800815c46456644ce80100200205711915993e444e82c8008ee057119159940444e800205711b1645674f9113a00082e05721915993e444e800205711915993e444e835c008fe05711915993e444ed002057c9c45993e444e80380081dc5711915993e444e800205711925993e444e81f4008e605719915993e444e8002057119159940444e81ec00825c4645664f9133a00400205711914f9113a00801000815c4645664f91a3a0020020579dc4649664f9113a000002057119159941444e80020571191599494f9113a000815c46c59a5993e444e8002057119159940444e804800815fb711925993e444e800000815c4645113a00601400815c4645664f9113b46b00205711b1645664f9113a400815c8645664f9113a07b002057c9c4645684f9113a00081dc4645664f9113a03100205711915993e4f1113c4008e605711915993e444eb00205721915993e444e80480093e05711915993e444e8002057119159940444e818000815c46f5915993e444ed00247815c46453e444e81940000205711664f9183a00e002057c9c464566444e80d00094e05711935993e444e800205711b66c53e444e802000815fc711925993e444e800209711915993e444e802800825c4645664f9113a06300205721915993e444e818000815c470591599113a0a70020571191599644f9113a000815c4645664f9113ac2000205711915993e444e80dc00815c4645664f9113a0b700247815c6645664f9113a000815c46456a4f9113a0a400205721914f9113a00601000815c46f5b663166444e800205711664f9113a0cb02800815c44f9113a00a018040020574dc4645664f9113a000815c46c5915993e468e800205711b16453e444e81c000815c4645664f9163a0440023583dc4645664f9113a000815c464566444e80140100205711915993e450e800400815c4645664f9113b49900205711915993e4450b3a000815c464566444e814c0500205711915993e450e814c008ca05711915993e490e800205711915993e4d1113a000815c46453e444e80280800247815c4645664f9113ac008e6057119159d3e444e800205711664f9113a07b03800815ec715915993e444e8002057c99159942444e80480000247815c45993e444ed00205711915993e444e8270008ca05711915993e3a00500205711915993e444e838400815c4645664f9113a00200205791c4645664f9113ac00815ec79db1645664f8e800205711664f9113a0120380091e05711664f9143a00600000815ca645664f9113a00000205711915a93e468e80020571195645664f91a3a00000205711915993f450e800205789c4645664f9113a000815c46456656d3e444e800239815c4645664f9113a400815f2769915993e444e800205711916196a4f9113a000815c4645684f9113a07b0020571191619664f92e3a000815fd711915993e444e800205711915a93e444e822800815c45993e444e81800e00205711915993f444e82a000815c4645664f9143a06f00205711915993f444e800400815c4645684f9113a01200205711915993f444e814c00815ec7119159955444e800205711915993e444ed31c008ca05711915993e3a07d0020a7119161966444e8014008c9c4655915993e444e8002057119159940444e829000815c46ad915993e444e800205711915993e444e90800091e05711915993e444fa00205711915a1664f9113a000815c4645664f9133a00200247815c46d966444e800800815c4645684f9113a06000247815c45993f444e8018008ca05711935993e444e800229815c4645664f9113a000815c46556a4f9113a01200205711915993e444e80e400815ec711b6645113a00800205711b6645664f9113b40096e05711664f9113a00e00000815c45993e444e833800815c8645664f9113a0a400247815c4645674f9113a000815ec711914f9113a058002057c9c46193e444e803800815c46d9915993e454e800205711b65993e444e820400815c4645664f9113a07a00205711955a9664f9113a00081600711914f9113a0080020571191631664f9113b400002056d9664f9113a01900253815c464566444e80140094e05711915993e450e800205711915993e444e822c0091e057119a5993e444e800205711b65993e444f10280089205711915993e444e800239815c4645664f91a3a000815c46c5915993e444e800205711915993e444e839c0091605711915993e444e800247815c4645664f9113a400825c4645664f9113a0440023271191619664f8e804800815c4645664f9113a03e002057119161966501113a000815c4645664f916444e80020571191621664f91a3a000815915993e444e80640200205711915993e444e831000815c4645665353e444e8002057119159940444e822800815c46d991599113a03200205711915993e444e82b400815c6645664f9113a00600251815c4645664f9113a000815c4645664f92a444e800205645664f9113a04b028008fa0571191619664f8e80020572191619664f9113a00091e05711b64f9113a00800250815c46d9664f9113a000815c4645664f912444e800000815c46456a4f9113a000815c4655915993e444e800205721915993e444e822800815c4645664f9113a07500253815c4645664fd113a00083e05711b65993e444e800205711b1645664f9133a0008fe05711925993e444e8002057b1c464566569113a000815b65993e444e80480a00205711915993e444eb018000020a71191599113a0050020b711915993e444e800800815c4645664f9113a0c100205711914f9113a04402000815c4645664f9113b42e002057c9c46f5b64f9113a000815e7711915a93e444e800207815c4649664f9113a000815c45993e444e82900e00205711915993e450e800c0091e05645664f9113e8190020579dc4645664f92e3a000815c4645664f9113a01500247815c4645664f91a3a000815fb711915a93e444e800205711925993e444e81ac00815c4645664f9113a0ab0020571194645664f9113a000815c464566501113c4e80025391d915993e444e806400815c464566509113a05300205711915a13e444e82900081602711915993e444e800205711bd649664f9113a000815c4645664f9113a076002056c5915993e444e806400815c4645664f9113c40100205715915993e444e80c400815f2711935993e444e800205711915993e444f114c008ca0571191599113a09d0022d815c4645664f9113a4008e605711915993e444e800232815c464566444e8014008ca05711915993e450e800205711915993e444f43a000002057119159940444e800205711915993e444e831800815c4645664f928444e800205711865993e444e803800815c45993e444e82280e002057119159d3e444e801800815c4645664f9113b404002057cdc4645674f9113a00096205711915993e444e80020571191621664f9113a000815c4645664f9113a06400205711664f9113a0a90180000205721915993e444e80023279dc4645664f8e804800815ec711915993e458e800205655915993e444e80640082dc46c5915993e444e800205711915993e444e808000815e77119159940444e800233815c4645664f9113a000815c4645865a13e444e800205711925993e444e826400815c4655664f9113a00200205729c4645664f9113a000815c4645684f9113a08a002057edc464566501113a000815c4645664f9113a4060020f71191599614f9113a0008e605711915993e44ce80020579dc8645664f9113a00091239711915993e444e800232815c4645664fd113a000815c8645664fd3e444e800205711915995e4f9113b400835c46d9914f9113a008002057119161966444e80d000815c45993f4f9113a00a002057edc8645664f9113a00092605711915993e444e800205711915993e444e81fc00815c464566444e80c80400209711915993e44d113a000815c464567599113a00500253815c464566509113a00091e05711915993e444e8002056d9915993e444e80e4008ce05711915993e44ce800205711915993e444e839400815e4711915993e444e800253815c4645664f9113c400815c46456654d3e444e8002056456a4f9113a01202800815c4649664f9113a0c700205711a2645664f9113a000815c464566501113a036002478c9915993e444e806400815c46456a5093e444e800000815f264566509113a0008e605645664f9113a01900205711915a13e444f13a000815c464d664f9113a07b00000815c664d664f9113a000815c46d9664f9113a01900000815c45993e444e803800815c4645664f91a3a00600205711a0645664f9113a000815c4645664f9113a0d2002057119159940444f102800815c464d91599113a0020020b711915993e444ed3a000815c4645664f9113b40a00205711b6649664f9113a000815c464d664f9113a01200239815ec79d91599113a000815dc711915993e444e800205645664f9113a06406400815c4699915993e444e800247815c4645664f9133a000815c46c5955993e444e800247911c4645664f9113a0009120571191599113a09d00244815c464566444e801400815f5711915993e444e80020971193645664f9113a000815c46498c5993e444e8002057fdc4645664f9113a000815c6645664f9113a03300205711914f9113a0550180091e05711915b13e444e80020579dc45993e444e80380093a05711914f9113a00800000815c4645684f9113a0008fe05711664f9113a0ce00205711935993e444e818000815f271191599113a00500000815c464d664f9113ac00815f2711915993e450e80020571191615664f9113a000815f2645664f9113a05a0023982dc4645664f9113a000815c4645665613e444e80022f815c4645664f9113a000815c4649664f9113a0a5002097b1c4645664f9113a000815fb711664f9113a00e00205711915993e458e81b000815c45993e458e80280600205711916193e444ed3a00082dc4645664f9113a06400205711b663166444e8028000020571191599113a03400000815c46556a4f9113a00083e057119159940444e80020579dc4645684f9113a0000020b721915993e444e800205711915993e444eb0cc00815c464d3e444e8018040020771191599614f9113a0008159159940444e80480a00206711915993e444e801000815c464566444e802002002057edc4645684f9113a00091e05645664f9113a0190022d815c4645664f9113a000815c464d914f9113a00800205711915993e444e82cc00815e771191599113a03400212815c4645664f9113a000815f2711915993f444e80020571191599404f9113c4008ca057119159942444e8002057b1c46453e444e8020008fe05711915a93e444e800205711915993e495113a000815c4645864f9113a0640020b711915993e444e81fc0090605711915a13e444e800205811c4645664f9113a000815c8645664f914444e800000815c8645864f9113a0008ca05711915993e444f10024782dc4645664f9113a000815c46456a4f9113a06b00205711915993e458e80c40000205711915993e444ef0020b815c4645664f9143a000815c4645664f9113a006002057cdc4645664f9113a000815c4645664f9113d00e0025481dc4645664f9113a00081dc46d991599113a00200239815c4655664f9113a00091e056456c4f9113a01900205711bd6456a4f9113a000815c4645664f9123a0310023f815f27113e444e803800815c4645664f9113a032002398c9ec71191599113a000849f2711915993e444e800205711915a13e444f102800815c4645865993e490e80020571191599113a07b01400815c4645664f9143a07b00205711915993e445033a000815c8711915993e444e8002057119161967444e801400815ca6d9915993e444e80020571191599113a01201400815c4645664f9143a0120020a815c4645664f9113a000815c464d664f9113a0a40020f711915993e458e802800815c4645664f933444e80024d815c46d9664f9113a000815c4649664f9113a0040020b815c4645664fd113a000815c4645664f9113b44400206711915993e444e802800815c4645664f9133a00600205719915993e444e800400815e7769915993e444e800232815c4649664f8e8008008fe057119159940444e800205719915993e444e814c00815c4645665393e444e800000815f2711934f9113a000815c46d991599113a04600205741c4645664f9113a000815c464566444e8180050020571191599624f9113a000815c4645664f9143a060002057c9c46f53e444e803800815f2645664f91a3a01200000815c46193e444e8038008fe05721915993e444e800205711915a93e444e82640083e05711915a13e444e800205711915993f444e81ec00815c464566501113a06b0021b815c4645664f9113a000815c4645664f9113ac0100205645684f9113a01202800815c46456658d3e444e800205711915993e444eb14c00815c46453e450e80180400247815c4655664f9113a000815c4645664fd113a0120025b91dc4645664f9113a000815c4645664f93c444e80020571193619664f9113a000815c8645664f9113a06b00205711bd64566501113a000815f271191619113a00500205711935993e444e822800815915993e444e806406002327c9915993e444e804800815f27119159942444e800205711915993f444e818000815c6711935993e444e800205721bd645664f9113a000815c4645665593e444e800209711915993e444e80c400815c4645665091a3a012002057c9915993e444e828400815f2711915993e444f100205711915a93e444e831c00815c46458e5a93e444e800247815c4645664f91e3a000815c4645664f9113a08e00000815c464567444e801400815c4645825993e444e800205711914fd113a0060100091e05711664f9113b4e80020b711915993e444e80180081dc4645674f9113a00200239815c4645664f9113dc00815c4645664f9113a0da00205711915993e444e821400815c4645664f911410e800205711915993e4c9113a000815c4649664f9113a00a00253815c6645664f9113a000815c46d9915a93e444e8002327119159942444e804800815c464566501113a099002057119159d3e444e814c008fe05711664f9113a00e002057e1ec645664f9113a000815c4645664f9113a01300205711916316a4f9113a000815c46453e444e80c4080020771191599113a00400800815c464566509113a0a100205721915993e444e82640082dc8711915993e444e80020571d9161966444e80140094e05711915993e444eb00205711915d5664f9113a000815c4645664f915444e800205711664f9113a06b03800815c4645664f9113a401002057c9915993e444e804800815c4645864f9113a0060025391dc45993e444e801800815c464566444e82900500205711915993e450e829000815c4645674f9113a04600235815c4645664f9163a0008fe05711915a13e444e80000091e05721664f9113a000815c4645664f9113a45300247815955993e444e806400815e9721915993e444e8002057b1c46f5b6599113a0000020f711b65993e444e800000815c464d664f9113a000815c4645664f930444e800205711915993e444e825c00002057c9c4645113a00500205711bd5993e444e803800815c464566501113a0c700205711915a13e444e81ac0000207711925993e444e800205711915993e444e82e800815c4645664f93d444e800205721c4645864f9113a000815c464566509113a07b0020571591599614f9113a000815c4645664f9113a0330020f711915993e444e800800815e7711935993e444e800247815c45993e444e81fc00815c8645664f9113a0c700205711915cd3e444e801800815c46d99159940444e800205711bd645684f9113a000815c464566509113a01200205711be649664f9113a00091e05645664f91e3a019002057edc464d664f9113a000815c4645664f9113a0c800205711915993f444e829000815c464586599113a09d00205711915993e444f11ec00815c4655664f9113a00600000815c4645113a00800800815c464586599113a0050020571191619664f9143a000815c46bd915993e444eb0020571191599113a08a014008ca0571191631864f8e800205711915993e450e82280000205711935993e44ce8002057119163166501113a000815c4645664f9113c41200205721b6645664f9113a00094e057119159d3e444e8002057119159942444e818000815c4645664f91a3a05300205711b65993e444e802800815da711915993e444e80020571191599414f9113a000815c464566505113a00e00247815c4689664f9113a000815c45993e444e82640e00205711915993e4dd113a000815c86458c5993e444e800205711914f9113a00601400815c4645664f9113c46000232815c6645664f9113a00083dc4645685993e444e800000815c764566444e80140094e05711915993e444e900254815c5645664f9113a000815c4645684f9113a09900205715b664566444e800800815c464586599133a0050020571191619664fd113a00095e05711915993e444e800205711915993f444e822800815ec711915993e444ed00232815c4645664f9113ac00815c4649664f9113a0440020b711915993e444e804c0091e32711664f9113a00600205711915a93e444e80100083dc46c5915993e444e800205711664f9113a0c703800815c4645664f911440e800205711b664567599113a00083dc4645664f916444e80020b711916193e444e801800815c46fd915a93e444e800205711915993e444e833000815f2711664f9113a0aa00000815c46453e44ce801800815c46d9664f9113a00e00000815c464566444e82740091e05645664f9113a05b002057c9ec5993e444e803800815f2711915993e460e800205711915a13e444e831c000020571191599113a00500000815c4645664f9143a00094e05711915993e468e800207711915993e444e8008008ba05711915993e444eb002057c9c44f9113a00e01000815c4631664f9113a00e00205711915993e454e802000815c46f1914f9113a00800205711915993e444e832400815c4645664f9113a08c00205711915993e444e82a000815c4645664f9113a00100205711b6645684f9113a000815c4645664f9113a053002057c9916193e444e804800815e771191599113a0050020579dc4645664f9143a000815c4645664fd3e450e800232815c4645674f9113a000815c464566509113a0a4002057edc464566444e801400815fb711915993e450e80020571191631684f9113a000815c46458f5993e444e800205711915c9664f9113a00091e05711664f9113a006002057119159940444e801000815c467d915993e444e800205711915993e458e8128000020571191599133a00500000815c4645664fd113a0008fe397c9c46453e444e800205711915993e444e811800815c4645664f9113c4a400205711915993e4450d3a0008ca05711915993e444e900205711915a93e444e802800815c8645664f9113a004002057c9c6645664f9113a000815c4645664f9113a06f00205711915993e44ce800400815c4645664f9113a06a00205711915993e44ce814c00815c5645674f9113a0020020579dc4645664fd113a00091e05721c45993e444e800205711915993e444eb0ec008e60f711915993e444e800205711925993e444e826c00815f2655664f9113a0120020a71191619664f9113a000815c8645664f9113b40600000815c4645665091a3a0000020f7119159940444e800207711915993e444e822c00815c45993e444ed02806002057edc4645664fd113a00081dc46c5915993e444e800205711a65993e444e801800815c46458659942444e8002057c9c45993e444e820800815c4645664f9113a095002057c9c4645664f9113ac00815c464566509113a08a0020571591599113a0040080000212711915993e444e80020571191619664f9113c400815c46d9915993e444ef002057119161d664f9113a000815c4645665853e458e80023d815c4645664f9113a000815c4645664f9113a06900205711915993e444f12280093a05645664f9113a039000008c9c464566509113a00094e05711915993e444e800205719915993e444e815400815915993e444e806401002478fdf2711914f9113a000815915993e444e814c19002057119559942444e8048008ca05711915993e468e80023f815c464d664f9113a0008fe057c9914f9113a05a00205711935993e444eb3a000815c4645664f9113a0d000205711915993e444ed090000020b711915993e450e800205711915993e444ff3a000815c464566501113a00a00000815c5649664f9113a00091e055993e444e80640600205719935993e444e801000815c45993e444e80380400205711935993e444e81ac00815c4645664f9113b43100205711664f918444e803800815e5711915993e444ed0024783dc4645664f9113a000815c4645665453e444e8002057119161966444ec014008ca057b1e7645664f8e80020b711915993e444e800400815c8645664f9113a00a0020a711915993e444e80140082dc4645664f9113a05300205711915993e444ed0e800815c771191599113a00500253815c4645664f9133a000815f27119159d3e444e800205711bd64d664f9113a000815c4691915993e444e80023279dc4645664f8e824000815c4645664f9113a065002057119461966444e801400815c6645664f9113a07b00205711915a13e444e801000815c464d664f9113ac040020571191599504f9113a0000020a711915993e444e800240815c4645674f9113a000815c46bd915993e444e800205711915993e4ed113a00091e0b711664f9113a00600205719915993e444e8048000020b711915993f444e800205711915993e444e824400815c4645664f9113a00300205711915993e4d9113a000002057119159942444e8002057c9c4645664f9113a400815f8711b1645664f8e800205711b6679664f9113a000815c4645864f9113a0a80023981dc4645664f9113a00094e18711915993e444e80024d815c4645865993e3a000815c4645664f9113ac7b00000815c4645664f9113c400815c6645664f9113a06000000815c6645664f9113ac00815ec711925993e444e80020571191599614f9283a0000020f711915a13e444e800205711915993e445073a000815c4645664f9113ac120020579dc464566509113a000815c4645664f9113bce800205711915a93e444e81100094e05645664f9113a0190020571191599404f9113a000815c4645664f931444e800205711935993e444e826400815c4645664f9113a07e00247815c46193e444e801800912057c9c46453e444e80020971191599614f9113a000815fb7119159942444e800205711915a93e469113a000815c4645664fd14444e800205711915993e444e81680000205711916193f444e80020579dc4645664f9113c40095a05721915993e444e800205719914f9113a00601000815ec711b6599113a00a0020578dc4645664f9113c4008ca05711915993e444e800205711915993e444eb18000815c8645664f9113a00e002057edc4645664f9113c400815c4645664f9113a0cd00205711664f9113a00e02800815c4645665813e444e800205711916193e444e81bc00815c4705b65993e444e80024783d915993e444e8064000020571191599113b00500205711915993e444e83780094e0b711915993e444e800205711955993e444e814c0000205711b664567444e8002057c9c4645664f91a3a000815c4645664f9113a0c000205711914f9113ac06010008fe0571191599113a09d00205711915993e444e8200008fe0571191599113a0050023f815c4645664f9143a00091e057119159944444e800205711915993e4e1113a000815c4645684f9113a00a0024781dc4645664f9113a0000020571194599113a00500205711915853e444e80200095609711915993e444e800205715915993e444e800800815c464d664f9113a0c7002057119159d3e444e81ec008ba05711915993e444e800232815c4645664f9133a000815f2711914f9113a055002057119159d3e444e804800815c464566444e81ac0500205711915993e450e81ac0000205711914f9153a008000008ca05715915993e3a000815c464566501113a04400205711915993e444f10d80083dc4645664f9113a00600205711b664d664f9113a0008c9c4645664f91a3a0120020571191605664f9113a000819c4645664f9113a03100205711915993e444e91ec00815c46b9915993e444ed002057119159d664f9113a000815c4645664f9113a0570022b815c4645664f9113a000815c4645674f9113a06000205711bd64566444e801400815c46f5915993e450e800205721915993e444e811000815f2711934f9113a0040020571193631664f9113a000815f2645665093e444e800205711915993e445083a000815c4645664f9113b43f00205711915993e444e9048008fe05711915993f444e800205711915995d444eb01000815c464566555113a00200232861c4645664f9113a000815c6645664f9113a0a40024d815e7711915993e3a000815f1711915993e444e80021a815c4645664f9113a000815c4645664f9113a09e00205711915993e444e9180008ca05645664f9113a01900205711914f9113a06401000815c46d991444e80200200205711915993f444e81ac00815c46453f444e80200600205711915993e49d113a00000205721914f9113a00400205711915993e4b9113a00094e05711955993e444e800232711915993e444e828400815c4645664f9113a03b00205711915a13e444e803800815915993e444e80d8120020564566509113a01202800815ee711915993e444e800205711b66c5865993e3a000815c56c5915993e444e800205711915993e444eb29000815c46f5915993f444e8002057edf2645864f9113a00091e3f645664f9113a0190020f815c4645664f9113c40091205711915993e444e80020571191599113a09901400815c4645664f9143a09900205711915993e444e81580091e0564566511113a01900205715c4649664f9113a000815c46c591599113a0a700205711915993e468e81ec00815915993e444f10480a002057c9c4645664f9113a000815c4645664f9113a0340023282dc4645664f9113a000002057c9955993e444e8002057119164166444e801400815c4645664f91a3a01200240815c4645664f9113a000815c6645865993e444e8002057a5c4645664f9143a000815c6645664f9113a08a00205711b66456652d113a000815c4645664f911430e80023f815f26453e444e804800815ca645664f9113a00800205711915993e4e9113ac0091e05711664f9113a0a800205711915993e444e81c000815c4649664f9113a03100205711664f9113a0440380086205711915993e444e800205711915993e468e818000815c4645664f9113a0ac00000815c45993e444e82a800815c4619664f9113a08200232711915993e444e804800815c4645865993e444eb00205711915993f444e82640000205711915993e460e800205711915993e444eb2280081dc4645664f9113a0060020571191599113a0c701400815f2711915993e44ce800205711915993e450e831c00002057119559942444e800205711915993e444e815400815c4645684f9113a04400000815c44f9113a00e0100000247815c45993f444e800205711915993e444e8284008fa05711915993e444e8002057119159d3e444e829000815c6711915993e444eb002057c9bd6453e444e804800815c4645664f9113a09a00205711b664566444e801400825c464566444e80100200205711b6645664f9143a000815c464566444e82980200205711915993e444e81400000205711914f9113a06500205711b4645664f9113a000815c464d664f9113a0040020b815c4645664f9113a000815c46458c599113a0050020571191631664f9143a0008fe057119159942444e800205711915993e444e82e000815c4645664f9113a0d900205711915993e444e929000815ec711915a93e444e800205711915993e444e81a0008ca05711955993e444e800205711915993f444e831c008e605715915993e444e80023b815c4645664f9113a000815f2645664f9113a0190023f815c4645664f9113c400815c4645664f9113a09f00000815c46d9664f9163a0008aa05711915993e444e800205711915993e444e81ec00815c464566509113a06b00000815c6645664f9113a000815e7711b66c5664f8e80020571191619674f9113a000815c4645864f9113a05700205711b6645664fd113a000815c4645674f9113a08a00205711915993e444e804800815c4645665753e444eb00234815c4645664f9143a000815c4645664f9113c46b00205711935993e44ce801000815c46f59159942444e800205711915993e444e835000815c4645664f9163a0020023f8e5ec71191599113a000815c46458c5993f444e80020579dc6645664f9113a00082df2711915993e444e800000815c45993e444e820800815c4645664f9113a06000000815c4645664f9113ac00815c4645865993e444e900205711915f1664f9113a000815c46f5915993e444f100205711915993e444e9228008e632711915993e3a00200232815c5711915993e3a000815fb719915993e444e800205711915993e468e829000815c4645664f9133a07b00000815c6645664f9133a000815c4645765993e444e80020579dc45993e444e820800815c4645664f9113a0cb0020579dc4645664f9113ac00815ec7119159940444e800205711915993e44ce80480091e05715915993e444e80020f711b65993e444e802800815c4645664f9113a0480025b815c4645664f9113a000815c464d664f9113a00a002057edc4645664f9113ac00815c4645685993e458e8002057119159942444e826400815c4645664f9113a08f002057b1c8645664f9113a000815c4645664f9113a0bd00247815fb7c9664f9113a000815c4645664f9133a06000000815c4645664f9133ac008e622711915993e444e8002057119159d3e444e801400815c46456c5993e444e800205711915993e444f126400815c8711914f9113a00400000815c4645664f9113e80082dc4645664f9113a09a0020571191619664f91a3a000815c4645664f9113a09200205645664f9113a07b06400815c4645664f924444e900205711915993e468e822800815c46c5915993e458e800000815c4645674f9113a000815c46453e44ce80180400205711b664566521113a000815915993e444e80641200205711914f9113a06e0180091e32711915993e3a00200205711915995d444e801000815c464566444e8014040020571191599614f9113b400815c4645665753e444e90020576dc4645664f9113a0008e632711915993e3a08b00205711915993e450e801000815c464566444e827002002057c9c4645734f9113a00092205711915993e444e8002057c9c4655664f9113a000815c4645865853e3a006002057119163566501113a000815c45993e444e802808002057119159942444e831c00815c46458e59942444e800205711915993e450ed01800815e77119159d3e444e800205645664f9113a06006400815c4655664f91a3a01200000815c4645664f9113a400825c4645664f9113a09c00205711915994c4f9113a00082dc4645664f9113a07b00209711915993e444e800800815fb7119159d3e444e800205711915993e444f131c00815c4645835993e444ed0020571d91619664f9113a00082dc4645664f9113a01200205711b664566509113a000815f2711914f9113a00500205711915993e444e829000815c4645664f9113a07400205711914f9113a06301800815c46458c619113a00500247889c4645664f9113a000815e7711915993e444e900205711915993e450e811400815c46456644ce8014040020578dc4645664f9113a400815ec711664f9113a00e00205711915993f444e80100081601711915993e444e800232711955993e444e804800815c46d9915993e444f1002057119163166509113a000815fb711915993e444e90020b711915993e444e81800083dc4645664f9113a00100205711915a93e444e80c400815c469d915993e444e80020f711915993e444e814c00815c4645664f9113a072002057119161966584e801400815c4645664fd113b40600205711955993e444e828400815c46458c5993e444f100205711915993e444e824c00815c459940444e80280600205711914f9113a00800800815ec711915a13e444e800205711915993e444eb10400815915b1664f9113a01900000815915993e444fa06400815eb711915993e444e800205711915993e4e9113a00000205729914f9113a0080020b711915993e444e832c0082dc46453e444e801804, 0x25a420000000000259c2000002594225901257c52574200000256c2256812560200000255822554125501254c1254812540200000253c12538100000253410000025301252c1000002524225201251c125181000002514125101000002504324fc224f8124f410000024f0124ec10000024e8124e0224d430000000000000000000024cc224c42000000000024c010000024b8224b4124a8324a022498200000000002494124901248c10000024881248020000000000247820000000000246c32468124602245822454124501244c10000000000000002448124441244010000024382000002430224282000002424124201241432410100000240c12408124041000002400123fc123f8123f4123e8323e0223dc123d810000023cc323c8123c4123c0100000000000000023b430000023b0123ac1239c4000002394200000238c2237c4237812374123701236822364123601235820000023502234c12348100000234412340123382233412330123282231c30000000000231812314123101230c1230812304122fc222f4222f0122e820000022e0222d8222d4122d010000022c8222c0222bc10000022b4222ac222a8122a4122a012294322901000002284300000227c222781000002274100000226c22268122641000000000022544224c20000000000000000000022481000000000022441000000000022401000002234300000223010000022282000000000022241222010000022182221410000022101000000000000000220c1000000000022042220010000021fc10000021f4221f0121ec121e8121dc321d420000021d0121cc10000021c0321bc121b4221a4400000219c2219422190121882218412178321702216c121681216412160100000215c121503000002148200000214410000021305212c100000000000000000000212812124100000000000000000000211832114121101210c1210812100220f82000000000020f0220ec120e420000020e010000020d8220d0220cc120b8520b4120b0100000000000000020ac120a4220a012098220941000002088300000208022078220741000000000020701206c120642000000000000000000002058320541000002050100000000002048200000204412040120382202c32028120184200c32008120041200011ffc11ff811ff0200000000001fec11fe811fe021fd821fd021fc821fc411fb831fb4100000000001fb011fac10000000000000001fa811fa410000000000000001f983000001f941000001f9011f8c10000000000000001f8031f7c100000000001f742000001f6c2000001f6811f6021f5431f4c21f4811f4411f3c21f3811f341000001f2831f202000001f1c1000001f0c41f003000001efc11ef81000001eec3000001ee031ed821ed021ec821ec411ec011ebc1000001eb811eb411eb011ea821ea021e9c100000000001e9811e941000001e844000001e8011e7c1000001e7421e6831e6411e583000000000000000000001e541000001e501000001e4821e4411e4011e3c11e381000001e3411e3011e2c1000001e28100000000001e2411e2011e182000001e141000001e101000001e082000001e0411e0011df431dec21de421ddc21dd031dc04000001dbc100000000001db810000000000000001db021dac1000001da811da411d9831d941000001d9011d8c11d8421d7c200000000001d7811d7411d7011d6041d5821d5021d4c11d4811d4411d4011d3c11d342000001d3011d2c1000000000000000000001d2811d2411d2011d1c1000001d1421d0c21d08100000000001cf841cf0200000000001cec11ce421ce011cd821ccc31cc421cb831cb41000001cb0100000000001ca821ca41000001c9c21c9421c9011c882000001c841000000000000000000001c8011c7c1000001c7811c645000001c601000001c5c11c5421c4c21c442000001c4011c3c11c3811c30200000000001c2820000000000000001c202000001c1c11c18100000000001c1411c101000001c0821c0021bfc1000001bf031be821be411be0100000000001bd821bcc31bc031bbc11bb42000001bac21ba421ba011b9c11b98100000000001b9021b8c1000001b8031b7c10000000000000001b70300000000001b6c1000001b642000001b60100000000000000000000000001b5c11b581000001b54100000000001b4c21b4811b4411b4011b3c11b381000001b3411b2c21b281000001b2411b2011b18200000000001b14100000000001b0c2000001b0811b0021afc11af811af411af01000001ae821ae411ae01000001adc11ad811ad02000000000000000000001acc11ac031abc11ab81000001ab4100000000001aac21aa421aa011a9c1000001a981000001a941000001a9011a8c11a803000001a7821a7411a7011a6c11a6421a5c2000001a5421a4c21a4811a441000001a3c200000000001a3811a3411a2c21a2811a241000001a2011a143000001a1011a0c100000000001a081000001a041000001a00119f8219f4119ec219e4219dc200000000000000019d8119d02000000000019cc119c8100000000000000019c41000000000019c010000019bc119b810000019b4119b0119a8200000199c30000000000000001998100000199411990119843197c21974219701196c10000019681196021958219502194c119481193c30000019381000000000019341000001930119186191411910100000000000000000000190c118fc418f4218f0118ec118e4218e010000018dc1000000000018d4218d010000018cc1000000000018c8118c0218b8218b0218a82000000000018a0218982188c30000018842187c200000187810000018645185c200000185811854100000185010000018404000000000018382182c318242000000000000000000000000018201000001818200000181410000000000180c200000180811804118001000000000017fc117f8117f4117ec20000017e8100000000000000017e4117e010000000000000000000017d8217c8400000000000000017c4117c01000000000017bc117b8117b4117b0117ac1000000000000000000000000017a810000017a410000017a01179c1000001794217901000000000000000178c10000017803177c11774200000176c2000001768117602000001758217541000000000017501174c11748100000174411740100000173c11738117341172c2172811724100000000001720100000000000000000000171c1171811714117101170430000016fc216f4216f01000000000016e8216d8416d41000000000016d0100000000000000016cc116c8116c4116b8316b4116b0116ac1169c41694216901168c10000016842000000000000000167c216742000001670100000000000000000000000001668216641166010000000000165c116581000001654116501000001644316401163c100000000001638116341163011628200000162411620116182160c300000160811604116001000000000015fc115f81000000000015f4115f0115ec115e8115e410000015e0115d0415cc115c4215c010000015b8215b020000015ac115a8115a410000000000159c215942158c2158810000015802157c11574200000156c2156810000015641155831554100000000000000015501154c10000015481000000000015402000001538200000153020000015282000000000015241151c200000151810000015102150c11504215001000000000014fc1000000000014f4214ec20000014e8114e0214dc114d8114d410000014c440000014bc214b42000000000014b01000000000014ac114a0300000149821494114901148c100000148420000000000000000000014801147c11474214701146c10000014681000001464114601145821454114501144820000014441000000000014401000000000000000143c11434214301142c11428114202141c11418114141140c214081140020000013f8213f020000013ec113dc413d4213cc213c4213bc20000013b8113b4113b0113a4313a011398200000000000000013902138c11388100000138020000000000137c10000013781136c30000000000136421354413501134c100000000001344213401000000000000000000000000000000133c11338113341132c2132810000013241131c200000000001318113141000000000000000130c2130811300212fc10000012f8112f020000012ec112e8112e0212d43000000000012d0112cc10000012c8100000000000000012c020000012bc112b0312a8212a0200000129c1000001298112941128831284112801127c112742126c200000126811264112601125c11258112502124c1000000000012481000001240212382123410000012301122c1122811224100000000000000012201121c11218112102120c112081000001204111fc20000011f8111f4111f01000000000011e8211dc30000011d8111d410000011d010000011cc10000011c810000011c4111c0111bc111b420000011b0111a8211a41119c211942119010000000000118c1118420000011801117c1000001178111702116c1000001164211601115821154111501114c10000000000000000000000000114810000011441113c21130300000000001124311201000001118200000111020000011082000001104110fc20000010f0310e8210e410000010dc210d810000010d4110d010000010cc10000010c4210b8310b4110b01000000000000000000000000010ac110a42000001098300000109410000010901000001084300000000001080100000000000000000000107c110703106c11064200000105c210581104840000010441103c21038100000000001034100000102c200000102811020200000101c100000000001018110141100c210081100410000000000000000ffc20ff81000000ff410fec200000000000fe420fdc20fd81000000fd41000000fd010fcc1000000fc8100000000000000000000000000fc4100000000000fbc200000000000fb030fac10fa42000000fa010f9820f9410f9010f8820f8410f8010f78200000000000f7020f6c10f6420f5c20f581000000f502000000f404000000f3c1000000f3030f2c10f2810000000000000000f2020f18200000000000f0840f0410efc2000000ef810ef41000000eec20ee4200000000000ee01000000edc10ed810ed410ec830ec410ebc20eb030eac10ea810ea41000000ea010e9820e8c30e881000000e8410e8010e7820e7020e6c10e642000000e5c20e581000000e4c3000000e48100000000000e4410e3c20e38100000000000e3020e2820e2410e1830e1410e1010e043000000e0010000000000000000df820df020de820de410de010ddc100000000000dd81000000dd410dd010dcc10dc030dbc1000000db42000000db010da430d9c20d9810d9020000000000000000d8430d801000000d7c10000000000000000d7810d74100000000000d7010d6c10d6810d6410d60100000000000d5820d541000000d4c2000000d4810d4410d3c20d342000000d2c20d2810d24100000000000d201000000d1820d08400000000000d0410d0010cfc10cf420cf010cec10ce4200000000000ce010cdc10cd810cd020ccc10cc810cc4100000000000cb830cb41000000cb010ca820ca410ca010c9c10c90300000000000000000000000000c8820c8410c8010c7c100000000000c781000000c741000000c7010c6c10c6810c6410c6010c5c10c542000000c5010c4c10c481000000c402000000c3820c302000000c2040c1820c102000000c0430c001000000bf43000000bf01000000bec10be030bd820bd410bc830bb840ba840ba020b9c10b9810b9410b90100000000000b8c1000000b881000000b7c30b7810b741000000b6050000000000000000b5c10b5810b5020b4c10b4810b441000000b40100000000000b3820b3410b3010000000000000000b2430b20100000000000b1820b1410b1010b0820b041000000b00100000000000afc100000000000af810af410ae830ae0200000000000000000000000000adc10ad810ad410ad01000000ac430ac010ab820ab41000000aac20aa81000000aa410a9c2000000a9810a9410a9010a8430a8010a7c100000000000a7810a6450a6010a5c10a5420a5010a4820a4020a382000000a341000000000000000000000a2c20a2420a201000000a1820a1410a1010a0c10a0810a0410a00109f8209f0200000000000000009e820000009e0209dc109d8109d4100000000000000009cc20000000000000000000009bc409b8109b41000000000009b010000009ac109a8109a4100000099c209942099010000009882097c3097810974109701096c10000009642096010000000000000000958200000000000950200000094430940100000093c109381093410000000000092c20000009203091040908208f840000008f4108f0108ec108e810000008e0208dc108d810000008d41000000000008d0108cc108c4208c010000008bc1000000000008b8108ac308a8108a4108a0100000089c10890308882087c3086c400000086810864100000085c2085420848300000084410000008383083410828308202000000000000000081c1081420000008101080c108081000000000008041000000000008001000000000007f8207f4107f0107e82000000000007e410000007e010000007dc10000007d4207cc207c8100000000000000007c410000007c0107bc1000000000007b8107b4100000000000000007b010000007a8207a4107a01079430790107882078410000000000077c207781077410768300000076020000000000075c1075810000007541075010748207441000000000007401073c10000007342072c2072420000000000071c207181071410710107043070010000006fc100000000000000006f8106f020000006ec10000006e420000006e0106d820000006cc306c0306b8206b4106ac206a810000006a4100000069c20698106941069010688200000068410000000000000000680106782067410668306602065c1000000000006542000000650100000064c106442063c20000000000063810000000000062c300000000000628106202061c10618106141061010604305f4400000000000000005f0105ec105e420000005e0105d8205d410000005d0105c040000005bc105b4205b0105ac105a81059c3059810000005941000000588305841058010000000000057c10000005703056c1000000568105602055820550200000054c1054810000005402053040000000000052c105242051c20514205101050430500104f4304f0104ec104e420000004e010000004d8204d41000000000004cc204c030000004bc104b8104b4104b010000004ac104a42049c2000000498104902048c10488104802047c104742046c2000000000000000046810460200000045c10458104502044c100000044030000000000043c10438104302042c104242042010418204141041010408203f4503e8300000000000000003e4100000000000000003e0103d8203d02000000000003c4303c0103b820000003b0203ac1000000000003a8103a41039c203981039410390100000038430378303741036c203681036410360103504034c103481034410340100000033c1033810000003302032c10000003281000000320203182000000000003102030430000002fc20000002f8100000000000000002f0202ec102e420000002e0102d4302cc20000002c420000002c0102bc102b4202b0102ac10000002a8102a410000002a0102982029410290100000028c1000000288102802027c10000002781026c30264202601025c100000000000000002542025010248202402023c10000000000000000230300000022c1022810224102201000000214300000021010208200000000000204101f83000000000001f020000001e8201e4101e0101d430000001d0101c8201c02000000000001bc1000000000001b810000001b02000000000001ac101a81019c3000000198100000019410190101882018020000000000017c10178101702016c101681016410000001601015c10000001503014c10000000000000000148101441013c2013810134101301012820000000000011840110200fc500f8100f0200000000000000000e820000000e4100e0100dc100d4200c8300c02000000000000b43000000000000b0100ac100a420000000a01000000098200000009020088200841007c200781006c30064200000005c20000000503004c1000000044200000003c200381003410030100000002820024100000001830014100083000000000200000, 2411, 2411⟩
def t4 : Archive := ⟨0x835c4645664f9113a00000205731915993e444e900000815c46453f454e8020000020571191444e815c0500000815c4651113a00601400002067119159940444e800000815c8645674f9113a000002056556c4f9113a01200000926057113e444e80200000205711915993e468e800000815c46d99159d113a00000205711915cd3f444e800000815c4669664f9163a000002057119259942444e800000815c465566501113a00000205645664f91e3e8190000083e05645664f9113e8000023281dc4645674f8e800000839c4645664f9113a00000232645664f9113e819000008ce0571191598e8014000020f78d915993e444f100000815c4645864f9113b400002057c9c44f9113a01000000815f2711664f9183d0000020571192599113a0a700000815c46453e444eb02000002057c9915993e444fa00000815c464566575133a0000020f711915b13e444e800000711915993e444f10840000212711664f9113a0060000091e3f711664f9113b40000000815c4444e80380500000815c464566444e80240000205711915b53e444ed00000815b659944444e80640000205711914f9133a00600000815c664d664f9113ac00002057c99161942444e800000815ce655664f9113a00000205711664f9113a01000000849c4645664f9113d00000205721914f9113a06300000815915993e444e81300000205711915993e468f10000082dc4645664f91a3a00000205711914f9113b44000000815c464566501113b400002056d966444e8064020000083605711914f9113bc00002057c9c46f541444e800000815c4645113bc080080000205711664f9183a00e0000082dc4645864f9113b400002056dd66511113a01900000819c4645664f9113a00000205645684f9113a05a00000815e55993e444f403800002327119159d3e3a01200000815c464567444ec0140000205711bd59941444e800000815c4655664f9113a0000020571191599133a03400000815c4645664f9113b0000020b711914f9133a00600000815c44f9113a01001000002057119559942468e80000081dc464566501113a00000205735915993e444e800000815ca6453e444e802000002398c9c5645664f8e80000083d915993e444e816c000023279dc4655664f8e80000082a0571d91599113a000002057113e460e80380400000815c46d9684f9163a0000020a71191599133a00500000825c4645664f9113a400002057113e44d113a00e00000889915993e444e80640000206711915993e444f100000815c464d3e444e816000002057119159d3e458e800000815915b13e444e806400002398c9c4645663a0050000083dc4645664f9113e8000020571191444e80240500000815c4655664f9113c40000205711915993e444ed0000082dc4655664f9113a00000247815c44f9113a00800000825f2719914f9113a0000020571191444e801c040000091e32715915993e3a000002077159159d3e444e800000711915993e444f7084000000083dc45993f444e800000815c464566505113d00000205735915993e444f100000815ca6453e455113a00000205711864f9113a00e00000815c4645865853e3b40000209711915993e448e800000815c46453e454ef3a000002057c99159942444e800000825c6645664f9113a0000020f5993e444e80640600000835c46453e444e802000002057b1915993e478e800000815c4501113a00a0200000205711914fd113a009000008ca057159159d3e3a000002478c9c4645663a0050000081dc464567444e80140000208711915993e444e80000081dc4645664f9113a00000205711914f91a3a00800000825915993e444e8064000020b711915993e444ed00000815c6645664f9133ac0000209711915bd3e444e800000815c465166444e829c000020571166501113a00e000000020f645664f9113e800002057119159d113a03400000815c45993f444e8064000020f721664f9113a0060000091e056456c4f9113e80000232815c4645673a00500000829f2711914f9113a000002057c991509113a00400000825c8645664f9113a0000020571191444e80240800000815c8645113a006014000020a7119159d113a0050000083d915993e444e80e40000205711b6599163a00200000815c44f9113a010020000020a711915993e444e80000081dc4645664f9113c40000205645664f9113e81900000815e3645664f9163a0000020b711914f9113b40400000815c464d66575113ac000020571191599113a03c00000829c771191599113a0000025391dc45993f444e800000849915993e444e80640000000835c46453e444ef00000815c46456a501113a000002057113e444e80280800000002055993f444e806400002056d9664f9113a04c0000091e057ed6c4f9113a00000206711914f9113a0080000083dc464566509113a00000209721914f9113a00400000815c564566501113a00000205645665111e444e800000815c46553e444e80200000205711916193e3b4240000083d915a13e444e80480000205711664f9113a00e00000815c4645664f9153bc0000212721915993e444e80000091e05645665111e3a000002057119463186444e80000094e47645664f9113e8000020578d915993e458f10000081dc4649674f9113a00000205645664f9113a05200000815c4619614f8e80380000205711914fd113a07000000815c464566509113a40000205711916193f444e800000849c4599414f9113a000002125993e444e80480e0000082a0571191599113b00000000829c764566444e800000815c44f9113c40a0200000205711914f9143a0700000091e3f711664fd113a00000205711664fd113a0a9000008ca057119259d3e3a00000205711684f9113d00e0000091e32711864f8e801800002057119159946444e8000008c9c4655664f8e80080000205711914f9113b40800000815c44f9113a00e01000002057119159d55444e800000815c45993e444f1038000020b711664f9113a00e00000815c464d684f9113a00000205711914fd113a06500000815c46456a4f9113a000001c4645664f9113ac210000083dc45993e458e801800002056d96c4f9113a01900000815c664566509113a00000205711915a942468e800000815c564567444e801400002057119159940450e80000082dc4645864fd113a00000205715915993e444e800000815c46c5916193e3b40000205711915993e468eb00000825c4645664f9163a000002057c9c4645113a00500000825c464566575113a0000020564566509113a019000000020571166505183a00000205725915993e444e8000008c9c4655664f91a3a00000207711914f9113a00800000815c44f9113a00e01400002057119159946444f10000091e32711664f9113b4000020571191599113a0050000091e05729664f9113a00000205711915a93e444f10000082dc46456a4f9113a00000205711915995d44ceb00000815c864566505113a000002478fdfb7c93e444e800000815c4661664f9113a000002057219159942444e800000815c45993f444e83340000205711914f9133ac06000008c9915993e478e80640000205715915993e444f10000082dc5645664f9113a000002057119463166444e80000081566505113a012038000020d729915993e444e800000815c464966501113a0000020559942444e80480e00000815c46d9914fd153a00000205711915993e3a04e00000815c4645664fd113a0000020f711684f9113a00e00000815f271193444e800800002057c9c464d3e44ce8000008159559944444e80640000205711915993e450e800000819c4645664f9113ac0000205711955a942444e800000815c46453e454e801800002057119461967444e800000815c464566444f1014000020b71191599113a00500000815c4645865853f3a00000205711955993e444eb00000841c4645664f9113a000002057119259d113a004000008ca05711915993e3a8000020571193599113a00200000815b65993e444fa0640000205711985993e444f100000815c464d664f9133a00000215711915993e444e800000815c46453e444e80400000205711915993e460f400000815c4669684f9113a00000205735915993e444eb00000815c44f9113a00e02000002057159259d3e444e800000815c46453e454ef0200000247815c46d967444e800000849c45993e444e82080000205711915993f444f10000082dc4645664fd113a00000205721915cd3e444e800000815c4645684f9133a00000205711915993e450f10000082dc4645664f9143a00000247815c46193e444ed000009260d7113e444e802000002057c9664f9113a01d0000083dc45993f4f9113a00000205711b16193e3a00e00000815c464967444e80140000000829c464566444ec00000815c4649664f9113a0000020571d915993e444ec00000855c4645664f9113c40000247815c44f9133a00600000825c6645664f9113ac000020f711915993e478e800000815c464566509163a0000020771191599113a09d00000815c46453e444e80600000205715914f9113a00800000815c4645864f9113d00000207711915993e444eb0000083dc45993e444e8020000020571194599133a00500000815915a13e458e804800002056556c5993e444e800000815c4649664f9113c4000020b711925993e444e800000815c465167599113a0000020f645664f9163a01900000815c85a13e444e80380000205645664f91a3a04c00000815c464d674f9113a000002057c9c45a141444e800000815c464566444ea010000020571191444e8020050000091e057293e444e80200000205711b659d113a00a00000815c45a166505113a00000205715915993e444ea00000829c464566444e82740000205711664fd113a0aa00000815664fd3e444e80640000205711955993e468e800000835ca6453e444e80200000205721c4645113a00500000815c464566444eb0f00000205711914fd113a00800000815c44f9113a00c0180000247815c45993e444ed00000815c46453e450e802000002057113e44ce802806000008ca0571d915993e3a00000205645664f91e3a01900000711915993e444ed084000020571193444e80200200000815c45993e444eb0380000205711b1645864fce800000815c464d3e44ce80200000247835c44f9113a00800000815f2711944f9113a00000232645664f9113a01900000829c7645664f9113a00000211711915993e444e800000815955993e444e813000002055993e444e80640800000815c4645664f9113cc0000205711915993e468ed00000815c4645664f9213a00000205711b6645113a00900000815c465167444e80140000000815c8645113a00500000815c46453f455113a0000020b711914fd113a00800000815c4645664f9113d0000024782dc45993e444ed00000815c4651664f9113a00000205711b64f9113a0100000091e32711664fd113a00000205711915993e450ea00000815f2645665091a3a000002057119159947444e800000815c771194599113a00000205645664f91e444fa00000815c46456650d113a000002057119159946444eb0000083dc464566501113a000002057293e444e80280800000815c44f9113ac0e0100000205711924f9113a00800000815c46d968444e80080000205721915993e460e8000008c9664f9113a0120380000205711914f9133b4060000091e05645664f91e3e80000205711915a93e444eb0000081dc4645664f91a3a00000207711b664567444e800000815664f9113a01d0640000205729c464d3e444e800000815e3645684f9113a00000205711684f9163a00e00000815c46d966444e802c0000205711915b53e444e900000815ca5993e444e80380000205711915993e484f100000815c4599414f9183a000002055993e460e80480e00000815c4645674f9133a00000232711955a93e444e800000815c5645664f9113ac0000205711874f9183a00e00000815c464566501113a40000232815c46d99159ce80000083dc46d98c599113a00000209711915995d444eb00000815c46456651d113c40000205721664f9113a01d00000819c4645664f9113b4000025391dc85993e444e800000645664f9113e821064000020571991599133a00500000815c46456644d113b000002056556c4f9113a01900000825c46453e444eb018000020f7119159940444f1000000020571d94599113a00000205711955993e444ed00000815c4665664f9113a00000205721914f913444e800000815c464566444eb0140000232815c4645864f8ed00000835c44f9113a00a020000020578d915a13e444f100000815cd645664f9113b40000205711985993e444eb00000815c464566501123a0000020a7b1c464566444e80000000205729934f9113a0000020571191444e81bc0500000815e764566511113a000002057c99559942444e800000815c664566501113a000002097c9c464d3e444e80000083dc4645664f9113a00000233829c4645663a0050000091e05711864fd113a0000020b711664f9113b40a00000815f271d91444e80140000205711916193e444ef00000815c46d966458e800c0000205711915993f444eb00000815c8645864f9113a000002056453e444e8194190000081dc4655664f9113a0000020564566501113a01900000815c464566444e80340000209711935993e444e800000815c46d9b159d113a0000020f711664f9113a0ce00000815c45993e468e80380000205711995993e444f100000815c4645664f9143ac00002478fdc85993e444e800000815864f9113a012038000020f711684f9113a00600000815c764566444e801400002057ed664f9113a06800000815c4645664f9113a4000020571191619624fce800000815c464d66444eb0080000205711935993e44ceb00000855c4645664f9113ac0000205711914f9113bc40000008ca05711915993e3b000002057219159940444e800000815c46455e444ef0200000209711915a13e444e80000083dc4645664f9113c400002056d98c599113a01900000815f2645664f9113dc000020b721916193e444e80000081dc4645664f9113b4000020a711915993e444ec00000815955993e444fa0640000212711664f9113d00e00000815c4645664f9123a00000205645684f9113a05b00000815b65993e478e80640000205711935993e454e800000815c6645664f9113a0000020571191599113b03c00000815c46456a4f91a3a00000205711944f9113a00800000815ca645664fd113a000002326d9664f9113a0190000082dc4645664f9113a40000205711925993e444eb00000815c46456c511113a00000205715915993e468e800000815c56d99159d113a00000205645664f9113a01900000819c45993e444e80380000205711664f9183a08200000849c4645684f9113a00000232815c46193e3a00e00000815c46193f444e80280000247815c45993f444e800000815c4645664f9123c4000020b711915993e448e80000083dc46d966501113a0000023279d915993e3a01900000815ca4f9113a00e0200000205711b66453e454ef000008153e444e80480a0200000205711915993e444ef00000815c464566468e80140000205721915993e444e800000815c6645664f9113c4000020b719915993e444e800000815c46456e4f9113a00000205711664f918444f400000815c464586599613b000002097c9c46453e44ce800000835c4645664fd113a000002055993e444e80480e00000815c8645865853e3a0000020571191619113b40500000002056456c511113a00000205721664f9113a0ce00000815915993e444e80740000205645664f9113c4190000082d915993e444e806400002327119161966508e800000815c461d3e444e803800002055b13e444e80640e000000020571194599113b00000232711915993e3a01400000815c45993e444ed0380000205711915993f468e800000825c4645664f9133a00000205711955a93e444e800000815c464d66444e826c000020571191599113b00400000815c4645133a006014000024782dc45993f444e800000815c459941444f40380000205721914f9113a00400000815c8645664f9113c4000020b721915993e444e800000815f259942444e8038000020f711914f9113a00800000815c4645864fd113b40000205715955993e444e800000815c46456644ceb00800002057119159940458e800000815c46456e4f9113c40000205711916313e454e800000815956456c4f9113a000002057119159944444fa00000815c46519159d113a000002057119359942444e8000008159559942444e806400002057c9c4645113b005000008153e444e80480e0100000205711916193e450ed00000825c464d3e444e80200000207711664f9113a00e00000815c464566519113b4000020f711b65993e444e800000815c46453f44ce8018000020671191599113a00500000815c465566444e80140000205711914f9113a40800000815c464566444ec0140000205711915a93e444ed00000815c464568505113a0000020559944444e80640600000815c464d66444e829c0000205711b663166458e800000815c464568509113a00000205721914f9113a00500000815c45993f444e8028000020b721914f9113a00400000815f2645113a0120140000205715915993e444ed00000815c464566501163c40000205711925993e468e800000815c46d99259d113a00000206711915993f444e800000815c4645664f9213ac00002057c9915a942444e80000083d915a13e444e80640000205711955993f444e800000815c465166444e82740000205711a64f9113a00800000819c4645664f9143a00000205711914f9123a008000008ca05711916193f3a0000020f711b65993e444f100000835ca6d9914f9113a00000205711915993e4442800000815c46456651d113ac0000205711955993e450e800000815c44f9113a0100280000205711934f9153a00800000815c66453e444e80200000207711915a93e444e8000008c9f2655664f9113a00000205729914fd113a00800000815c464566444ed0140000205711915993e458e800000849664f9113a01903800002097119159d3e444e800000815915993e444fa0280000205711985993e444ed0000081dc5645664f9113a000002056453e444e80640800000815f26453e444e82e80000205711664fd113c40a0000082dc45993f444e8028000020571186444e803805000008159159944444e80e40000205721664f9113a0aa00000815c4645664fd113b40000212721664f9113a00e00000815c7651664f9113a000002056d9664f9113a0190000091e057113f444e802000002127c9c459941444e8000008ca05715915993e3a00000205711915a53e444e800000815c46453e444ef020000020771191599113a00500000815c45993e444e82080000205721914f9113a00800000815c4645664f9143b40000232815f2711913a00500000815c4645664f9163c4000020b711915993e458e800000815c4665664f9113ac000020571193599113a0a500000815c464566444e80d00000205711bd6d967444e800000835c46453f444e80200000215711915993e444ed000008c9915993e3a019008000020571191444e80c8080000083d9159944444e806400002056dd664f9113a019000008ca0571191598e8014000020a7c9c4645113a00500000815c464566509133a00000205721b1645864f8e80000081dc4645664fd113a000002057113e444e8204080000083dc4645664f9113ac000020b711915993f444ed00000815c45a93e444e80380000208711915993e450e800000815c464566444e82c00000247815c45993e444f40000081dc4645664f9143a0000020a71191599113a00500000815915a13e444e80e00000205711914f915444ef00000815c46d991599113a80000205711914f9143b4040000082dc4645664f9143b400002057c9956193e444e80000091e32721664f9113a00000209711935993e444eb00000815c46456644ce829c0000205715664f9113a00e0000081dc464d66444e80080000205711925993e444ed00000815f2711113a00e014000023f815ca6453e444e80000083dc46d93e444e8020000020579d915993e444fa00000815c46d966501163a00000232815c464d663a00200000815c4599113a00e014000020571191454e80200200000815c859941444e803800002057b1c465166444e80000083dc4645684f9163a000002057113f444e80280800000815c4645664f9123ac0000207711925993e444e800000815c6645664f9113ac0000205715915a93e444e800000815c45993f444e80380000205711975993e444e80000083d915993e444fa3a00000205711914f9133a05700000815c46453e444e81e400002057119159d42444e800000815c45993e450e80380000205645664f9113ac1900000815c46453e458e80200000253815915993e444fa00000815955993e478e80640000205711915a9113a00500000815915b13e444e816c0000232655664f9113a01900000815ca711914f9153a000002057113e444e80400e00000815c45993e460f40380000205711b663568444e800000815c46d9664f9163a00000205711916193f450e80000091e05721864f9113a000002057119159d113a0a700000815c664d3e444e8018000020571591599113a00500000815c8645664f9113ac00002056456c5113e444e800000815c46453f444ed02000002057c9955993e444e800000815c46456e4f9113ac00002056d93e444e80640800000815c4651664f9113b00000000815c44f9133a00e00000815c46456c4f9113e80000205711915a93f444e800000815c4645664f9163a8000020d711914f9113bce80000083dc4645664f91a3a000002057c9ec645113a00500000815c46456a4f9143a0000020971191599113ac0200000815c4645684f9183a00000205715915993f444e800000825c4645664f9133ac0000205711914f9113a05800000815c46453e444e812400001c4645664f9113a421000008156c4f9113a0190180000000815ca6453e454e800000815c46d9664f9163c40000205715915993e450e800000815c4645664f9213b40000205721914f9113ac0400000815f26553e444e80100000205711915993e468e900000815c76d991599113a0000020571593599113a00200000815c4645664f8e809400002057cdc4645113a00500000002056456c4f9113e80000205729915993e444ef00000815c46456651d113b4000020a71d9161966444e80000083d915993e444e81300000205711864f9113d00e00000815c464566450e80140000205711934f9113a07000000815c46496a4f9113a0000020571193599133a00500000815c4645665111e3a00000205719915993e468e800000645664f9113a021064000020571191444e8024020000083dc4655664f9113a00000247815c45993e444ef000008c9c464566511113a000002055993e444e812c0e00000815c4645664fd143a00000247815c85993e444e800000815c5649664f9113a00000205711914fd153a00600000815c4645664f8f10940000205645664f91a3a01900000815c464d3e444e819400002057119359940444e800000815c4645664f91f3a000002227119159942444e80000091e055993e444e8074000020d711915993e444ef00000815c4665664f9113b40000206711915993e444e900000815c4645113a0640140000205711915993e458eb00000815fb7c991444e8014000020571192599113a00500000815c4655664f9113a4000023f815f264542444e800000815664f9113e819018000020571d91599113b00500000815c66453e44ce80180000205721915993e468e800000829c4651664f9113a000002055993e444e805c0a00000815c464568501113a0000020f6456c4f9113a0190000000205645665111e3a0000020f711915993e444ed00000815cd645664f9113a40000205711914fd143a0040000091e057213e444e8010000020b711915993f450e80000091e0b721664f9113a00000205729bd6453e444e80000091e056556c4f9113a000002055993e468e80480e00000819c4645664f9123a00000205721916193e444ed00000815c4649664fd113a00000205711b64f9163a00800000819c6645664f9113a00000205711664f9113a03000000815f2711934f9113a000002127edc45993e444e8000008fe397c9ec645113a00000205719955993e444e800000849c85993e444e80180000205711955a93e468e800000815c4649664f9143a000002097119159942444e80000084a05711664f9113d00000205711b15993e444f400000815c45993e444f40380000205721914f9133a00600000815c46d98c5a1113a00000206645664f9113a0190000083d915993e444f10480000205645664f9113e83900000815c464d664f9113a00000205655664f9113a01900000815c464568501113c400002398c9c4645674f8e800000815fd7c9934f9113a00000205721664f9183a00e00000815c4699664f9113b400002057c9c459941460e800000819c8645664f9113a00000205711915993e448ed00000815c45993e444f10c00000205711914f9133a0700000083dec711b6599113a00000205711915a13e444e800000815c8655664f9113a00000205719915993e444ed0000081dc4645664f9113a400002057113e444f40380400000815c46d991599113b00000232815c8645864f8e800000849c464566505113a0000025691dc85993e444e800000815915993e444fa10c000020571d91599113a03400000815ca6453e444ef02000002478c9c4645674f8e800000829c464586599113b0000020f645664f9113e81900000815c464d664f9113c4000020b711935993e444e800000829c464566444ec3a00000205711684f9113a0ce00000815955993e444e80740000205645664f9113b4190000091e054f9113a0190200000232815c7645663a00500000815c464566501133a00000239815c764566444e80000082dc85993e444e8028000020f7113e444e80280800000815f271194444e80140000247815c45993f444ed0000081dc6645664f9113a0000020a71d91599113a00500000815c4645684f9113c40000205721915993e444ed0000082dc4645684f9113a00000205711915993e3a8250000091e057113e444ef020000020f711664f9113a00e00000815c46453f450e80200000247815c45993e450ed00000815c46456e4f9113b4000020571194599113a0050000081d915993e444e80640000205721864f9113a00e00000815c45a141444e80280000205711bd4f9113a03700000835c46453e444ef020000020571191444e80380500000815c5645664f92e3a000002057c9bf6553e444e800000815c45993e444e903800002057c9c46453e44ce800000815c464566511113a0000020564566509113a0390000081dc8645664f9113a0000020564566501163a01200000815ec6d966444e80640000205645664f9163a04c00000815c86453e444ed010000020b721915993e444ed00000815c4645113a00901800002057119159d133a0050000091e32711b6598e80080000205711915993e44ce800000815c4645664b8e8014000020f711915a93e444e800000815c46d968501113a00000205711664f9123a00e00000819c4645664f9163a0000020f715915993e444e800000815c65993e444e803800002057119159946444e900000815c4655664f9163a00000205729bd6d93e444e800000815915a142444e804800002057119159d40444e800000815664fd113a0120280000000849c45993e444f400000815c46456a4f9113a40000205711934f9113a00800000815c45993f444ed02800002055993e444e80640e00000815c46456c4f91e3a000002057113e444ef028080000083dc464566444e80140000205711915993e44cf10000082dc4645664f9133a00000205711664f9143b40a00000815c5645664f9113a40000205711684f9113a0aa00000849c45a13e444e803800002057c9bd64542444e800000815c4645664f8eb094000020572191619113a005000008159159942468e802800002057193e444e8038040000084a05721664f9113a00000205721664f9113a00e00000815c4645664f9163b40000205719915a93e444e80000083dc4645664fd113a0000020571191599113a40500000815c464566444ec0d00000205711b65a13e444e800000815664f9113a01d0380000205711985993e444e90000083dc4645664f9143a00000205721916193f444e8000008ca0571191598ec0140000205711915993e444ee00000815915a93e444e80640000205711965993e444e8000008e60571191599113b000002057119159d3e444e800000815ca6453e444e81600000205721916193e450e800000821c4645664f9163a00000205645664f9163c41200000815c4645664fd113a400002057c9914f9113a01500000825c66453e444e8018000020a71191599113b0050000081dc4645664f9163a0000020571191599123a00500000815f371d91444e801400002057213e444e8038040000082dc85993e444e8038000020571991599113a00500000815c4651113a0080140000205711915993e450e900000815c86456a4f9113a00000205645665113e478e800000815c765186599113a00000205711b65a13e444f100000815c4645664f91e3e80000247815c44f9113a0580000081591599113a0190140000215711915993e444e900000815c4699664fd113a000002055a93e444e80480e00000815ec711b6599163a00000205715b664566444e800000815c46456f444e80140000232711915993e444fa00000815f2655664f91a3a00000205711915993f448e800000815c4645674f9113c4000020b7119159d3e444e8000008ca07715915993e3a0000020f711925993e444e800000815c6645664fd113a0000020571168505113a00e00000815664f91e3a0190180000205719915993e450e800000815c4645113a008008000020572191599113a00500000815915993f444e80640000205711914f9133a00800000815f2711934f9113ac00002325993e444e80640600000849c4645664f9183a00000000815c46453f454e800000815c44f9163a00a020000020571993599113a0020000083dc46193e444e80180000205731915993e444e800000815c664d664f9133a00000205711925993e444e900000815915993e450e80640000212721c45993e444e80000000205645664f91e3e80000205711935993e444eb000008ca0571191598e80d00000205721c46453e44ce800000815c45993e458e80380000205711915993f444ef00000815c8645664fd113a0000020971191599133a0050000091e05711664fd143a00000205645664f9113dc0a0000083dc459940444e80180000205721915993e450e8000008c9c5645664f8e80480000205711915a13e444eb000008ca0a71191598e80140000205719925993e444e800000825f26453e444e804c0000209711914f9113a06500000815cc645664f9113c400002097119159940444e800000815c45993f444e82040000232645664f9113a039000000020571191599133b00000000849c85993e444e800000815925993e444e806400002057119459d113a00200000815c86453f444e80100000205711664f9113a0d3000008c9c4645663a01201400002057119159961444ec0000082dc8645664fd113a00000000815c86453e44ce800000815c46453e454e81c00000205711915a93e458e800000815c4599113a0340380000205711915b13e444e800000815ca64d664f9113a00000205721914f9143a0040000082dc8645664f9143a000002327119159942444e80000081dc564566444e80100000205711915993e444f800000815c5645664f9163a0000020f645664f91e3a01900000815864f9113a0190180000205721925993e444e8000008c9915a13e444e804800002057119159941460e800000815c4645664f8ec0940000205711914f9153a06500000825f2711914f9113a00000235645664f91e3a0190000083dc45993e444e8018000020571191599163a00500000815c465186599113b00000205729934f9113a00400000825c4645664f9113a0000020571194599113b0e800000815c45993f450e802800002057c9c46453e44ceb00000815c4645113a0060140000205715b6645113a00800000835c464d664f9113a00000209711915993e46ce800000815c4645664f9213a40000205645664f9113a05b00000815c564566444e80d0000020571191599133a09d00000815c4645664f8ed0940000205711915993e44ceb00000815c4645664fd163a0000020571d94599113a00500000815c464d664f91a3a00000205655664f91a3a0190000083dc44f9113a006010000020f711664f9113c40600000815c4599113a08201400002057c9c46453e454e800000815c46453e44ce81bc00002057119159947444e90000091e055993e444ed06400002055993e444e81680e00000815c4645664f9113e80000209711915993e444f100000815c464586505113a000002056453e444e8194390000082dc4645113a006014000020d711b66453e444ef00000815c4645684f91a3a00000205711915993e454e8000008159159940444e80e40000205711934f9113ac0800000849c4645664f9113a00000205711914fd113bc0800000815c86453f444e80200000205711915993f450ed0000091e05721664f9113b40000205711934f9133a006000008c9c4655865993e3a000002056456a509113a00a00000815c7645664f9133a0000020571191599113a01600000815664f9113a01901800002057113e444e81540e00000815c45993e450e82080000212711664f9113a0ce000000020571191444e802400002327c9916193e3a01200000815e55993e444e80380000000815c44f9113a0100000000205711664f9183d00000205711925993e458e800000815c4665664f9113a4000020564568501113a01200000819c464d664f9113a00000205711684f9113a01000000815915b166511113a0000020f64566501113a019000008e6327b1e7645663a00000207715925993e444e800000815c8645664f9113d00000205711684f9183a00e000008153e444e806406010000020f711915993e444e900000815c464567444e827400002057119159d3e444eb00000815ca64d3e444e802000002055993e444e8074060000082d664f9113a01901800002057c9934f9113a01200000815ce64566509113a00000206711915a13e444e800000815c4645664f9113c80000205711664f9113b43000000815915993e444e80e400002055993e444f40480e000008ca05715925993e3a00000205711955a13e444e800000815c564566555113a00000205711b65b13e444e800000815f26556a4f9113a00000209711915993e444f700000815c464d664f9113b4000020f711915993e448e800000815c459940458e801800002057119159941444e80000083dc6645664f9113a000002057119159942444e800000815915993e444e806c000020571191599113a0b4000008fe05711914f9113bc0000209711914f9113a00800000815c7645674f9113a000002057c9c4645113a0a700000815c46d966444e82e00000205645684f9113a01200000815915993e444e810c0000205711914fd3e454e800000825c664d664f9113a0000020f645664f9113a01900000815c45993e444e803c000020d711934f9113a00800000815c4645684f9113b40000205711915993e448e9000008c9e771191599423a0000020571191599113a0a700000815c6645664f9113a40000207711935993e444e8000008d5915993e444e8064000020571194599113b00500000645664f9113a021028000020571191598e80940400000815cc645664f9113ac000020f721915993e444e800000815b65993e444e816c00002057119159942444f10000082dc464566509113a00000205645664f9113a41900000815c465566511113a00000205645684f9113c41200000815915993e444f110c0000207711915a13e444e800000815c46453e454e80200000205719915993e448e80000083d915993e444f1064000020571168501113a00e00000819c4645664f9133a0000024783d915993e444fa00000815c8645664f9113a40000205711955993e44ce800000815c4645664f9133b0000020571191598e80940500000815c564966444e80100000205711915b93e444e900000815915993e448e806400001915993e444f10840a0000083605729914f9113a00000212711b65993e444e800000815ca645113a0080080000205711914fd113a05800000815ec711b65a1113a000002057c9914f9133a01200000815c4645674f91a3a0000020f7119159940458e80000091e05715b6599113a000002056456c511113a01900000815c8699664f9113a00000205721915993e448e800000815c45993e458f10180000247815c4444e80200200000815c4645664f9133b40000247815664fd113a01900000815c464567444e802400002056453e444e80e4080000000205711914f9153bc000020571d9464566444e800000815c46456b4f9113a0000020f711664fd113a00a00000825f2711914f9113ac0000205711684f9113a00e00000815c4645113a09b0200000232815c4651663a00500000825c664566444e8008000020d71191444e80200200000825c6645664f9133a0000020571166505113a0aa00000849c459941444e803800002057119159942444f700000831c4645664f9113a00000247815c85993f444e800000815ca64d914f9113a0000020971191599113a09d00000825c4645664f9113ac000020571191505113a00800000829c465166444e80140000207711915993e44ce800000815c464542444e80200000247815c85993e450e800000815c464d6a4f9113a000002056556a4f9113a0190000083dc4645664f9163a000002057119559d3e444e80000083d915993e444fa02800002057119159d3e444ec00000815c564d664f9113a00000205711684f9113c40e00000815c85993e444ed038000020564566511113e81900000815915b13e444fa3a000002056d9684f9113a01200000815c56d966444e80280000205711915993e458e900000835ca711914f9113a0000020f6d9664f9113a0190000083e057113e444e8020000020a711915993e44ce800000815f27b1934f9113a0000020571193599113a00500000815c5645684f9113a000002057116650518444e800000815c7645113a006014000023271191599423a0020000083dc4645664f9163c40000205711b66458c454e800000815c4645674f9113b40000205711113a00a020020000083dc45993e444e82a00000205711914f9113a00900000815f27113e44ce80380000205711915993e478e800000815c464568444e80140000205719915993e458e800000815c464d664fd113a00000205711664f9133a00e000008c9c4645665091a3a00000205711935993e450e800000815c85993f444e80280000000835ca6453e444e800000815c44f9113a06e0380000205711915993e460e800000815915993e458e806400002077119159d3e444e80000091e05711113a0060140000205711915a13f444e800000815c464d3e444e80400000205729915993e454e800000815c4645684f9143a0000020571191444e82940800000815c4444e8038040080000232815c4645674f8e800000815c8645664f9163a000002057113e44ce80380400000815915b13e444e81300000205711664f9113a01d00000825c4645664f91a3a0000020f711664f9113a0cb00000815c664566444e80d00000205731915993e444ed00000815915b1664f9113e80000205711915a93e44ce80000081dc56d991599113a000002057119464566444ec00000829c4645674f9113a000002057edf264d3e444e800000815664f9113a0a80640000205715915993e44ce800000815c8645664fd113b400002057119159942444eb00000889c4655664f9113a000002057c9c4645133a00500000711915993e444fa084000020771191444e80200200000815c46556c4f9113a00000232815c56d991598e800000815c85993e444e82080000205721915993e450ed000008fe057c9954f9113a00000247711664f9113b420000008c9c465566509113a00000209711914f9133a00600000835c4645664f9153a00000205711914f9113a07000000815c4649684f9113a000002057c9ec6453e44ce800000815ca6d9934f9113a00000205711674f9113a00e00000815c46456644ce80140000000815664f9113a01d000008ca05711913a008008000020571191598eb094040000083dc46d9664f9163a00000205711915b53e444e800000815c4444e80280601400002056456c4f9113a012000008c9c4645664f8e824c0000205711914f9113a06500000815c46453e444e810000002057119159940444e800000825c4655664f9113a0000020571191579113a00800000815c4645664fd133a0000000083dc44f9113a00800000002056556c4f9113a00000205711664fd163a00a00000815c4645113b0060140000000815c465167444e800000815c56d9b1599113a000002055993e444e832c1900000825f26453e444e804800002057113e444e818c0e00000815c4645664f91c3a00000205655664f9113a05b000008c9c4645664f9113dc0000205711915993e444f500000815c464d6644ce8008000020571168501113a0060000083dc45993e444ed0180000205711915b53e444f100000815c464d3f444e80200000000815c45a141444e800000815915a13e444e812c00002057113e444e8064080000091e0571166505113a000002057159159d3e444e800000849c45993e460e8038000020b711914f9113a06500000815c4655664f9113e800002057119159940444f10000082dc464566501113a00000209711915993e444ed00000815c46d9664f91e3a0000020571191444ed0180500000815c45993e444f40c000002127edf25993e444e800000815c85993f444e803800002057119159d113a00500000815c46453e44ce81900000205729914f9153a00800000815fb7c9914f9133a00000205711925993e44ce800000815c4645664f9113a00000205711b65993e460e800000815c4645664f8e90940000205721664f9143a00e00000815c45993e458e820800002057119159942468e800000815c4645664f91b3a0000025391dc44f9113a00800000815915b13e444fa0640000205711664f9113a0ce00000815915a13e468e804800000008153e444e80640800000815c66453e444e81600000205721914f9113a05500000815c4645674fd113a0000020571591444e80200200000849c45993e444f43a00000247815c44f9153a00800000815c4645674f9143a00000205711915a13e444f4000008ca05711913a0060140000205711915993e444f10000082dc4645664f9113a00000205711864f9113a0aa00000815664f9113b4190180000212711864f9113a00e00000815c464d67444e800800002057116c4f9113a00e00000815955993e444e80e4000020d711914f9153a0080000083dc464568501113a0000020b711915993e46ce800000815c4599113a0820d0000020a71191444e8018050000082dc45993e444e8338000020571166505183a00e00000815c459941444e80280000205721914f9113a0580000091e3f7113e444e802000002057113e444e82a40800000825f27113e444e8038000020571166501113a0aa00000815c465566509113a0000020571191501113a0080000082dc4645664f9113c400002057119259d3e444e8000008159159944478e80640000205655684f9113a01200000825c45993e444e8038000020f711935993e444e80000083d955993e444e8064000023264566511113a019000008c9c46456a509113a000002127c9c45993e444f400000815f264566511113a000002057c9bd6553e444e80000083dc4645684f9113a000002057113e454e80280800000815c464566509113b40000205711935993e444e900000815c8645664fd143a00000205715b664966444e800000815c465166444e800800001c4645664f9113a0a300000825c44f9113a00e0100000205711945993e44ce800000815c461941444e803800002057113e444e83340800000815c4645664f9113dc0000209711915a93e444e800000815c45993e444e82a80000212711664f9113a00e00000815c46d9b1631863a000002057c9c664d3e444e8000008c991619664f8e8064000020571192444e80200200000815c46453e44ce80380000205711915a13e444e900000815c46453e444e802000002057b1915b13e444e800000825c5645664f9113a00000205711935993e448e800000815915a93e444e816c000020571191598ec094050000081dc464566509113a00000205719935993e444e80000083dc4645684f9113c40000205645664f9113a05f00000815915993e478fa3a000002097c9ec6453e444e800000815935993e444e8064000020971191599113a00500000815c4645684f9123a0000020b711915993e444f700000815c464d6f4f9113a000002127113e444e80380400000815c4645734f9113b40000205719915a13e444e800000815c46458c444e82000000205711915993e444ea0000083dc45993f444e801800002057b1e76d9b1598e800000815c85993e444f4038000020f711664f9113a07f0000083dc4669664f9113a00000205711914f9113c4080000082dc46453e444e8020000020f7119159944444e800000815c46456644ceb0140000205711935993e444ef00000815c56f5b6599113a0000020f711664f9143a00600000815c864d664f9113a00000205645684f9113a01900000825c4645664fd113a00000205711915b53e444eb0000083dc4645664f9133a00000205711915993e444f900000825c4645664f9143a00000205711916196644cec00000815c4651674f9113a0000020571191599133b0e800000815c46453e444eb100000020571193599113a03200000815c4645143a00601400002057119159940444eb00000815f27b1bd6d9113a0000020571191599153a00500000825c464d66444e80080000205721915a13e444e80000084a0571166505113a00000205711b159941444e800000815c459941444e80380000209711935993e44ce800000815c459942444e80380000205711664f9113a0a000000815c76456644ce80140000205711685053e444e800000815684f9113a0120380000205721934f9113a00400000815c4645664f9133a40000205645664f9113a01a00000815fb6456c4f9113a00000247815915b144444e800000815ca645864f9113a00000205711915993f454e800000815c4645674f92e3a000002057c9c66453e44ce800000815915993e478e813000002097edf26453e444e800000825c4649664f9113a0000020571141444e80380400000815f271191444e827400002055993f444e80640600000815c4645664f9173a00000205711915a140458e800000815664f9113a07f0640000205669664f9113a01900000815c46f9b659d113a0000020564566511113a01900000815c6645664f9133a000002055993e450e80640600000815c46456a509113a0000020571191599113a09d00000815c4645664f9113ac000020f711b65a13e444e800000815c4655664f91e3a00000205645664f9133a01900000815c45cd3e444e803800002057159159942444e800000849f2721664f9113a00000205711915993e474e800000815c46456f4f9133a00000232711955993e444e80000083dc4645674f9113a00000205711684fd113a00a00000815c664d3e444e80200000205711935993e458e800000815c8645664f9133a00000205711935995d444e800000815c764567444e801400002057119159d3e444e900000815c86453e444e81b8000020d711914f9113a0650000082dc4645664f9113ac000020571d915993e444e800000815915b13e478e80640000205711915a13e458e8000008c9915b13e444e806400002055993e444e80e00e00000815c4645665011a3a00000205729b66453e454e800000815ca645664f9113a000002478c9c44f9113a00800000815c464586444e80240000205711934f9113bc0800000815c46456644cec010000020572191444e80100200000815c45993e460f43a000002057119159942450e800000815c86453e44ce801000002327c99159942444e800000815c6645674f9113a00000205711864f9183a00e00000815c4645153a0080140000205711684f9113a08200000815664f9113a01d048000020571141444e8038080000083dc46d966444e8008000020d7c9c46453e444e800000815c4645684f9163c40000000849c459941444e80000083e05711664fd113a00000205645674f9113a0190000083de3645664f9113a00000205729914f9113a0040000094e47711664f9113b4000020571191599133b00500000711915993e444e808400002056556a4f9113a00a, 0x18bc118b810000018ac30000000000189c400000189031888218802187c1187810000000000187020000000000186c1186420000018601185c10000018581185411840518382183410000018283181c318181180c300000180421800117fc117f810000017f4117ec20000017e81000000000017e4117e0117d8217d4117d0117cc117c4217c0117bc1000000000017b4217b010000017ac117a4217a01179c100000179810000017941179011788217802000000000000000177c117742000001768317602175430000017501174821744117401173c100000173811728417202171c1171810000017102170c117042170010000016f8216f4116f010000016e8216e41000000000016d050000016c4316c0116bc1000000000016b81000000000016b02000000000016ac1000000000016a420000016a011698216941169010000016882168411680116782000001674100000166c216603165c116581165410000016501164c11648100000163c31638116302162c10000000000162810000000000162411620116143160c2000001608115f840000015f4115ec2000000000015e810000015e020000015d4315cc215c420000015b83000000000015b0215ac115a42000000000015a01159c11594215901000001588215802157c100000157810000015702156821560200000155c11558100000000001554115501154c10000015442153c200000153421530115282000001524100000151c2151421510100000150821500214fc10000014f42000000000014ec20000014e8114dc314d0314cc10000014c0314b8214b4114b0114a4314a0100000149c10000014942148c200000148811484100000147c2147810000000000000001474100000146c21464214601145430000014501144c1144810000014441000000000014401000000000000000000000000000000143c1000001438100000000000000000000143411428314202141c1141811414114101140820000013fc313f8113f4113f01000000000013ec113e8113e41000000000013e01000000000013dc10000013d8113d4113d0113cc113c8113c020000013bc10000013b4213b01000000000000000000000000013ac113a8113a41000000000013a01139821394100000138831380200000000001370400000136820000013602135c1135811350213404133c10000013381000000000013302132c11328113241131c21314213101130c113042000001300112ec512dc4000000000012d8112d4112c8312c020000012bc112b8112b41000000000012ac212a8112a02129821290212843127c2127811274100000126c212681000001264112601000001250412482124411240112382123020000000000122c11228112241121c21214212101120431200111f43000000000011ec211e8111dc311d8111d4111d0111cc1000000000011c030000011b4311b0111ac1000000000011a8100000000000000011a0200000119041188211841000000000011783117021168200000116410000011601115c10000000000114c400000000000000000000114810000000000113c30000000000000001138111245111c211142111011108200000110411100110fc10000010f810000010f0210e8210d450000010c8310c0210bc10000010b8110b4110b0110a8210a410000010a01109c1109810000010884107c310781106c3000000000010642105441050100000104c110481103840000000000000001034100000102c2102811024110201101c11010300000100821004100000100010ffc10ff030fe820fe41000000fd8300000000000fd020fcc10fc03000000fac50fa420f9c20f9810f9410f8c200000000000f881000000f8020f7040f6c10000000000000000000000000000000f6810f6020f5c10f5420f5010f4c10f4030f3820f3410f301000000f28200000000000f2020f1c10f1420f0c2000000f0810ef84000000ef410ef010ee8200000000000ee410edc20ed810ed410ec830ec410eb83000000eb410eac20e9c40000000000000000e9420e9010000000000000000e8c1000000e84200000000000e8010e7c10e78100000000000e7410e701000000e682000000000000000000000e6020000000000000000e582000000e541000000e501000000e482000000e4410e3c20e3420e3010e2c100000000000e2810e2410e2010e1820e141000000e1010e043000000df83000000df410dec20de810de020dd820dd41000000dd010dcc10dc810dc4100000000000dc010dbc10db810db02000000da430da010d9c1000000d9810d902000000d882000000d8410d8010d782000000d74100000000000d7010d5c500000000000d54200000000000000000000000000d50100000000000d48200000000000d4410d4010d382000000d3410d2830d1c30d1810d14100000000000d1010d0c10d0810000000000000000cfc30cf030cec1000000ce030cd040ccc10000000000000000cc420cc010cb820cb410ca44000000c9c200000000000c9030c8c10c8810c8410c8010c78200000000000c7020c6430c583000000c4c30c4810c4410c4010c3c1000000c3810c3020c2c100000000000c28100000000000c20200000000000c182000000c1410c0c20c081000000bfc30bf420bf01000000be820be02000000bdc10bd420bd010bc820bb06000000ba820000000000000000ba410b98300000000000b941000000b9010b88200000000000b7c30b7420b6c20b642000000b601000000b5c1000000b581000000b5410b501000000b4c10b481000000b441000000b4010b3c10b303000000b2820b2410b1c2000000b1810b1410b1010b0c1000000b0420b0010000000000000000afc1000000af810af41000000af010aec10adc40ad810ad410ad010000000000000000ac820ac410ac01000000abc1000000ab42000000aa830aa020a9c10a981000000a90200000000000a8c10a8810a802000000a7c100000000000a7810a702000000a6c1000000a6810a6410a6010a5430a5010a4c10a481000000a3c3000000a38100000000000a3020a2040a104000000a0c1000000a0810a04109fc2000000000009f42000000000009f0109e8209e4109d830000009cc309c030000009b8209b0209a82000000000000000000000000009a41099c20998100000099020988209802097820974109701096c109642000000000009601095c10958109541094c209481094020000000000093c100000093810934109301000000000000000092c10928109241091c209181091020908200000000000000000000000000904108f8308f4108ec208e4208dc208d42000000000008c830000008c4108bc20000008b8108b4108ac208a4208a01000000000000000089c10898108941088c2000000000000000000000888100000000000000008802087820874108701086c10000008681000000864108601000000000008543084c20840300000083430000008301082c10000008242081c2000000000000000081810814108101080c1000000804207f4407f0107ec10000007e8107e4107d8307d020000007cc107c4207c0107bc107b81000000000007b4107b0107ac10000007a8107a4107a010798207902078c100000078810000007802000000000000000077c10000007742076c2075c40758107541075010748207402073c10738100000000000734100000073010000000000072c10000000000071c400000071810000007141070c207081000000700206f8206f0206ec10000006e8106e0206d8206d410000006cc20000006c810000006c4106b8306b4106b0106ac100000000000000006a8106a41069830000000000000000000006902068c10684200000067c20000006781067410000000000067010668200000065c30650300000064820644106401063c1000000638106302000000000006282000000624100000000000620100000061c1000000000000000000000618106141000000610100000060c1000000608105f840000005f4105e8305e4105e010000005d8205d4105d0105cc105c4205c0105bc105b420000005b0105ac105a03059c100000059420000005901000000000000000058c10000000000058420000005801000000578200000057410570105643000000000005601055820548400000000000544105401053820534105301052c10000000000000000000005281000000524100000051c2000000518100000000000000000000050c3050420000004fc204f8104f4100000000000000004ec200000000000000004e81000000000004e4104dc204d8104d4104d010000004c8204c4104bc204b8104b020000004ac104a42000000000000000049c200000049810494104901048c10488104802047c104742046830464104601045c104581000000454104444000000440100000043c1000000000004381043410430100000042c1042810424100000041c204181041020408200000000000400203fc10000003f4203f010000003e8203e020000003d8203d4103d010000003cc10000003c8103c4103bc203b8103b0203ac103a81039c303981039410000003901000000000000000038c100000000000388103802037c103781036c303681000000364103601035c103581000000354103501034c1034030000003382000000334100000000000330103282000000000003241032010000000000031c1030c40304203001000000000002f8202f410000002f0102ec102e8102dc302d81000000000002d020000002cc102c810000000000000000000002c410000002c010000002bc102ac400000000000000002a4202a010000000000029c100000000000000002981000000000000000029410000002901000000288200000027c30000002742026c20000002681026410260100000025820254102501024430000002401023c10238102341022c202281022020000000000021820000002141000000000000000000000000002101020c1020030000001fc101f03000000000001e430000001dc201d4201d0101c430000001bc20000001b0301a820000001a4100000000000000001a0100000019c1019420190101882017c30178101741016c201681015c3015810000001541000000000001501014c1014030138201341000000130100000012c1000000128100000000000000000000011c300000000000000001103010820000000fc300f8100f4100f0100ec100e8100e41000000000000e0100d820000000d410000000cc200c4200c0100b8200b410000000000000000000000ac2000000000000a8100000000000000000a02000000000000000009c100000009030084300000000000000000000007c200000007810070200682006410060100000005c100000005810054100000004c20048100000000000044100000000000040100000003c100381002c3000000028100184000000010200000000c10000000081000000000000002, 1584, 1584⟩
def t5 : Archive := ⟨0x815b64f9113a01e000000021271186505113a000000008c9915993e478fa000000020571166505183d00000000815c46c586504e80000000205655664f91e3e80000000815c4599113a01100000002057113e444f50400000000815c44f9113bc10000000020571141460e80200000000815664f91e3e80600000002056456c511113e8000000091dc45993e484ed0000000205711b659d163a00000000815c4645113a0090000000235645664f91e3e80000000829c465166444ec00000002056d966444e80680000000815b659944478e800000002057219144ce80140000000815c461d3e460f400000002056456c5111e3a00000000815c45a141460e800000001915993e4442b0640000000815c459941460e800000000008153e444e8078000000084dc44f9113a008000000020a7cdc7645113a00000000815c44f9113ac10000000020572d91444e80240000000849c44f9113a0100000000212721664f9143a0000000081dc5645113a0080000000232645665111e3a00000000815c4645153bc0200000002056556c4f91a3a00000000815c4444ec038050000000205655665111e3a00000000815c44f9113a01100000002057116c505113a00000000815c8645113a009000000020559944478e801800000008ce0a71d91598e800000002057113e464e8038000000000205711113a0110000000235645665111e3a00000000815c44f9163c40800000002057c993509113a00000000815c859941460e8000000020f711664f9143b40000000815915993e478fa0000000205711914fd153bc0000000825c46456644cec00000002057293e454e803800000009260d7293e444e8000000020571d9459d113a00000000815c4651663b0250000000232815c8644e80140000000815915a142468e8000000020571186444e80440000000815c46456644cec00000001915993e444e80880000000815914f9113a01e0000000205711913bc250200000000815c46d969444e8000000020f711113a0080080000000815ca6453e44ce80000000205729914f9153bc0000000815664f9113ec1d000000020571140444e8040000000083dc44f9153a008000000020d71191444ef0080000000835c46453e454ef000000020f711113a0060140000000815664f91a3a01d000000020571141454e80380000000839c4645113a009000000020571168505113d0000000082dc8645113a00500000002056dd665111e3a00000000815c461941460e80000000205721914fd133a00000000815c4444e8044050000000205645665111e3a00000000815c4645113a0110000000205711914fd153b40000000711915993e488f70000000205711915993e0a40000000825c4645663ac25000000020f7113f444e802000000008ce0a71191598ec000000020572d91444e80140000000835c46453f444ef000000020a71d9159d113a00000000829c4645663b025000000020d7293e444e80380000000815c464d3e454ef000000020f645664f91e3e80000000815c46455e454e800000002054f9113a0150380000000829c4444e803805000000020571168505113a00000000815c44f9133a01000000002057119144cec018000000083dc45a13f444e8000000020571141460e8010000000083dc45993f444e8000000020571191454e802400000008c93e444e80640800000002327c991619423a0000000083dca4f9113a008000000020572191444e80140000000815c64f9113a010000000020571191598e80980000000815c44f9183a01000000002057119459d113b00000000835ca6453e444ef000000020571d91444e8024000000083d9159944444fa00000002057113e44ceb0380000000849664f9113e80e00000002054f9133a01901800000006456c4f9113a02100000002477116d4f9113b4000000091e057113f454e800000002127113e44ce80380000000815c4501163a0080000000205721934f9133a0000000083d9159944478e8000000020572168505113a00000000815c4649113a0090000000205729934f9113bc000000083dc85993f444e800000002055993f444ed0640000000835c464d3e444ef0000000247815ca4f9153a00000000815c4444e802c08000000020571191598290140000000855c4645864f8ed00000002327c9956193e3a00000000815ca645113a009000000020571191444ec0200000000815c4645143b40500000002125993e444e8074000000081566505183a01200000002478fdc44f9113bc000000083dc45a141444e800000002057c991444e80580000000825c464566444ec000000020f71166505113a00000000835c4645113a009000000020a7119159d113b00000000815c4645113c00800000002478c9c43a0080080000000825ca6453e444e800000002057c9c4444e80440000000815ca64d3e444eb00000002055993e444ed0740000000815c86453e454e800000002478c9c43a006014000000091e32721864f8e800000002057c9ec651113a000000008153e444e806408000000020f711864fd113a000000008c9864f8e80480e000000020571191444ec024000000084966505113a019000000020571193444e80240000000815c76456644cec00000002057113e444f40400000000815c4645113c0090000000205711664fd163c40000000645664f9113e82200000002056556c509113a00000000829c465167444e80000000247835ca4f9113a00000000825c44f9113a0100000000212711664f9113b40000000645684f9113a02100000001c4645664f9223e80000000815c44f9113a01e0000000232645674f8e80640000000815664f9113dc0e00000002057113e454ef02800000008c9c4655663a00500000002057113e444e80400000000815c461d41460e80000000205645665111e3e80000000815c4651113a009000000020571d94599133a00000000829f27b191444e800000002097113e444eb038000000081dc564d66444e800000002057193e44ce8038000000083d3e444e80640800000002398c9c7645663a00000000815c56d968444e800000002326556c4f9113a00000000849c85993e444ed000000020572991444e80140000000815f27119144cec000000020b711914fd153a000000008156c4f9113e80e00000002055a141444e80480000000815c84f9113a010000000020559942444e8074000000091dcc5993e444ed000000020571193599133b00000000859c4645663a00500000002055993e460e807400000008156c4fd113a019000000020571191450e80240000000815915b142444e80000000205729934f9133a00000000835c44f9113bc0a000000020571191444ea02000000006456c4f9113e82100000002057159459d113a00000000829c4645113a0090000000212711664f9183d00000000829c76456644ce8000000020f7113e444e804000000008156a509113a00e00000002055993e450ed06400000008c9664fd113a019000000020571191454ec02000000008ca0571d94598e800000002055b13e444e80740000000815c46453f454e80000000205711113a0100140000000815915993e458fa00000002057b1b65b1113a0000000091e32711864fce800000002055b144444e80380000000815c46516644cec000000020571191599153b0000000083dc56d966444e800000002325993e444e80740000000815c4644e8094080000000205444e80640800800000008153e444e806c06000000020564566444e807000000008153e454e8064080000000205729914f9153a00000000815c464d663ac250000000205711113a00a02400000008e63271191598ec00000002056556c4f9113a00000000815113a01901805000000020b5993f444e80640000000849c4444e80380500000002055b141444e80640000000815c8645113b00500000002057113e44cf40380000000815c4645663b0260000000212795664f9113d00000000815c86453f454e800000002054f9113e819020000000081dc465167444e80000000232645664f8e80680000000815c461d41444e8000000020571d94444e80200000000815c46458651ced00000002097113e44ce803800000008153f444e8064080000000232829c7645663a0000000082d664f9113a01d00000002054f91e3a0190200000000815c4444e803406000000020571191505153a0000000084dc44f9113a01000000002055993e444fa0380000000849c85993e460e80000000205711113a0100080000000825c64f9113a00e000000020f7113e458e80200000000815664f9113d01d00000002057113e44ce8038000000083d915993e458fa000000020571591444e80240000000829c46456644cec00000002057113e454e804000000009260d7113e444ef000000020571d94599113a00000000849e55993e444e800000002055993f444e806400000008153e444e8074080000000232815c4651663b00000000815c8651113a005000000020f711b659d113a00000000645664f9163c421000000020d4f9113a0190200000000835ca6453e444e80000000205711996193e3b4000000081544444e80640800000002055a13e444e80740000000645664f9223a019000000020f6556c4f9113a00000000815664f9113a01d00000002057113f444e8040000000082dc46453e44ced00000002056dd6c4f9113a00000000815ca645153a0050000000209729934f9113a000000008153e444e8048100000000212711684f9113d00000000815c464d66444ec00000002057213e44ce80380000000849c45993e444f40000000205729934f9113a00000000849c44f9113a008000000020f711664fd143a00000000849915993e444fa00000002057293e444e80400000000815c8645143a005000000020571d94444e80180000000829c764566444e8000000020571194444ec020000000081dc4645113a0090000000232829c4645663b00000000835c44f9113a0100000000216711915993e3b0000000081566505113a019000000020f7113e444f10200000000829c8645113a00500000002478c9c56d9663a0000000083d664fd113a0190000000205711133a00e014000000083dc44f9113bc08000000020571194599113b00000000849c85993e444f400000001c4645664f9110ac0000000815c4460e8038050000000205729944f9113a00000000815c4505113a01000000002057c991509133a0000000083d664f9113a01d00000002056193f444e80640000000815c86453e44ceb0000000205795664f9183d00000000815b65b13e444fa0000000205711113a00e02400000008c9e7645664f8fa0000000212721684f9113a000000008c9c4645663a016000000020a71d91444e80180000000815c4444e803c040000000205721914f9133b40000000849c85993e444e800000002056193e444e807400000008c9915b13e444fa00000002056556c4f9113e8000000091e057113e454ef0000000205729914fd153a00000000815c4645113bc090000000212711864f9113d0000000091e32711b659ce80000000232815c43a00e0140000000815c46c5864f8f4000000020a71191599113b00000000815955b13e478e8000000020d711914fd153a00000000859c4645663b00500000002057c9954f9133a00000000815c5649113a008000000023271591599423a00000000815b65b144444e800000002057119159d133b00000000815915a13e444f700000002054f9113a01d01000000008c9e764566510e8000000020d72991444e80080000000815c45a13e460f4000000020d729914f9153a00000000815664f91f3a01d000000020572994444e80140000000815c45993e460f400000002326456c511113a0000000081566515113a01900000002127113e444f40100000000815c464d3f454e80000000247815c84f9133a00000000815955b144444e800000002055993f444fa0640000000815c464d66444ea00000002055b144444e801800000008153e44ce80480e00000002057113e464e80400000000815c4645113b4090000000205711113d00e0140000000815c45a141458e800000002055993f478e8064000000083dc4501113a008000000021271166505183a0000000083d9159940444fa000000020571166505163a00000000815ca64d113a00200000001915993e488fa0640000000815665091a3a00e0000000247835c44f9113bc000000083dc45993f458e800000002057119459d133a00000000835ca6453f444e800000002054f9113a01e0640000000815ca64d3e454e800000001915993e478fa0840000000815664f9113e81d000000020a71191444ec01800000008c9c5655664f8e80000000216711915993e3a800000008153e444e80641000000001915993e444f10880000000815915b13e444fa00000002055993f444e807400000008ce0571191598ec0000000212721864f9113a00000000815c464d663a02500000002055993e478e80740000000815c85993e460f400000002327119159d423a00000000815c4444e80380500000002097c991509113a00000000815ec6d966478e800000002326193e3a0190180000000825c86453e444eb0000000205711113a0110380000000815f371194444e80000000205729934fd113a00000000815f271d94444e800000002125993e444f40480000000815c4505133a00e0000000247815c4444e802400000008c9b6598e8064020000000235645664f9113e80000000815c765166444ec000000020559944444e80740000000849c84f9113a00400000002056dd6c511113a0000000082dc4645113b40500000002056456c511113a00000000849c45993f444e800000002055a93e444e80740000000815c4651663a02500000002127293e444e80200000000815c45a141444f10000000232815c4651673a00000000815c8444e8038050000000205711864f9183d00000000835ca64d3e444e800000002327119559d3e3a0000000083dc45993f444f1000000020559941444e8074000000083db65993e444fa000000020571191579153bc0000000815c565166444e800000002478fdca4f9113a00000000825f26553e444e8000000020f6456c4f9113e80000000849ca5993e444e80000000232645663a0190140000000926057293e444e800000002057119144ce80240000000849c459941444f4000000020a7c9c7645113a00000000815c44f9153a00e000000021271141444e8020000000083d955993e444fa0000000212721664fd113a00000000815b659d113a01900000002057113e460f40100000000815915a13e444fa000000020a71d91599113b00000000815c46d966458ea000000020f5993e444fa01800000008153e444e80600a000000020f7113e44ce80180000000849c45a141444e800000002057c9c4651113b00000000815c44fd153a00a0000000205711914f9153bc000000082dc86453e44ce800000002055993e444fb0380000000849c459941444e800000002057c9974f9113a0000000083d915b144444e8000000020571191598eb098000000091e054f9113a01e00000002057113e458e80400000000835c46455e444ef000000020f711664fd113b40000000815c465167444e800000002055993f450e80640000000815c8645113b4050000000209721914f9133a000000008c9f2644e8048050000000232815c4644e80240000000829c765166444e800000001664f9113d0210380000000815c56d966458e80000000205721914f9133a00000000815664f9183d01200000002054f9113a01e0200000000849c859941444e800000002055993e450e80740000000815f2655113a0050000000205711914f9153b400000008153e444ef06408000000020f645684f9113e80000000829f271191444ec00000002097c9914f9113dc000000083dc44f9113a00800000002478c9c46193e3b4000000081566515113a01d000000020f645664f9113e80000000815c7444e803805000000020d711914f9113bc000000082dc4645113a009000000020571991599133b00000000815664f9113a01e00000001664f9113a0210380000000815b65993e478fa00000002057cdc7651113a00000000645684f9113c42100000002056456c4f91e3e80000000815c4645153bc050000000247815c8444e80140000000849664f9113d019000000020b5993e444ed0640000000815c44f9113c410000000020d7293e444e80280000000815113a01203805, 0x84810000008441000000840108382082c308281000000000008241082010810400000000000000008082080410000007fc207f8107f020000007ec107e4207e0107d8207d41000000000007d0107c820000007c0207b8207b0200000000000000007ac107a420000007a01079c1079810794107901078c1000000000000000000000788100000078410774400000077010000007643000000000007601075c10000007503074c107481000000744107401073c107381072c300000000000000007242071c2071810710207082070410700106fc106f810000006f410000006e830000006e410000006e0106dc106cc406c8106c0206b8206b0206ac10000006a8106a4100000069c206981068c30688106802067c1067810674100000000000000000000066c20664206601000000650400000064c1000000000006481064020000000000063c1000000000006381063410000006301062430620106104060820600205fc105f8105f4105f0105e8205e4105dc205d42000000000005d01000000000005cc10000005c030000000000000000000005bc105b4205ac205a81000000000005a410000005a0105982059410000005901000000000005882058410580100000057c100000056c4000000568100000056410000005601055c105581000000550200000054c100000054810000005402000000538205341000000000000000052c205281052410000000000000000520100000000000518205141050c2050810500204fc104f8104f4104ec20000004e8104e4104e010000004d040000004c8204c4104c0104bc104b420000004b010000004ac104a8104a41000000000004a0100000048c5000000488100000048020474304701046c1046810464100000046010458204541045010000000000044430000000000043c20434204283042410420100000041820000004102040c10404203fc203f4203ec203e4203dc203d4203d0103cc10000003c810000003c410000003bc203b8103b020000003a8203a410000003a01039c103903038c10000000000038810384103801037c1037810000000000037410000003701036c10364203601035c1035810354103501034820340203382000000330200000032c10000000000000000000003281032410000000000031c20318103102030c103042000000300102fc102f8100000000000000002f410000002f010000002ec102e030000002d43000000000002d010000002cc10000002c8102c4102c0102bc10000002b4202b0102a4302a0102982000000290200000028c10000002842000000280100000027c100000000000278102702026c1025c402581024c3024810000000000000000244102401023430230102282022410218302102020c101fc401ec401e8101e4101e0101dc101d4201d010000001cc101c420000001b830000001b4101b0101ac101a8101a41019c200000019420000000000000000000001901018820000000000017c3017810174101701000000168201641015c200000015810150201482000000000001441013c20128500000012410000000000011c2000000114200000011010000001082000000000001041000000100100f43000000000000ec200e4200e010000000dc100d8100d0200c4300c010000000bc100b42000000000000b010000000ac100000000000000000a42000000098300000009020000000000008c1008810000000841000000000000801007820074100701006c1006810064100601000000058200502004820044100401003c100381002c3000000000000000002030000000182001410000000101000c1000000008100002, 531, 531⟩
def t6 : Archive := ⟨0x2125993e444fb000000000083d3e444fa0200000000002054f9113a01e0000000000815ca651113b00000000002324f9113a01e000000000091e32720e80140000000002326193f3a01900000000008153e444fa04000000000021271141454e800000000008153e444fa07800000000020d4f9113a01e00000000008353e444ef064000000000205444e807006000000000084966505113e80000000002054f9153a01e00000000008153e454ef064000000000205444e80580e000000000084d3e444e8078000000000212721113a0050000000000815664fd1e3e800000000020e71191444f000000000008153e480e807800000000020572d94444e80000000000815c4460f40140000000002323a019020020000000000849c44f9133d000000000020e72d91444e800000000008c991598e8070000000000205711133a0110000000000815c4444ec044000000000205711913bc2700000000008153e444fc0780000000002055b145444e80000000000815c4645660a8000000000205711193a0110000000000815665151e3a00000000001915993e4782c0000000000815c4444e80440000000002326193e3a01d0000000000645664f9110b000000000020a711915982a0000000000815c4505193a0000000000205711133b00e0000000000645664f9233e8000000000205721113a0110000000000829c4444e80440000000001915b13e488fa000000000083dc44f9153bc0000000001664f9113d02300000000006456c4f9110ac0000000002054fd153a0190000000000815665151f3a00000000002054f91e3e8080000000000859c4651663b0000000000214711113a0110000000000849ca4f9153a0000000000205711113d8110000000000815c4444ec04000000000020a711113b00e00000000008156c505113e80000000002054f9113bc1e00000000008153e44ce80740000000002327c9913a0160000000000815664f91f3ec00000000020572991454ec0000000000815c44f9193d4000000000205444e806409000000000083d3e444e8078000000000212711113d005000000000081544444e8078000000000205711183a0110000000000815113a01e008000000000205444e8068080000000000835c4645113c000000000020a72d91444e800000000008ca05710e80440000000002055993e460fb000000000084dc44f9113d400000000020571191454f0000000000083dc44fd153a00000000002054f9153a01d0000000000815c44f9193d000000000020d711913bc25000000000083d664fd113e800000000021771191598ec000000000091e32710e802400000000020571d113a01100000000008c8e80480e0140000000002054fd113a01e0000000000815c4444f4044000000000205711913a027000000000083dc4444e802400000000020571194598290000000000815113a01d0140000000002127213e44ce800000000008c9b6598e8068000000000212711113a0090000000000815c8645133b00000000002323a01901805000000000084dc44f9113bc000000000205444e8048110000000000849c4444e80440000000002137293e444e800000000008c9f2654e80140000000002055111e3a00800000000005993e444e808c0000000001664f9183d02100000000008153e478e807800000000020a72191444ec0000000000815cb444e804400000000020a71d113a00e000000000081545444e80780000000002326d9673a019, 0x1bc201b8101b4101ac20000001a81000000000001a41019c201942000000190100000018430180101782000000174100000000000000000000016c2000000160301582015020000000000014c10144200000013830130200000012c10128101241012010118201141010c200000000000100300f820000000f4100f01000000000000ec100e8100dc300d8100c8400c0200b82000000000000b4100b01000000000000a430000000000000000000000a010000000000009820094100000008c20084200801007820000000000006c30000000000000000064200000005c2005420000000501004c1004810044100401003820000000000000000030200000002c1002420000000201001c1001810000000000001410008300002, 113, 113⟩
def t7 : Archive := ⟨0x2323a012044000000000000851c4444f60000000000002134f9113f00000000000008153e480fc0000000000002323a01d0140000000000008c8e8078020000000000002323a019024000000000000851cb444e8000000000000205444e807c000000000000815c4464f6000000000000205515203a00000000000008c8e80580e0000000000002323a01a0200000000000008c8e807006, 0x34100301002c10020300000001c100181001410000000000000830000000002, 14, 14⟩
def t8 : Archive := ⟨0x2323a01f, 0x1, 1, 1⟩
def t9 : Archive := ⟨0x0, 0x0, 0, 1⟩
def t10 : Archive := ⟨0x0, 0x0, 0, 1⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level9 : ∀ i < t9.count, noneLive 1 (t9.get tableDict i) := by intro i hi; change i < 0 at hi; omega
def ok8 (i : Nat) := flag tableDict t9 1 (t8.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert8_0 : span ok8 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level8 : ∀ i < t8.count, noneLive 2 (t8.get tableDict i) := by
  apply allRows (hn:=level9)
  intro i hi
  change i < 1 at hi
  change ok8 i = true
  exact (span_ok cert8_0 i (by omega) (by omega))
def ok7 (i : Nat) := flag tableDict t8 2 (t7.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert7_0 : span ok7 0 14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level7 : ∀ i < t7.count, noneLive 3 (t7.get tableDict i) := by
  apply allRows (hn:=level8)
  intro i hi
  change i < 14 at hi
  change ok7 i = true
  exact (span_ok cert7_0 i (by omega) (by omega))
def ok6 (i : Nat) := flag tableDict t7 3 (t6.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_0 : span ok6 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_16 : span ok6 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_32 : span ok6 32 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_48 : span ok6 48 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_64 : span ok6 64 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_80 : span ok6 80 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_96 : span ok6 96 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert6_112 : span ok6 112 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level6 : ∀ i < t6.count, noneLive 4 (t6.get tableDict i) := by
  apply allRows (hn:=level7)
  intro i hi
  change i < 113 at hi
  change ok6 i = true
  exact (if h : i < 64 then (if h : i < 32 then (if h : i < 16 then (span_ok cert6_0 i (by omega) (by omega)) else (span_ok cert6_16 i (by omega) (by omega))) else (if h : i < 48 then (span_ok cert6_32 i (by omega) (by omega)) else (span_ok cert6_48 i (by omega) (by omega)))) else (if h : i < 96 then (if h : i < 80 then (span_ok cert6_64 i (by omega) (by omega)) else (span_ok cert6_80 i (by omega) (by omega))) else (if h : i < 112 then (span_ok cert6_96 i (by omega) (by omega)) else (span_ok cert6_112 i (by omega) (by omega)))))
def ok5 (i : Nat) := flag tableDict t6 4 (t5.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_0 : span ok5 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_16 : span ok5 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_32 : span ok5 32 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_48 : span ok5 48 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_64 : span ok5 64 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_80 : span ok5 80 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_96 : span ok5 96 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_112 : span ok5 112 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_128 : span ok5 128 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_144 : span ok5 144 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_160 : span ok5 160 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_176 : span ok5 176 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_192 : span ok5 192 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_208 : span ok5 208 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_224 : span ok5 224 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_240 : span ok5 240 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_256 : span ok5 256 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_272 : span ok5 272 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_288 : span ok5 288 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_304 : span ok5 304 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_320 : span ok5 320 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_336 : span ok5 336 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_352 : span ok5 352 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_368 : span ok5 368 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_384 : span ok5 384 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_400 : span ok5 400 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_416 : span ok5 416 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_432 : span ok5 432 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_448 : span ok5 448 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_464 : span ok5 464 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_480 : span ok5 480 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_496 : span ok5 496 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_512 : span ok5 512 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert5_528 : span ok5 528 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level5 : ∀ i < t5.count, noneLive 5 (t5.get tableDict i) := by
  apply allRows (hn:=level6)
  intro i hi
  change i < 531 at hi
  change ok5 i = true
  exact (if h : i < 272 then (if h : i < 128 then (if h : i < 64 then (if h : i < 32 then (if h : i < 16 then (span_ok cert5_0 i (by omega) (by omega)) else (span_ok cert5_16 i (by omega) (by omega))) else (if h : i < 48 then (span_ok cert5_32 i (by omega) (by omega)) else (span_ok cert5_48 i (by omega) (by omega)))) else (if h : i < 96 then (if h : i < 80 then (span_ok cert5_64 i (by omega) (by omega)) else (span_ok cert5_80 i (by omega) (by omega))) else (if h : i < 112 then (span_ok cert5_96 i (by omega) (by omega)) else (span_ok cert5_112 i (by omega) (by omega))))) else (if h : i < 192 then (if h : i < 160 then (if h : i < 144 then (span_ok cert5_128 i (by omega) (by omega)) else (span_ok cert5_144 i (by omega) (by omega))) else (if h : i < 176 then (span_ok cert5_160 i (by omega) (by omega)) else (span_ok cert5_176 i (by omega) (by omega)))) else (if h : i < 224 then (if h : i < 208 then (span_ok cert5_192 i (by omega) (by omega)) else (span_ok cert5_208 i (by omega) (by omega))) else (if h : i < 240 then (span_ok cert5_224 i (by omega) (by omega)) else (if h : i < 256 then (span_ok cert5_240 i (by omega) (by omega)) else (span_ok cert5_256 i (by omega) (by omega))))))) else (if h : i < 400 then (if h : i < 336 then (if h : i < 304 then (if h : i < 288 then (span_ok cert5_272 i (by omega) (by omega)) else (span_ok cert5_288 i (by omega) (by omega))) else (if h : i < 320 then (span_ok cert5_304 i (by omega) (by omega)) else (span_ok cert5_320 i (by omega) (by omega)))) else (if h : i < 368 then (if h : i < 352 then (span_ok cert5_336 i (by omega) (by omega)) else (span_ok cert5_352 i (by omega) (by omega))) else (if h : i < 384 then (span_ok cert5_368 i (by omega) (by omega)) else (span_ok cert5_384 i (by omega) (by omega))))) else (if h : i < 464 then (if h : i < 432 then (if h : i < 416 then (span_ok cert5_400 i (by omega) (by omega)) else (span_ok cert5_416 i (by omega) (by omega))) else (if h : i < 448 then (span_ok cert5_432 i (by omega) (by omega)) else (span_ok cert5_448 i (by omega) (by omega)))) else (if h : i < 496 then (if h : i < 480 then (span_ok cert5_464 i (by omega) (by omega)) else (span_ok cert5_480 i (by omega) (by omega))) else (if h : i < 512 then (span_ok cert5_496 i (by omega) (by omega)) else (if h : i < 528 then (span_ok cert5_512 i (by omega) (by omega)) else (span_ok cert5_528 i (by omega) (by omega))))))))
def ok4 (i : Nat) := flag tableDict t5 5 (t4.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_0 : span ok4 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_16 : span ok4 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_32 : span ok4 32 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_48 : span ok4 48 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_64 : span ok4 64 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_80 : span ok4 80 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_96 : span ok4 96 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_112 : span ok4 112 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_128 : span ok4 128 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_144 : span ok4 144 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_160 : span ok4 160 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_176 : span ok4 176 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_192 : span ok4 192 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_208 : span ok4 208 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_224 : span ok4 224 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_240 : span ok4 240 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_256 : span ok4 256 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_272 : span ok4 272 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_288 : span ok4 288 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_304 : span ok4 304 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_320 : span ok4 320 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_336 : span ok4 336 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_352 : span ok4 352 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_368 : span ok4 368 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_384 : span ok4 384 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_400 : span ok4 400 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_416 : span ok4 416 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_432 : span ok4 432 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_448 : span ok4 448 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_464 : span ok4 464 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_480 : span ok4 480 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_496 : span ok4 496 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_512 : span ok4 512 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_528 : span ok4 528 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_544 : span ok4 544 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_560 : span ok4 560 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_576 : span ok4 576 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_592 : span ok4 592 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_608 : span ok4 608 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_624 : span ok4 624 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_640 : span ok4 640 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_656 : span ok4 656 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_672 : span ok4 672 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_688 : span ok4 688 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_704 : span ok4 704 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_720 : span ok4 720 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_736 : span ok4 736 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_752 : span ok4 752 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_768 : span ok4 768 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_784 : span ok4 784 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_800 : span ok4 800 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_816 : span ok4 816 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_832 : span ok4 832 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_848 : span ok4 848 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_864 : span ok4 864 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_880 : span ok4 880 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_896 : span ok4 896 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_912 : span ok4 912 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_928 : span ok4 928 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_944 : span ok4 944 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_960 : span ok4 960 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_976 : span ok4 976 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_992 : span ok4 992 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1008 : span ok4 1008 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1024 : span ok4 1024 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1040 : span ok4 1040 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1056 : span ok4 1056 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1072 : span ok4 1072 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1088 : span ok4 1088 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1104 : span ok4 1104 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1120 : span ok4 1120 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1136 : span ok4 1136 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1152 : span ok4 1152 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1168 : span ok4 1168 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1184 : span ok4 1184 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1200 : span ok4 1200 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1216 : span ok4 1216 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1232 : span ok4 1232 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1248 : span ok4 1248 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1264 : span ok4 1264 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1280 : span ok4 1280 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1296 : span ok4 1296 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1312 : span ok4 1312 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1328 : span ok4 1328 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1344 : span ok4 1344 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1360 : span ok4 1360 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1376 : span ok4 1376 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1392 : span ok4 1392 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1408 : span ok4 1408 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1424 : span ok4 1424 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1440 : span ok4 1440 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1456 : span ok4 1456 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1472 : span ok4 1472 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1488 : span ok4 1488 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1504 : span ok4 1504 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1520 : span ok4 1520 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1536 : span ok4 1536 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1552 : span ok4 1552 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert4_1568 : span ok4 1568 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level4 : ∀ i < t4.count, noneLive 6 (t4.get tableDict i) := by
  apply allRows (hn:=level5)
  intro i hi
  change i < 1584 at hi
  change ok4 i = true
  exact (if h : i < 784 then (if h : i < 384 then (if h : i < 192 then (if h : i < 96 then (if h : i < 48 then (if h : i < 16 then (span_ok cert4_0 i (by omega) (by omega)) else (if h : i < 32 then (span_ok cert4_16 i (by omega) (by omega)) else (span_ok cert4_32 i (by omega) (by omega)))) else (if h : i < 64 then (span_ok cert4_48 i (by omega) (by omega)) else (if h : i < 80 then (span_ok cert4_64 i (by omega) (by omega)) else (span_ok cert4_80 i (by omega) (by omega))))) else (if h : i < 144 then (if h : i < 112 then (span_ok cert4_96 i (by omega) (by omega)) else (if h : i < 128 then (span_ok cert4_112 i (by omega) (by omega)) else (span_ok cert4_128 i (by omega) (by omega)))) else (if h : i < 160 then (span_ok cert4_144 i (by omega) (by omega)) else (if h : i < 176 then (span_ok cert4_160 i (by omega) (by omega)) else (span_ok cert4_176 i (by omega) (by omega)))))) else (if h : i < 288 then (if h : i < 240 then (if h : i < 208 then (span_ok cert4_192 i (by omega) (by omega)) else (if h : i < 224 then (span_ok cert4_208 i (by omega) (by omega)) else (span_ok cert4_224 i (by omega) (by omega)))) else (if h : i < 256 then (span_ok cert4_240 i (by omega) (by omega)) else (if h : i < 272 then (span_ok cert4_256 i (by omega) (by omega)) else (span_ok cert4_272 i (by omega) (by omega))))) else (if h : i < 336 then (if h : i < 304 then (span_ok cert4_288 i (by omega) (by omega)) else (if h : i < 320 then (span_ok cert4_304 i (by omega) (by omega)) else (span_ok cert4_320 i (by omega) (by omega)))) else (if h : i < 352 then (span_ok cert4_336 i (by omega) (by omega)) else (if h : i < 368 then (span_ok cert4_352 i (by omega) (by omega)) else (span_ok cert4_368 i (by omega) (by omega))))))) else (if h : i < 576 then (if h : i < 480 then (if h : i < 432 then (if h : i < 400 then (span_ok cert4_384 i (by omega) (by omega)) else (if h : i < 416 then (span_ok cert4_400 i (by omega) (by omega)) else (span_ok cert4_416 i (by omega) (by omega)))) else (if h : i < 448 then (span_ok cert4_432 i (by omega) (by omega)) else (if h : i < 464 then (span_ok cert4_448 i (by omega) (by omega)) else (span_ok cert4_464 i (by omega) (by omega))))) else (if h : i < 528 then (if h : i < 496 then (span_ok cert4_480 i (by omega) (by omega)) else (if h : i < 512 then (span_ok cert4_496 i (by omega) (by omega)) else (span_ok cert4_512 i (by omega) (by omega)))) else (if h : i < 544 then (span_ok cert4_528 i (by omega) (by omega)) else (if h : i < 560 then (span_ok cert4_544 i (by omega) (by omega)) else (span_ok cert4_560 i (by omega) (by omega)))))) else (if h : i < 672 then (if h : i < 624 then (if h : i < 592 then (span_ok cert4_576 i (by omega) (by omega)) else (if h : i < 608 then (span_ok cert4_592 i (by omega) (by omega)) else (span_ok cert4_608 i (by omega) (by omega)))) else (if h : i < 640 then (span_ok cert4_624 i (by omega) (by omega)) else (if h : i < 656 then (span_ok cert4_640 i (by omega) (by omega)) else (span_ok cert4_656 i (by omega) (by omega))))) else (if h : i < 720 then (if h : i < 688 then (span_ok cert4_672 i (by omega) (by omega)) else (if h : i < 704 then (span_ok cert4_688 i (by omega) (by omega)) else (span_ok cert4_704 i (by omega) (by omega)))) else (if h : i < 752 then (if h : i < 736 then (span_ok cert4_720 i (by omega) (by omega)) else (span_ok cert4_736 i (by omega) (by omega))) else (if h : i < 768 then (span_ok cert4_752 i (by omega) (by omega)) else (span_ok cert4_768 i (by omega) (by omega)))))))) else (if h : i < 1184 then (if h : i < 976 then (if h : i < 880 then (if h : i < 832 then (if h : i < 800 then (span_ok cert4_784 i (by omega) (by omega)) else (if h : i < 816 then (span_ok cert4_800 i (by omega) (by omega)) else (span_ok cert4_816 i (by omega) (by omega)))) else (if h : i < 848 then (span_ok cert4_832 i (by omega) (by omega)) else (if h : i < 864 then (span_ok cert4_848 i (by omega) (by omega)) else (span_ok cert4_864 i (by omega) (by omega))))) else (if h : i < 928 then (if h : i < 896 then (span_ok cert4_880 i (by omega) (by omega)) else (if h : i < 912 then (span_ok cert4_896 i (by omega) (by omega)) else (span_ok cert4_912 i (by omega) (by omega)))) else (if h : i < 944 then (span_ok cert4_928 i (by omega) (by omega)) else (if h : i < 960 then (span_ok cert4_944 i (by omega) (by omega)) else (span_ok cert4_960 i (by omega) (by omega)))))) else (if h : i < 1072 then (if h : i < 1024 then (if h : i < 992 then (span_ok cert4_976 i (by omega) (by omega)) else (if h : i < 1008 then (span_ok cert4_992 i (by omega) (by omega)) else (span_ok cert4_1008 i (by omega) (by omega)))) else (if h : i < 1040 then (span_ok cert4_1024 i (by omega) (by omega)) else (if h : i < 1056 then (span_ok cert4_1040 i (by omega) (by omega)) else (span_ok cert4_1056 i (by omega) (by omega))))) else (if h : i < 1120 then (if h : i < 1088 then (span_ok cert4_1072 i (by omega) (by omega)) else (if h : i < 1104 then (span_ok cert4_1088 i (by omega) (by omega)) else (span_ok cert4_1104 i (by omega) (by omega)))) else (if h : i < 1152 then (if h : i < 1136 then (span_ok cert4_1120 i (by omega) (by omega)) else (span_ok cert4_1136 i (by omega) (by omega))) else (if h : i < 1168 then (span_ok cert4_1152 i (by omega) (by omega)) else (span_ok cert4_1168 i (by omega) (by omega))))))) else (if h : i < 1376 then (if h : i < 1280 then (if h : i < 1232 then (if h : i < 1200 then (span_ok cert4_1184 i (by omega) (by omega)) else (if h : i < 1216 then (span_ok cert4_1200 i (by omega) (by omega)) else (span_ok cert4_1216 i (by omega) (by omega)))) else (if h : i < 1248 then (span_ok cert4_1232 i (by omega) (by omega)) else (if h : i < 1264 then (span_ok cert4_1248 i (by omega) (by omega)) else (span_ok cert4_1264 i (by omega) (by omega))))) else (if h : i < 1328 then (if h : i < 1296 then (span_ok cert4_1280 i (by omega) (by omega)) else (if h : i < 1312 then (span_ok cert4_1296 i (by omega) (by omega)) else (span_ok cert4_1312 i (by omega) (by omega)))) else (if h : i < 1344 then (span_ok cert4_1328 i (by omega) (by omega)) else (if h : i < 1360 then (span_ok cert4_1344 i (by omega) (by omega)) else (span_ok cert4_1360 i (by omega) (by omega)))))) else (if h : i < 1472 then (if h : i < 1424 then (if h : i < 1392 then (span_ok cert4_1376 i (by omega) (by omega)) else (if h : i < 1408 then (span_ok cert4_1392 i (by omega) (by omega)) else (span_ok cert4_1408 i (by omega) (by omega)))) else (if h : i < 1440 then (span_ok cert4_1424 i (by omega) (by omega)) else (if h : i < 1456 then (span_ok cert4_1440 i (by omega) (by omega)) else (span_ok cert4_1456 i (by omega) (by omega))))) else (if h : i < 1520 then (if h : i < 1488 then (span_ok cert4_1472 i (by omega) (by omega)) else (if h : i < 1504 then (span_ok cert4_1488 i (by omega) (by omega)) else (span_ok cert4_1504 i (by omega) (by omega)))) else (if h : i < 1552 then (if h : i < 1536 then (span_ok cert4_1520 i (by omega) (by omega)) else (span_ok cert4_1536 i (by omega) (by omega))) else (if h : i < 1568 then (span_ok cert4_1552 i (by omega) (by omega)) else (span_ok cert4_1568 i (by omega) (by omega)))))))))
def ok3 (i : Nat) := flag tableDict t4 6 (t3.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_0 : span ok3 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_16 : span ok3 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_32 : span ok3 32 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_48 : span ok3 48 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_64 : span ok3 64 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_80 : span ok3 80 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_96 : span ok3 96 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_112 : span ok3 112 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_128 : span ok3 128 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_144 : span ok3 144 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_160 : span ok3 160 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_176 : span ok3 176 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_192 : span ok3 192 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_208 : span ok3 208 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_224 : span ok3 224 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_240 : span ok3 240 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_256 : span ok3 256 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_272 : span ok3 272 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_288 : span ok3 288 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_304 : span ok3 304 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_320 : span ok3 320 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_336 : span ok3 336 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_352 : span ok3 352 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_368 : span ok3 368 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_384 : span ok3 384 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_400 : span ok3 400 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_416 : span ok3 416 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_432 : span ok3 432 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_448 : span ok3 448 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_464 : span ok3 464 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_480 : span ok3 480 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_496 : span ok3 496 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_512 : span ok3 512 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_528 : span ok3 528 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_544 : span ok3 544 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_560 : span ok3 560 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_576 : span ok3 576 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_592 : span ok3 592 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_608 : span ok3 608 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_624 : span ok3 624 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_640 : span ok3 640 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_656 : span ok3 656 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_672 : span ok3 672 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_688 : span ok3 688 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_704 : span ok3 704 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_720 : span ok3 720 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_736 : span ok3 736 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_752 : span ok3 752 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_768 : span ok3 768 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_784 : span ok3 784 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_800 : span ok3 800 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_816 : span ok3 816 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_832 : span ok3 832 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_848 : span ok3 848 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_864 : span ok3 864 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_880 : span ok3 880 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_896 : span ok3 896 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_912 : span ok3 912 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_928 : span ok3 928 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_944 : span ok3 944 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_960 : span ok3 960 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_976 : span ok3 976 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_992 : span ok3 992 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1008 : span ok3 1008 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1024 : span ok3 1024 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1040 : span ok3 1040 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1056 : span ok3 1056 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1072 : span ok3 1072 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1088 : span ok3 1088 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1104 : span ok3 1104 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1120 : span ok3 1120 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1136 : span ok3 1136 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1152 : span ok3 1152 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1168 : span ok3 1168 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1184 : span ok3 1184 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1200 : span ok3 1200 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1216 : span ok3 1216 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1232 : span ok3 1232 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1248 : span ok3 1248 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1264 : span ok3 1264 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1280 : span ok3 1280 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1296 : span ok3 1296 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1312 : span ok3 1312 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1328 : span ok3 1328 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1344 : span ok3 1344 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1360 : span ok3 1360 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1376 : span ok3 1376 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1392 : span ok3 1392 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1408 : span ok3 1408 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1424 : span ok3 1424 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1440 : span ok3 1440 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1456 : span ok3 1456 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1472 : span ok3 1472 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1488 : span ok3 1488 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1504 : span ok3 1504 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1520 : span ok3 1520 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1536 : span ok3 1536 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1552 : span ok3 1552 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1568 : span ok3 1568 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1584 : span ok3 1584 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1600 : span ok3 1600 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1616 : span ok3 1616 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1632 : span ok3 1632 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1648 : span ok3 1648 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1664 : span ok3 1664 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1680 : span ok3 1680 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1696 : span ok3 1696 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1712 : span ok3 1712 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1728 : span ok3 1728 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1744 : span ok3 1744 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1760 : span ok3 1760 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1776 : span ok3 1776 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1792 : span ok3 1792 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1808 : span ok3 1808 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1824 : span ok3 1824 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1840 : span ok3 1840 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1856 : span ok3 1856 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1872 : span ok3 1872 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1888 : span ok3 1888 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1904 : span ok3 1904 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1920 : span ok3 1920 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1936 : span ok3 1936 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1952 : span ok3 1952 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1968 : span ok3 1968 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_1984 : span ok3 1984 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2000 : span ok3 2000 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2016 : span ok3 2016 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2032 : span ok3 2032 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2048 : span ok3 2048 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2064 : span ok3 2064 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2080 : span ok3 2080 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2096 : span ok3 2096 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2112 : span ok3 2112 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2128 : span ok3 2128 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2144 : span ok3 2144 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2160 : span ok3 2160 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2176 : span ok3 2176 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2192 : span ok3 2192 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2208 : span ok3 2208 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2224 : span ok3 2224 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2240 : span ok3 2240 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2256 : span ok3 2256 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2272 : span ok3 2272 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2288 : span ok3 2288 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2304 : span ok3 2304 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2320 : span ok3 2320 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2336 : span ok3 2336 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2352 : span ok3 2352 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2368 : span ok3 2368 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2384 : span ok3 2384 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert3_2400 : span ok3 2400 11 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level3 : ∀ i < t3.count, noneLive 7 (t3.get tableDict i) := by
  apply allRows (hn:=level4)
  intro i hi
  change i < 2411 at hi
  change ok3 i = true
  exact (if h : i < 1200 then (if h : i < 592 then (if h : i < 288 then (if h : i < 144 then (if h : i < 64 then (if h : i < 32 then (if h : i < 16 then (span_ok cert3_0 i (by omega) (by omega)) else (span_ok cert3_16 i (by omega) (by omega))) else (if h : i < 48 then (span_ok cert3_32 i (by omega) (by omega)) else (span_ok cert3_48 i (by omega) (by omega)))) else (if h : i < 96 then (if h : i < 80 then (span_ok cert3_64 i (by omega) (by omega)) else (span_ok cert3_80 i (by omega) (by omega))) else (if h : i < 112 then (span_ok cert3_96 i (by omega) (by omega)) else (if h : i < 128 then (span_ok cert3_112 i (by omega) (by omega)) else (span_ok cert3_128 i (by omega) (by omega)))))) else (if h : i < 208 then (if h : i < 176 then (if h : i < 160 then (span_ok cert3_144 i (by omega) (by omega)) else (span_ok cert3_160 i (by omega) (by omega))) else (if h : i < 192 then (span_ok cert3_176 i (by omega) (by omega)) else (span_ok cert3_192 i (by omega) (by omega)))) else (if h : i < 240 then (if h : i < 224 then (span_ok cert3_208 i (by omega) (by omega)) else (span_ok cert3_224 i (by omega) (by omega))) else (if h : i < 256 then (span_ok cert3_240 i (by omega) (by omega)) else (if h : i < 272 then (span_ok cert3_256 i (by omega) (by omega)) else (span_ok cert3_272 i (by omega) (by omega))))))) else (if h : i < 432 then (if h : i < 352 then (if h : i < 320 then (if h : i < 304 then (span_ok cert3_288 i (by omega) (by omega)) else (span_ok cert3_304 i (by omega) (by omega))) else (if h : i < 336 then (span_ok cert3_320 i (by omega) (by omega)) else (span_ok cert3_336 i (by omega) (by omega)))) else (if h : i < 384 then (if h : i < 368 then (span_ok cert3_352 i (by omega) (by omega)) else (span_ok cert3_368 i (by omega) (by omega))) else (if h : i < 400 then (span_ok cert3_384 i (by omega) (by omega)) else (if h : i < 416 then (span_ok cert3_400 i (by omega) (by omega)) else (span_ok cert3_416 i (by omega) (by omega)))))) else (if h : i < 512 then (if h : i < 464 then (if h : i < 448 then (span_ok cert3_432 i (by omega) (by omega)) else (span_ok cert3_448 i (by omega) (by omega))) else (if h : i < 480 then (span_ok cert3_464 i (by omega) (by omega)) else (if h : i < 496 then (span_ok cert3_480 i (by omega) (by omega)) else (span_ok cert3_496 i (by omega) (by omega))))) else (if h : i < 544 then (if h : i < 528 then (span_ok cert3_512 i (by omega) (by omega)) else (span_ok cert3_528 i (by omega) (by omega))) else (if h : i < 560 then (span_ok cert3_544 i (by omega) (by omega)) else (if h : i < 576 then (span_ok cert3_560 i (by omega) (by omega)) else (span_ok cert3_576 i (by omega) (by omega)))))))) else (if h : i < 896 then (if h : i < 736 then (if h : i < 656 then (if h : i < 624 then (if h : i < 608 then (span_ok cert3_592 i (by omega) (by omega)) else (span_ok cert3_608 i (by omega) (by omega))) else (if h : i < 640 then (span_ok cert3_624 i (by omega) (by omega)) else (span_ok cert3_640 i (by omega) (by omega)))) else (if h : i < 688 then (if h : i < 672 then (span_ok cert3_656 i (by omega) (by omega)) else (span_ok cert3_672 i (by omega) (by omega))) else (if h : i < 704 then (span_ok cert3_688 i (by omega) (by omega)) else (if h : i < 720 then (span_ok cert3_704 i (by omega) (by omega)) else (span_ok cert3_720 i (by omega) (by omega)))))) else (if h : i < 816 then (if h : i < 768 then (if h : i < 752 then (span_ok cert3_736 i (by omega) (by omega)) else (span_ok cert3_752 i (by omega) (by omega))) else (if h : i < 784 then (span_ok cert3_768 i (by omega) (by omega)) else (if h : i < 800 then (span_ok cert3_784 i (by omega) (by omega)) else (span_ok cert3_800 i (by omega) (by omega))))) else (if h : i < 848 then (if h : i < 832 then (span_ok cert3_816 i (by omega) (by omega)) else (span_ok cert3_832 i (by omega) (by omega))) else (if h : i < 864 then (span_ok cert3_848 i (by omega) (by omega)) else (if h : i < 880 then (span_ok cert3_864 i (by omega) (by omega)) else (span_ok cert3_880 i (by omega) (by omega))))))) else (if h : i < 1040 then (if h : i < 960 then (if h : i < 928 then (if h : i < 912 then (span_ok cert3_896 i (by omega) (by omega)) else (span_ok cert3_912 i (by omega) (by omega))) else (if h : i < 944 then (span_ok cert3_928 i (by omega) (by omega)) else (span_ok cert3_944 i (by omega) (by omega)))) else (if h : i < 992 then (if h : i < 976 then (span_ok cert3_960 i (by omega) (by omega)) else (span_ok cert3_976 i (by omega) (by omega))) else (if h : i < 1008 then (span_ok cert3_992 i (by omega) (by omega)) else (if h : i < 1024 then (span_ok cert3_1008 i (by omega) (by omega)) else (span_ok cert3_1024 i (by omega) (by omega)))))) else (if h : i < 1120 then (if h : i < 1072 then (if h : i < 1056 then (span_ok cert3_1040 i (by omega) (by omega)) else (span_ok cert3_1056 i (by omega) (by omega))) else (if h : i < 1088 then (span_ok cert3_1072 i (by omega) (by omega)) else (if h : i < 1104 then (span_ok cert3_1088 i (by omega) (by omega)) else (span_ok cert3_1104 i (by omega) (by omega))))) else (if h : i < 1152 then (if h : i < 1136 then (span_ok cert3_1120 i (by omega) (by omega)) else (span_ok cert3_1136 i (by omega) (by omega))) else (if h : i < 1168 then (span_ok cert3_1152 i (by omega) (by omega)) else (if h : i < 1184 then (span_ok cert3_1168 i (by omega) (by omega)) else (span_ok cert3_1184 i (by omega) (by omega))))))))) else (if h : i < 1808 then (if h : i < 1504 then (if h : i < 1344 then (if h : i < 1264 then (if h : i < 1232 then (if h : i < 1216 then (span_ok cert3_1200 i (by omega) (by omega)) else (span_ok cert3_1216 i (by omega) (by omega))) else (if h : i < 1248 then (span_ok cert3_1232 i (by omega) (by omega)) else (span_ok cert3_1248 i (by omega) (by omega)))) else (if h : i < 1296 then (if h : i < 1280 then (span_ok cert3_1264 i (by omega) (by omega)) else (span_ok cert3_1280 i (by omega) (by omega))) else (if h : i < 1312 then (span_ok cert3_1296 i (by omega) (by omega)) else (if h : i < 1328 then (span_ok cert3_1312 i (by omega) (by omega)) else (span_ok cert3_1328 i (by omega) (by omega)))))) else (if h : i < 1424 then (if h : i < 1376 then (if h : i < 1360 then (span_ok cert3_1344 i (by omega) (by omega)) else (span_ok cert3_1360 i (by omega) (by omega))) else (if h : i < 1392 then (span_ok cert3_1376 i (by omega) (by omega)) else (if h : i < 1408 then (span_ok cert3_1392 i (by omega) (by omega)) else (span_ok cert3_1408 i (by omega) (by omega))))) else (if h : i < 1456 then (if h : i < 1440 then (span_ok cert3_1424 i (by omega) (by omega)) else (span_ok cert3_1440 i (by omega) (by omega))) else (if h : i < 1472 then (span_ok cert3_1456 i (by omega) (by omega)) else (if h : i < 1488 then (span_ok cert3_1472 i (by omega) (by omega)) else (span_ok cert3_1488 i (by omega) (by omega))))))) else (if h : i < 1648 then (if h : i < 1568 then (if h : i < 1536 then (if h : i < 1520 then (span_ok cert3_1504 i (by omega) (by omega)) else (span_ok cert3_1520 i (by omega) (by omega))) else (if h : i < 1552 then (span_ok cert3_1536 i (by omega) (by omega)) else (span_ok cert3_1552 i (by omega) (by omega)))) else (if h : i < 1600 then (if h : i < 1584 then (span_ok cert3_1568 i (by omega) (by omega)) else (span_ok cert3_1584 i (by omega) (by omega))) else (if h : i < 1616 then (span_ok cert3_1600 i (by omega) (by omega)) else (if h : i < 1632 then (span_ok cert3_1616 i (by omega) (by omega)) else (span_ok cert3_1632 i (by omega) (by omega)))))) else (if h : i < 1728 then (if h : i < 1680 then (if h : i < 1664 then (span_ok cert3_1648 i (by omega) (by omega)) else (span_ok cert3_1664 i (by omega) (by omega))) else (if h : i < 1696 then (span_ok cert3_1680 i (by omega) (by omega)) else (if h : i < 1712 then (span_ok cert3_1696 i (by omega) (by omega)) else (span_ok cert3_1712 i (by omega) (by omega))))) else (if h : i < 1760 then (if h : i < 1744 then (span_ok cert3_1728 i (by omega) (by omega)) else (span_ok cert3_1744 i (by omega) (by omega))) else (if h : i < 1776 then (span_ok cert3_1760 i (by omega) (by omega)) else (if h : i < 1792 then (span_ok cert3_1776 i (by omega) (by omega)) else (span_ok cert3_1792 i (by omega) (by omega)))))))) else (if h : i < 2112 then (if h : i < 1952 then (if h : i < 1872 then (if h : i < 1840 then (if h : i < 1824 then (span_ok cert3_1808 i (by omega) (by omega)) else (span_ok cert3_1824 i (by omega) (by omega))) else (if h : i < 1856 then (span_ok cert3_1840 i (by omega) (by omega)) else (span_ok cert3_1856 i (by omega) (by omega)))) else (if h : i < 1904 then (if h : i < 1888 then (span_ok cert3_1872 i (by omega) (by omega)) else (span_ok cert3_1888 i (by omega) (by omega))) else (if h : i < 1920 then (span_ok cert3_1904 i (by omega) (by omega)) else (if h : i < 1936 then (span_ok cert3_1920 i (by omega) (by omega)) else (span_ok cert3_1936 i (by omega) (by omega)))))) else (if h : i < 2032 then (if h : i < 1984 then (if h : i < 1968 then (span_ok cert3_1952 i (by omega) (by omega)) else (span_ok cert3_1968 i (by omega) (by omega))) else (if h : i < 2000 then (span_ok cert3_1984 i (by omega) (by omega)) else (if h : i < 2016 then (span_ok cert3_2000 i (by omega) (by omega)) else (span_ok cert3_2016 i (by omega) (by omega))))) else (if h : i < 2064 then (if h : i < 2048 then (span_ok cert3_2032 i (by omega) (by omega)) else (span_ok cert3_2048 i (by omega) (by omega))) else (if h : i < 2080 then (span_ok cert3_2064 i (by omega) (by omega)) else (if h : i < 2096 then (span_ok cert3_2080 i (by omega) (by omega)) else (span_ok cert3_2096 i (by omega) (by omega))))))) else (if h : i < 2256 then (if h : i < 2176 then (if h : i < 2144 then (if h : i < 2128 then (span_ok cert3_2112 i (by omega) (by omega)) else (span_ok cert3_2128 i (by omega) (by omega))) else (if h : i < 2160 then (span_ok cert3_2144 i (by omega) (by omega)) else (span_ok cert3_2160 i (by omega) (by omega)))) else (if h : i < 2208 then (if h : i < 2192 then (span_ok cert3_2176 i (by omega) (by omega)) else (span_ok cert3_2192 i (by omega) (by omega))) else (if h : i < 2224 then (span_ok cert3_2208 i (by omega) (by omega)) else (if h : i < 2240 then (span_ok cert3_2224 i (by omega) (by omega)) else (span_ok cert3_2240 i (by omega) (by omega)))))) else (if h : i < 2336 then (if h : i < 2288 then (if h : i < 2272 then (span_ok cert3_2256 i (by omega) (by omega)) else (span_ok cert3_2272 i (by omega) (by omega))) else (if h : i < 2304 then (span_ok cert3_2288 i (by omega) (by omega)) else (if h : i < 2320 then (span_ok cert3_2304 i (by omega) (by omega)) else (span_ok cert3_2320 i (by omega) (by omega))))) else (if h : i < 2368 then (if h : i < 2352 then (span_ok cert3_2336 i (by omega) (by omega)) else (span_ok cert3_2352 i (by omega) (by omega))) else (if h : i < 2384 then (span_ok cert3_2368 i (by omega) (by omega)) else (if h : i < 2400 then (span_ok cert3_2384 i (by omega) (by omega)) else (span_ok cert3_2400 i (by omega) (by omega))))))))))
def ok2 (i : Nat) := flag tableDict t3 7 (t2.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_0 : span ok2 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_16 : span ok2 16 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_32 : span ok2 32 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_48 : span ok2 48 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_64 : span ok2 64 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_80 : span ok2 80 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_96 : span ok2 96 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_112 : span ok2 112 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_128 : span ok2 128 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_144 : span ok2 144 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_160 : span ok2 160 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_176 : span ok2 176 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_192 : span ok2 192 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_208 : span ok2 208 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_224 : span ok2 224 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_240 : span ok2 240 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_256 : span ok2 256 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_272 : span ok2 272 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_288 : span ok2 288 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_304 : span ok2 304 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_320 : span ok2 320 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_336 : span ok2 336 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_352 : span ok2 352 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_368 : span ok2 368 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_384 : span ok2 384 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_400 : span ok2 400 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_416 : span ok2 416 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_432 : span ok2 432 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_448 : span ok2 448 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_464 : span ok2 464 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_480 : span ok2 480 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_496 : span ok2 496 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_512 : span ok2 512 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_528 : span ok2 528 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_544 : span ok2 544 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_560 : span ok2 560 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_576 : span ok2 576 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_592 : span ok2 592 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_608 : span ok2 608 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_624 : span ok2 624 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_640 : span ok2 640 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_656 : span ok2 656 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_672 : span ok2 672 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_688 : span ok2 688 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_704 : span ok2 704 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_720 : span ok2 720 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_736 : span ok2 736 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_752 : span ok2 752 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_768 : span ok2 768 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_784 : span ok2 784 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_800 : span ok2 800 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_816 : span ok2 816 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert2_832 : span ok2 832 7 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level2 : ∀ i < t2.count, noneLive 8 (t2.get tableDict i) := by
  apply allRows (hn:=level3)
  intro i hi
  change i < 839 at hi
  change ok2 i = true
  exact (if h : i < 416 then (if h : i < 208 then (if h : i < 96 then (if h : i < 48 then (if h : i < 16 then (span_ok cert2_0 i (by omega) (by omega)) else (if h : i < 32 then (span_ok cert2_16 i (by omega) (by omega)) else (span_ok cert2_32 i (by omega) (by omega)))) else (if h : i < 64 then (span_ok cert2_48 i (by omega) (by omega)) else (if h : i < 80 then (span_ok cert2_64 i (by omega) (by omega)) else (span_ok cert2_80 i (by omega) (by omega))))) else (if h : i < 144 then (if h : i < 112 then (span_ok cert2_96 i (by omega) (by omega)) else (if h : i < 128 then (span_ok cert2_112 i (by omega) (by omega)) else (span_ok cert2_128 i (by omega) (by omega)))) else (if h : i < 176 then (if h : i < 160 then (span_ok cert2_144 i (by omega) (by omega)) else (span_ok cert2_160 i (by omega) (by omega))) else (if h : i < 192 then (span_ok cert2_176 i (by omega) (by omega)) else (span_ok cert2_192 i (by omega) (by omega)))))) else (if h : i < 304 then (if h : i < 256 then (if h : i < 224 then (span_ok cert2_208 i (by omega) (by omega)) else (if h : i < 240 then (span_ok cert2_224 i (by omega) (by omega)) else (span_ok cert2_240 i (by omega) (by omega)))) else (if h : i < 272 then (span_ok cert2_256 i (by omega) (by omega)) else (if h : i < 288 then (span_ok cert2_272 i (by omega) (by omega)) else (span_ok cert2_288 i (by omega) (by omega))))) else (if h : i < 352 then (if h : i < 320 then (span_ok cert2_304 i (by omega) (by omega)) else (if h : i < 336 then (span_ok cert2_320 i (by omega) (by omega)) else (span_ok cert2_336 i (by omega) (by omega)))) else (if h : i < 384 then (if h : i < 368 then (span_ok cert2_352 i (by omega) (by omega)) else (span_ok cert2_368 i (by omega) (by omega))) else (if h : i < 400 then (span_ok cert2_384 i (by omega) (by omega)) else (span_ok cert2_400 i (by omega) (by omega))))))) else (if h : i < 624 then (if h : i < 512 then (if h : i < 464 then (if h : i < 432 then (span_ok cert2_416 i (by omega) (by omega)) else (if h : i < 448 then (span_ok cert2_432 i (by omega) (by omega)) else (span_ok cert2_448 i (by omega) (by omega)))) else (if h : i < 480 then (span_ok cert2_464 i (by omega) (by omega)) else (if h : i < 496 then (span_ok cert2_480 i (by omega) (by omega)) else (span_ok cert2_496 i (by omega) (by omega))))) else (if h : i < 560 then (if h : i < 528 then (span_ok cert2_512 i (by omega) (by omega)) else (if h : i < 544 then (span_ok cert2_528 i (by omega) (by omega)) else (span_ok cert2_544 i (by omega) (by omega)))) else (if h : i < 592 then (if h : i < 576 then (span_ok cert2_560 i (by omega) (by omega)) else (span_ok cert2_576 i (by omega) (by omega))) else (if h : i < 608 then (span_ok cert2_592 i (by omega) (by omega)) else (span_ok cert2_608 i (by omega) (by omega)))))) else (if h : i < 736 then (if h : i < 672 then (if h : i < 640 then (span_ok cert2_624 i (by omega) (by omega)) else (if h : i < 656 then (span_ok cert2_640 i (by omega) (by omega)) else (span_ok cert2_656 i (by omega) (by omega)))) else (if h : i < 704 then (if h : i < 688 then (span_ok cert2_672 i (by omega) (by omega)) else (span_ok cert2_688 i (by omega) (by omega))) else (if h : i < 720 then (span_ok cert2_704 i (by omega) (by omega)) else (span_ok cert2_720 i (by omega) (by omega))))) else (if h : i < 784 then (if h : i < 752 then (span_ok cert2_736 i (by omega) (by omega)) else (if h : i < 768 then (span_ok cert2_752 i (by omega) (by omega)) else (span_ok cert2_768 i (by omega) (by omega)))) else (if h : i < 816 then (if h : i < 800 then (span_ok cert2_784 i (by omega) (by omega)) else (span_ok cert2_800 i (by omega) (by omega))) else (if h : i < 832 then (span_ok cert2_816 i (by omega) (by omega)) else (span_ok cert2_832 i (by omega) (by omega))))))))
def ok1 (i : Nat) := flag tableDict t2 8 (t1.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert1_0 : span ok1 0 16 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert1_16 : span ok1 16 14 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level1 : ∀ i < t1.count, noneLive 9 (t1.get tableDict i) := by
  apply allRows (hn:=level2)
  intro i hi
  change i < 30 at hi
  change ok1 i = true
  exact (if h : i < 16 then (span_ok cert1_0 i (by omega) (by omega)) else (span_ok cert1_16 i (by omega) (by omega)))
def ok0 (i : Nat) := flag tableDict t1 9 (t0.get tableDict i)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma cert0_0 : span ok0 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private lemma level0 : ∀ i < t0.count, noneLive 10 (t0.get tableDict i) := by
  apply allRows (hn:=level1)
  intro i hi
  change i < 1 at hi
  change ok0 i = true
  exact (span_ok cert0_0 i (by omega) (by omega))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem reject (zs : List Sig) (h : Steps raw zs) (hl : zs.length ≤ 10) (ho : target ∈ raw ++ zs) : False := by
  obtain ⟨k,S,hk,live,sub⟩ := extract_steps h ho
  have req := necessary raw (by decide +kernel) live sub
  have eq : (t0.get tableDict 0).toFinset = raw.toFinset := by decide +kernel
  exact level0 0 (by decide) (by decide +kernel) k (by omega) ((eq.trans req).symm ▸ live)
end PEqualNP.Outside.L_meta_29856.Check

namespace PEqualNP.Outside.L_meta_29856.C7Projection

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

end PEqualNP.Outside.L_meta_29856.C7Projection

namespace PEqualNP.Outside.L_meta_29856.Bridge
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
end PEqualNP.Outside.L_meta_29856.Bridge

namespace PEqualNP.Outside.L_meta_29856.Bridge

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

end PEqualNP.Outside.L_meta_29856.Bridge

namespace PEqualNP.Outside.L_meta_29856
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
end PEqualNP.Outside.L_meta_29856

theorem PEqualNP.Outside.L_meta_29856 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 5 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 9 ∈ (C.gates.get i).inputs ∧ 9 ≠ 0 ∧ 9 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 9 false = true)) := by
  rintro ⟨C,i,k,_,fan,sz,comp,h0,hu,hor,hand,hik,hk,hw,hn,hl,ht⟩
  exact PEqualNP.Outside.L_meta_29856.no_c7_10_or_under_and C i k 9 fan sz comp h0 hu hor hand hik hk hw hn hl ht
