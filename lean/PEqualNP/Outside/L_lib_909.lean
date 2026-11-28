import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_909

open Finset

def stepF (state : Option (List ℕ)) (cap : ℕ) : Option (List ℕ) :=
  state.bind (fun loads =>
    ((loads.filter (fun v => decide (v ≤ cap))).max?).map
      (fun v => (v+1) :: loads.erase v))

theorem foldl_none (l : List ℕ) : l.foldl stepF none = none := by
  induction l with
  | nil => rfl
  | cons x l ih => simpa [List.foldl_cons, stepF] using ih

/-- The list of loads and the labelled loads agree as multisets. -/
def Rel {p : ℕ} (L : List ℕ) (G : Fin p → ℕ) : Prop :=
  ∀ f : ℕ → ℤ, (L.map f).sum = ∑ k, f (G k)

def D {p : ℕ} (X : Fin p → ℕ) (t : ℕ) : ℤ := ∑ k, ((t - X k : ℕ) : ℤ)

theorem rel_mem {p : ℕ} {L : List ℕ} {G : Fin p → ℕ} (h : Rel L G) (v : ℕ) (hv : v ∈ L) :
    ∃ k, G k = v := by
  by_contra hne
  push_neg at hne
  have h1 := h (fun x => if x = v then 1 else 0)
  have h2 : ∑ k, (fun x : ℕ => if x = v then (1 : ℤ) else 0) (G k) = 0 := by
    apply Finset.sum_eq_zero; intro k _; simp [hne k]
  have h3 : 0 < ((L.map (fun x : ℕ => if x = v then (1 : ℤ) else 0))).sum := by
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hv
    have hnn : ∀ l : List ℕ, 0 ≤ (l.map (fun x : ℕ => if x = v then (1 : ℤ) else 0)).sum := by
      intro l
      apply List.sum_nonneg
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx
      split_ifs <;> norm_num
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons, ite_true]
    linarith [hnn l1, hnn l2]
  rw [h1, h2] at h3
  exact lt_irrefl _ h3

theorem rel_mem' {p : ℕ} {L : List ℕ} {G : Fin p → ℕ} (h : Rel L G) (k : Fin p) : G k ∈ L := by
  by_contra hne
  have h1 := h (fun x => if x = G k then 1 else 0)
  have h2 : (L.map (fun x : ℕ => if x = G k then (1 : ℤ) else 0)).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have : y ≠ G k := fun e => hne (e ▸ hy)
    simp [this]
  have h3 : 0 < ∑ j, (fun x : ℕ => if x = G k then (1 : ℤ) else 0) (G j) := by
    have := Finset.single_le_sum (f := fun j => (fun x : ℕ => if x = G k then (1 : ℤ) else 0) (G j))
      (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ k)
    simp only [ite_true] at this
    linarith
  rw [← h1, h2] at h3
  exact lt_irrefl _ h3

theorem sum_update {p : ℕ} (X : Fin p → ℕ) (k : Fin p) (y : ℕ) (f : ℕ → ℤ) :
    ∑ j, f (Function.update X k y j) = ∑ j, f (X j) + (f y - f (X k)) := by
  have : ∀ j, f (Function.update X k y j) = f (X j) + (if j = k then f y - f (X k) else 0) := by
    intro j
    by_cases hj : j = k
    · subst hj; simp
    · simp [hj]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem rel_step {p : ℕ} {L : List ℕ} {G : Fin p → ℕ} (h : Rel L G) (k : Fin p) :
    Rel ((G k + 1) :: L.erase (G k)) (Function.update G k (G k + 1)) := by
  intro f
  have hp := (List.perm_cons_erase (rel_mem' h k)).map f
  have e1 := hp.sum_eq
  simp only [List.map_cons, List.sum_cons] at e1 ⊢
  rw [sum_update, ← h f, e1]
  ring

theorem step_some {p : ℕ} {L : List ℕ} {G : Fin p → ℕ} (h : Rel L G) (cap : ℕ)
    (hex : ∃ k, G k ≤ cap) :
    ∃ kg, G kg ≤ cap ∧ (∀ k, G k ≤ cap → G k ≤ G kg) ∧
      stepF (some L) cap = some ((G kg + 1) :: L.erase (G kg)) := by
  obtain ⟨k0, hk0⟩ := hex
  have hne : L.filter (fun v => decide (v ≤ cap)) ≠ [] := by
    intro he
    have : G k0 ∈ L.filter (fun v => decide (v ≤ cap)) := by
      simp [List.mem_filter, rel_mem' h k0, hk0]
    rw [he] at this; simp at this
  obtain ⟨v, hv⟩ : ∃ v, (L.filter (fun v => decide (v ≤ cap))).max? = some v := by
    cases hm : (L.filter (fun v => decide (v ≤ cap))).max? with
    | none => exact absurd (List.max?_eq_none_iff.1 hm) hne
    | some v => exact ⟨v, rfl⟩
  have hv' := List.max?_eq_some_iff.1 hv
  obtain ⟨hvm, hvmax⟩ := hv'
  rw [List.mem_filter] at hvm
  obtain ⟨hvL, hvc⟩ := hvm
  obtain ⟨kg, rfl⟩ := rel_mem h v hvL
  refine ⟨kg, by simpa using hvc, ?_, ?_⟩
  · intro k hk
    apply hvmax
    simp [List.mem_filter, rel_mem' h k, hk]
  · simp [stepF, hv]

theorem D_update {p : ℕ} (X : Fin p → ℕ) (k : Fin p) (t : ℕ) :
    D (Function.update X k (X k + 1)) t = D X t - (if X k < t then 1 else 0) := by
  unfold D
  rw [sum_update X k (X k + 1) (fun x => ((t - x : ℕ) : ℤ))]
  split_ifs with h
  · have : t - (X k + 1) + 1 = t - X k := by omega
    have e : ((t - X k : ℕ) : ℤ) = ((t - (X k + 1) : ℕ) : ℤ) + 1 := by rw [← this]; push_cast; ring
    rw [e]; ring
  · have e1 : t - (X k + 1) = 0 := by omega
    have e2 : t - X k = 0 := by omega
    rw [e1, e2]; simp

def g (b t x : ℕ) : ℤ :=
  ((b + 1 - x : ℕ) : ℤ) - ((b - t + 2 : ℕ) : ℤ) * ((t - x : ℕ) : ℤ) +
    ((b - t + 1 : ℕ) : ℤ) * ((t - 1 - x : ℕ) : ℤ)

theorem g_low (b t x : ℕ) (htb : t ≤ b) (hx : x < t) : g b t x = 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, t = x + 1 + d := ⟨t - x - 1, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, b = x + 1 + d + e := ⟨b - (x + 1 + d), by omega⟩
  unfold g
  have h1 : x + 1 + d + e + 1 - x = d + e + 2 := by omega
  have h2 : x + 1 + d + e - (x + 1 + d) + 2 = e + 2 := by omega
  have h3 : x + 1 + d - x = d + 1 := by omega
  have h4 : x + 1 + d + e - (x + 1 + d) + 1 = e + 1 := by omega
  have h5 : x + 1 + d - 1 - x = d := by omega
  rw [h1, h2, h3, h4, h5]; push_cast; ring

theorem g_mid (b t x : ℕ) (hx : t ≤ x) (hxb : x ≤ b) : 1 ≤ g b t x := by
  unfold g
  have h3 : t - x = 0 := by omega
  have h5 : t - 1 - x = 0 := by omega
  rw [h3, h5]
  have : (1 : ℤ) ≤ ((b + 1 - x : ℕ) : ℤ) := by
    have : 1 ≤ b + 1 - x := by omega
    exact_mod_cast this
  simpa using this

theorem g_high (b t x : ℕ) (htb : t ≤ b) (hx : b < x) : g b t x = 0 := by
  unfold g
  have h1 : b + 1 - x = 0 := by omega
  have h3 : t - x = 0 := by omega
  have h5 : t - 1 - x = 0 := by omega
  rw [h1, h3, h5]; simp

theorem g_nonneg (b t x : ℕ) (htb : t ≤ b) : 0 ≤ g b t x := by
  rcases lt_or_ge x t with h | h
  · rw [g_low b t x htb h]
  rcases le_or_gt x b with h' | h'
  · linarith [g_mid b t x h h']
  · rw [g_high b t x htb h']

theorem g_sum {p : ℕ} (X : Fin p → ℕ) (b t : ℕ) :
    ∑ k, g b t (X k) = D X (b + 1) - ((b - t + 2 : ℕ) : ℤ) * D X t +
      ((b - t + 1 : ℕ) : ℤ) * D X (t - 1) := by
  unfold g D
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]

theorem exists_move {p : ℕ} (G R : Fin p → ℕ) (b : ℕ) (kr : Fin p) (hr : R kr ≤ b)
    (hdom : ∀ t, D R t ≤ D G t) : ∃ k, G k ≤ b := by
  by_contra hne
  push_neg at hne
  have h0 : D G (b + 1) = 0 := by
    unfold D; apply Finset.sum_eq_zero; intro k _
    have : b + 1 - G k = 0 := by have := hne k; omega
    simp [this]
  have h1 : (1 : ℤ) ≤ D R (b + 1) := by
    unfold D
    have := Finset.single_le_sum (f := fun k => ((b + 1 - R k : ℕ) : ℤ))
      (fun k _ => by positivity) (Finset.mem_univ kr)
    have h2 : (1 : ℤ) ≤ ((b + 1 - R kr : ℕ) : ℤ) := by
      have : 1 ≤ b + 1 - R kr := by omega
      exact_mod_cast this
    linarith
  linarith [hdom (b + 1)]

theorem core {p : ℕ} (G R : Fin p → ℕ) (b : ℕ) (kg kr : Fin p) (hr : R kr ≤ b) (hg : G kg ≤ b)
    (hmax : ∀ k, G k ≤ b → G k ≤ G kg) (hdom : ∀ t, D R t ≤ D G t) :
    ∀ t, D (Function.update R kr (R kr + 1)) t ≤ D (Function.update G kg (G kg + 1)) t := by
  intro t
  rw [D_update, D_update]
  by_cases hv : G kg < t
  swap
  · rw [if_neg hv]; split_ifs <;> linarith [hdom t]
  rw [if_pos hv]
  by_cases hu : R kr < t
  · rw [if_pos hu]; linarith [hdom t]
  rw [if_neg hu]
  push_neg at hu
  have htb : t ≤ b := le_trans hu hr
  suffices hlt : D R t < D G t by linarith
  by_contra hle
  push_neg at hle
  have heq : D R t = D G t := le_antisymm (hdom t) hle
  have hG : ∑ k, g b t (G k) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    rcases le_or_gt (G k) b with h | h
    · exact g_low b t (G k) htb (lt_of_le_of_lt (hmax k h) hv)
    · exact g_high b t (G k) htb h
  have hR : 1 ≤ ∑ k, g b t (R k) := by
    have := Finset.single_le_sum (f := fun k => g b t (R k))
      (fun k _ => g_nonneg b t (R k) htb) (Finset.mem_univ kr)
    linarith [g_mid b t (R kr) hu hr]
  rw [g_sum] at hG hR
  have hc : (0 : ℤ) ≤ ((b - t + 1 : ℕ) : ℤ) := by positivity
  have := mul_le_mul_of_nonneg_left (hdom (t - 1)) hc
  rw [heq] at hR
  linarith [hdom (b + 1)]

theorem card_succ_lt {n p : ℕ} (c : Fin (n + 1) → Fin p) (i : Fin n) :
    (Finset.univ.filter (fun j : Fin (n + 1) => j < i.succ ∧ c j = c i.succ)).card =
      (if c 0 = c i.succ then 1 else 0) +
        (Finset.univ.filter (fun j : Fin n => j < i ∧ c j.succ = c i.succ)).card := by
  rw [Fin.card_filter_univ_succ']
  simp [Fin.succ_pos, Fin.succ_lt_succ_iff]

theorem card_zero_lt {n p : ℕ} (c : Fin (n + 1) → Fin p) :
    (Finset.univ.filter (fun j : Fin (n + 1) => j < 0 ∧ c j = c 0)).card = 0 := by
  simp

theorem card_all {n p : ℕ} (c : Fin (n + 1) → Fin p) (k : Fin p) :
    (Finset.univ.filter (fun j : Fin (n + 1) => c j = k)).card =
      (if c 0 = k then 1 else 0) + (Finset.univ.filter (fun j : Fin n => c j.succ = k)).card := by
  rw [Fin.card_filter_univ_succ']

theorem upd_val {p : ℕ} (R : Fin p → ℕ) (k a : Fin p) :
    Function.update R k (R k + 1) a = R a + (if k = a then 1 else 0) := by
  by_cases h : k = a
  · subst h; simp
  · simp [Function.update_of_ne (Ne.symm h), h]

theorem partA {p : ℕ} : ∀ (n : ℕ) (bs : Fin n → ℕ) (c : Fin n → Fin p) (L : List ℕ)
    (G R : Fin p → ℕ), Rel L G → (∀ t, D R t ≤ D G t) →
    (∀ i, R (c i) + (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ bs i) →
    ∃ (L' : List ℕ) (G' : Fin p → ℕ), (List.ofFn bs).foldl stepF (some L) = some L' ∧ Rel L' G' ∧
      ∀ t, D (fun k => R k + (Finset.univ.filter (fun i : Fin n => c i = k)).card) t ≤ D G' t := by
  intro n
  induction n with
  | zero =>
    intro bs c L G R hrel hdom _
    refine ⟨L, G, rfl, hrel, ?_⟩
    simpa using hdom
  | succ n ih =>
    intro bs c L G R hrel hdom hfit
    have hr : R (c 0) ≤ bs 0 := by
      have := hfit 0; rw [card_zero_lt] at this; omega
    obtain ⟨kg, hg, hmax, hst⟩ := step_some hrel (bs 0) (exists_move G R (bs 0) (c 0) hr hdom)
    have hdom' := core G R (bs 0) kg (c 0) hr hg hmax hdom
    have hrel' := rel_step hrel kg
    obtain ⟨L', G', hf, hrel'', hdom''⟩ := ih (fun i => bs i.succ) (fun i => c i.succ) _ _
      (Function.update R (c 0) (R (c 0) + 1)) hrel' hdom' (by
        intro i
        have := hfit i.succ
        rw [card_succ_lt] at this
        show Function.update R (c 0) (R (c 0) + 1) (c i.succ) + _ ≤ bs i.succ
        rw [upd_val]
        split_ifs at this ⊢ <;> omega)
    refine ⟨L', G', ?_, hrel'', ?_⟩
    · rw [List.ofFn_succ, List.foldl_cons, hst]; exact hf
    · intro t
      have e : (fun k => R k + (Finset.univ.filter (fun i : Fin (n + 1) => c i = k)).card) =
          (fun k => Function.update R (c 0) (R (c 0) + 1) k +
            (Finset.univ.filter (fun i : Fin n => c i.succ = k)).card) := by
        funext k; rw [card_all, upd_val]; ring
      rw [e]; exact hdom'' t

theorem partB {p : ℕ} : ∀ (n : ℕ) (bs : Fin n → ℕ) (L : List ℕ) (G : Fin p → ℕ), Rel L G →
    ((List.ofFn bs).foldl stepF (some L)).isSome = true →
    ∃ c : Fin n → Fin p, ∀ i,
      G (c i) + (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ bs i := by
  intro n
  induction n with
  | zero => intro bs L G _ _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro bs L G hrel hs
    rw [List.ofFn_succ, List.foldl_cons] at hs
    have hex : ∃ k, G k ≤ bs 0 := by
      by_contra hne
      push_neg at hne
      have hnone : stepF (some L) (bs 0) = none := by
        simp only [stepF, Option.bind_some, Option.map_eq_none_iff, List.max?_eq_none_iff]
        apply List.filter_eq_nil_iff.2
        intro x hx
        obtain ⟨k, rfl⟩ := rel_mem hrel x hx
        simpa using hne k
      rw [hnone, foldl_none] at hs
      simp at hs
    obtain ⟨kg, hg, -, hst⟩ := step_some hrel (bs 0) hex
    rw [hst] at hs
    obtain ⟨c', hc'⟩ := ih (fun i => bs i.succ) _ _ (rel_step hrel kg) hs
    refine ⟨Fin.cons kg c', ?_⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [card_zero_lt]; simpa using hg
    · rw [card_succ_lt]
      have := hc' i
      rw [upd_val] at this
      simp only [Fin.cons_zero, Fin.cons_succ] at this ⊢
      split_ifs at this ⊢ <;> omega

theorem rel_init (p : ℕ) : Rel (List.replicate p 0) (fun _ : Fin p => 0) := by
  intro f
  simp [List.map_replicate, List.sum_replicate]

end PEqualNP.Outside.L_lib_909

open PEqualNP.Outside.L_lib_909 in
theorem PEqualNP.Outside.L_lib_909 : ∀ (n p : ℕ) (b : Fin n → ℕ),
  let step := fun (state : Option (List ℕ)) (cap : ℕ) =>
    state.bind (fun loads =>
      ((loads.filter (fun v => decide (v ≤ cap))).max?).map
        (fun v => (v+1) :: loads.erase v))
  let result := ((List.finRange n).map b).foldl step (some (List.replicate p 0))
  let fits := fun c : Fin n → Fin p => ∀ i : Fin n,
    (Finset.univ.filter (fun j : Fin n => j < i ∧ c j = c i)).card ≤ b i
  (result.isSome = true ↔ ∃ c : Fin n → Fin p, fits c) ∧
  ∀ loads : List ℕ, result = some loads → ∀ c : Fin n → Fin p, fits c → ∀ t : ℕ,
    ((List.finRange p).map (fun label => t - (Finset.univ.filter (fun i : Fin n => c i = label)).card)).sum ≤
      (loads.map (fun v => t-v)).sum := by
  intro n p b step result fits
  have hres : result = (List.ofFn b).foldl stepF (some (List.replicate p 0)) := by
    rw [List.ofFn_eq_map]; rfl
  have hdom0 : ∀ t, D (fun _ : Fin p => 0) t ≤ D (fun _ : Fin p => 0) t := fun t => le_rfl
  refine ⟨⟨fun h => ?_, fun ⟨c, hc⟩ => ?_⟩, ?_⟩
  · rw [hres] at h
    obtain ⟨c, hc⟩ := partB n b _ _ (rel_init p) h
    exact ⟨c, fun i => by simpa using hc i⟩
  · obtain ⟨L', G', hf, -, -⟩ := partA n b c _ _ (fun _ => 0) (rel_init p) hdom0
      (fun i => by simpa using hc i)
    rw [hres, hf]; rfl
  · intro loads hl c hc t
    obtain ⟨L', G', hf, hrel, hdom⟩ := partA n b c _ _ (fun _ => 0) (rel_init p) hdom0
      (fun i => by simpa using hc i)
    rw [hres, hf] at hl
    cases hl
    have h1 := hdom t
    have h2 := hrel (fun v => ((t - v : ℕ) : ℤ))
    unfold D at h1
    rw [← h2] at h1
    simp only [zero_add] at h1
    rw [← Fin.sum_univ_def]
    have h3 : ((loads.map (fun v => t - v)).sum : ℤ) = (loads.map (fun v => ((t - v : ℕ) : ℤ))).sum := by
      push_cast [Nat.cast_list_sum, List.map_map]; rfl
    exact_mod_cast (show ((∑ k : Fin p, (t - (Finset.univ.filter (fun i : Fin n => c i = k)).card) : ℕ) : ℤ)
      ≤ ((loads.map (fun v => t - v)).sum : ℤ) by rw [h3]; push_cast; exact h1)
