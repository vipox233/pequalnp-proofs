import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_884

open Finset

variable {q k : ℕ} (name : Option (Fin q) × Bool ↪ Fin k)

def hb (b : Bool) : Fin k := name (none, b)

def lf (c : Fin q) (b : Bool) : Fin k := name (some c, b)

def st (b : Bool) : Finset (Fin k) :=
  insert (hb name b) ((univ : Finset (Fin q)).image (fun c => lf name c b))

@[simp] lemma hb_inj {b b' : Bool} : hb name b = hb name b' ↔ b = b' := by simp [hb]

@[simp] lemma lf_inj {c c' : Fin q} {b b' : Bool} : lf name c b = lf name c' b' ↔ c = c' ∧ b = b' := by
  simp [lf]

@[simp] lemma hb_ne_lf {b b' : Bool} {c : Fin q} : hb name b ≠ lf name c b' := by simp [hb, lf]

@[simp] lemma lf_ne_hb {b b' : Bool} {c : Fin q} : lf name c b' ≠ hb name b := by simp [hb, lf]

lemma mem_st {b : Bool} {x : Fin k} : x ∈ st name b ↔ x = hb name b ∨ ∃ c, lf name c b = x := by
  simp [st]

lemma hit3 (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P) (x y z : Fin k)
    (h : ∃ u ∈ ({x, y, z} : Finset (Fin k)), P u ∈ ({x, y, z} : Finset (Fin k)) ∧ P u ≠ u) :
    P x = y ∨ P x = z ∨ P y = z := by
  have hPP : ∀ x, P (P x) = x := hP
  obtain ⟨u, hu, hPu, hne⟩ := h
  simp only [mem_insert, mem_singleton] at hu hPu
  rcases hu with rfl | rfl | rfl <;> rcases hPu with h | h | h
  all_goals first
    | exact absurd h hne
    | (left; exact h)
    | (right; left; exact h)
    | (right; right; exact h)
    | (left; rw [← h, hPP]; done)
    | (right; left; rw [← h, hPP]; done)
    | (right; right; rw [← h, hPP]; done)

lemma part1 (P : Equiv.Perm (Fin k)) (hP : Function.Involutive P) :
    ((∀ (c : Fin q) (b : Bool),
        ∃ u ∈ ({hb name b, lf name c false, lf name c true} : Finset (Fin k)),
          P u ∈ ({hb name b, lf name c false, lf name c true} : Finset (Fin k)) ∧ P u ≠ u) ∧
      ∃ u ∈ st name false, P u ∈ st name false ∧ P u ≠ u) ↔
    ∃! c : Fin q, (∀ b, P (hb name b) = lf name c b) ∧
      ∀ j, j ≠ c → P (lf name j false) = lf name j true := by
  have hPP : ∀ x, P (P x) = x := hP
  constructor
  · rintro ⟨T, hs⟩
    have hA : ∀ c, P (lf name c false) ≠ lf name c true →
        ∀ b, P (hb name b) = lf name c false ∨ P (hb name b) = lf name c true := by
      intro c hc b
      rcases hit3 P hP _ _ _ (T c b) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hc
    obtain ⟨c, hc⟩ : ∃ c, P (lf name c false) ≠ lf name c true := by
      by_contra hall
      push Not at hall
      obtain ⟨u, hu, hPu, hne⟩ := hs
      rw [mem_st] at hu hPu
      rcases hu with rfl | ⟨j, rfl⟩
      · rcases hPu with h | ⟨j, hj⟩
        · exact hne h
        · have h2 := hall j
          rw [hj, hPP] at h2
          simp at h2
      · rw [hall j] at hPu
        simp at hPu
    have huniq : ∀ d, d ≠ c → P (lf name d false) = lf name d true := by
      intro d hd
      by_contra hcd
      rcases hA c hc false with h1 | h1 <;> rcases hA d hcd false with h2 | h2 <;>
        (rw [h1] at h2; simp at h2 <;> exact hd h2.symm)
    have hPf : P (hb name false) = lf name c false := by
      rcases hA c hc false with h1 | h1
      · exact h1
      · exfalso
        have h3 : P (hb name true) = lf name c false := by
          rcases hA c hc true with h3 | h3
          · exact h3
          · rw [← h1] at h3
            have := P.injective h3
            simp at this
        obtain ⟨u, hu, hPu, hne⟩ := hs
        rw [mem_st] at hu hPu
        rcases hu with rfl | ⟨j, rfl⟩
        · rw [h1] at hPu
          simp at hPu
        · by_cases hj : j = c
          · subst hj
            rw [← h3, hPP] at hPu
            simp at hPu
          · rw [huniq j hj] at hPu
            simp at hPu
    have hPt : P (hb name true) = lf name c true := by
      rcases hA c hc true with h3 | h3
      · rw [← hPf] at h3
        have := P.injective h3
        simp at this
      · exact h3
    refine ⟨c, ⟨fun b => by cases b <;> assumption, huniq⟩, fun c' hc' => ?_⟩
    have := hc'.1 false
    rw [hPf] at this
    have h' : c = c' := by simpa using this
    exact h'.symm
  · rintro ⟨c, ⟨h1, h2⟩, -⟩
    refine ⟨fun c' b => ?_, ⟨hb name false, by simp [st], ?_, ?_⟩⟩
    · by_cases hc : c' = c
      · subst hc
        refine ⟨hb name b, by simp, ?_, ?_⟩
        · rw [h1 b]
          cases b <;> simp
        · rw [h1 b]
          simp
      · refine ⟨lf name c' false, by simp, ?_, ?_⟩
        · rw [h2 c' hc]
          simp
        · rw [h2 c' hc]
          simp
    · rw [h1 false, mem_st]
      exact Or.inr ⟨c, rfl⟩
    · rw [h1 false]
      simp

lemma st_card (b : Bool) : (st name b).card = q + 1 := by
  unfold st
  rw [card_insert_of_notMem (by simp),
    card_image_of_injective _ (fun c c' h => by simp only [lf_inj] at h; exact h.1)]
  simp

lemma st_good (b : Bool) :
    (¬ ∃ c, lf name c false ∈ st name b ∧ lf name c true ∈ st name b) ∧
      ∀ c, (∃ b', hb name b' ∈ st name b ∧ lf name c b' ∈ st name b) ∨
        (∃ j, j ≠ c ∧ lf name j false ∈ st name b ∧ lf name j true ∈ st name b) := by
  refine ⟨?_, fun c => Or.inl ⟨b, by simp [st], by simp [mem_st]⟩⟩
  rintro ⟨c, h1, h2⟩
  cases b <;> simp [mem_st] at h1 h2

lemma part2 (hq : 2 ≤ q) (S : Finset (Fin k)) (hS : S.card ≤ q + 1) :
    ((¬ ∃ c, lf name c false ∈ S ∧ lf name c true ∈ S) ∧
      ∀ c, (∃ b, hb name b ∈ S ∧ lf name c b ∈ S) ∨
        (∃ j, j ≠ c ∧ lf name j false ∈ S ∧ lf name j true ∈ S)) ↔
    S = st name false ∨ S = st name true := by
  constructor
  · rintro ⟨hn, hd⟩
    have hd' : ∀ c, ∃ b, hb name b ∈ S ∧ lf name c b ∈ S := fun c =>
      (hd c).resolve_right (fun ⟨j, _, h1, h2⟩ => hn ⟨j, h1, h2⟩)
    choose g hg using hd'
    have hboth : ¬ (hb name false ∈ S ∧ hb name true ∈ S) := by
      rintro ⟨hf, ht⟩
      have hsub : insert (hb name false) (insert (hb name true)
          ((univ : Finset (Fin q)).image (fun c => lf name c (g c)))) ⊆ S := by
        intro x hx
        simp only [mem_insert, mem_image, mem_univ, true_and] at hx
        rcases hx with rfl | rfl | ⟨c, rfl⟩
        · exact hf
        · exact ht
        · exact (hg c).2
      have hc := card_le_card hsub
      rw [card_insert_of_notMem (by simp), card_insert_of_notMem (by simp),
        card_image_of_injective _ (fun c c' h => by simp only [lf_inj] at h; exact h.1)] at hc
      simp only [card_univ, Fintype.card_fin] at hc
      omega
    let c0 : Fin q := ⟨0, by omega⟩
    have huniq : ∀ b, hb name b ∈ S → b = g c0 := by
      intro b hb'
      have h0 := (hg c0).1
      by_contra hne
      apply hboth
      cases b <;> cases h : g c0 <;> rw [h] at h0 hne <;>
        first | exact absurd rfl hne | exact ⟨hb', h0⟩ | exact ⟨h0, hb'⟩
    have hsub : st name (g c0) ⊆ S := by
      intro x hx
      rw [mem_st] at hx
      rcases hx with rfl | ⟨c, rfl⟩
      · exact (hg c0).1
      · have := huniq (g c) (hg c).1
        rw [← this]
        exact (hg c).2
    have heq := eq_of_subset_of_card_le hsub (by rw [st_card]; exact hS)
    cases h : g c0 <;> rw [h] at heq <;> rw [← heq] <;> simp
  · rintro (rfl | rfl)
    · exact st_good name false
    · exact st_good name true

end PEqualNP.Outside.L_lib_884

open PEqualNP.Outside.L_lib_884 in
theorem PEqualNP.Outside.L_lib_884 : ∀ (q k : Nat), 2 ≤ q →
  let V := Option (Fin q) × Bool
  ∀ name : V ↪ Fin k,
  let hub := fun b : Bool => name (none,b)
  let leaf := fun (c : Fin q) (b : Bool) => name (some c,b)
  let star := fun b : Bool => insert (hub b) (Finset.univ.image (fun c : Fin q => leaf c b))
  let neutral := fun S : Finset (Fin k) => ∃ c, leaf c false ∈ S ∧ leaf c true ∈ S
  let desired := fun (c : Fin q) (S : Finset (Fin k)) =>
    (∃ b, hub b ∈ S ∧ leaf c b ∈ S) ∨
    (∃ j, j ≠ c ∧ leaf j false ∈ S ∧ leaf j true ∈ S)
  (∀ P : Equiv.Perm (Fin k), Function.Involutive P →
    let hit := fun S : Finset (Fin k) => ∃ u ∈ S, P u ∈ S ∧ P u ≠ u
    let chosen := fun c : Fin q =>
      (∀ b, P (hub b) = leaf c b) ∧
      ∀ j, j ≠ c → P (leaf j false) = leaf j true
    ((∀ (c : Fin q) (b : Bool), hit {hub b, leaf c false, leaf c true}) ∧ hit (star false)) ↔
      ∃! c, chosen c) ∧
  ∀ S : Finset (Fin k), S.card ≤ q+1 →
    ((¬ neutral S ∧ ∀ c, desired c S) ↔ S = star false ∨ S = star true) := by
  intro q k hq V name hub leaf star neutral desired
  refine ⟨fun P hP => ?_, fun S hS => ?_⟩
  · intro hit chosen
    exact part1 name P hP
  · exact part2 name hq S hS
