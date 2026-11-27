import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_658

def proj {n : ℕ} (S : Finset (Fin n)) (F : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n)) :=
  F.image (fun x => x ∩ S)

theorem mem_proj {n : ℕ} {S : Finset (Fin n)} {F : Finset (Finset (Fin n))}
    {y : Finset (Fin n)} : y ∈ proj S F ↔ ∃ x ∈ F, x ∩ S = y := by
  simp [proj]

theorem erase_closed_down {n : ℕ} (s s' : Fin n) (F : Finset (Finset (Fin n)))
    (h : ∀ x ∈ F, x.erase s' ∈ F) :
    ∀ x ∈ Down.compression s F, x.erase s' ∈ Down.compression s F := by
  intro x hx
  by_cases hss : s' = s
  · subst hss
    exact Down.erase_mem_compression_of_mem_compression hx
  rw [Down.mem_compression] at hx ⊢
  rcases hx with ⟨hxF, hxe⟩ | ⟨hxF, hins⟩
  · left
    refine ⟨h x hxF, ?_⟩
    rw [Finset.erase_right_comm]
    exact h _ hxe
  · have hs : s ∉ x := by
      intro hs
      rw [Finset.insert_eq_of_mem hs] at hins
      exact hxF hins
    have h1 : insert s (x.erase s') ∈ F := by
      have h2 := h _ hins
      rwa [Finset.erase_insert_of_ne (Ne.symm hss)] at h2
    by_cases hxe : x.erase s' ∈ F
    · left
      refine ⟨hxe, ?_⟩
      have h3 : s ∉ x.erase s' := fun h4 => hs (Finset.mem_of_mem_erase h4)
      rwa [Finset.erase_eq_of_notMem h3]
    · right
      exact ⟨hxe, h1⟩

theorem proj_down_card_le {n : ℕ} (s : Fin n) (S : Finset (Fin n))
    (F : Finset (Finset (Fin n))) :
    (proj S (Down.compression s F)).card ≤ (proj S F).card := by
  by_cases hsS : s ∈ S
  · have hsub : proj S (Down.compression s F) ⊆ Down.compression s (proj S F) := by
      intro y hy
      rw [mem_proj] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [Down.mem_compression] at hx ⊢
      rcases hx with ⟨hxF, hxe⟩ | ⟨hxF, hins⟩
      · left
        refine ⟨mem_proj.2 ⟨x, hxF, rfl⟩, mem_proj.2 ⟨x.erase s, hxe, ?_⟩⟩
        ext a
        simp only [Finset.mem_inter, Finset.mem_erase]
        tauto
      · have hs : s ∉ x := by
          intro hs
          rw [Finset.insert_eq_of_mem hs] at hins
          exact hxF hins
        have h1 : insert s (x ∩ S) ∈ proj S F := by
          refine mem_proj.2 ⟨insert s x, hins, ?_⟩
          exact Finset.insert_inter_of_mem hsS
        by_cases hxp : x ∩ S ∈ proj S F
        · left
          refine ⟨hxp, ?_⟩
          have h3 : s ∉ x ∩ S := fun h4 => hs (Finset.mem_of_mem_inter_left h4)
          rwa [Finset.erase_eq_of_notMem h3]
        · right
          exact ⟨hxp, h1⟩
    exact (Finset.card_le_card hsub).trans (le_of_eq (Down.card_compression s (proj S F)))
  · apply Finset.card_le_card
    intro y hy
    rw [mem_proj] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Down.mem_compression] at hx
    rcases hx with ⟨hxF, -⟩ | ⟨-, hins⟩
    · exact ⟨x, hxF, rfl⟩
    · exact ⟨insert s x, hins, Finset.insert_inter_of_notMem hsS⟩

theorem exists_compressed {n : ℕ} (l : List (Fin n)) (F : Finset (Finset (Fin n))) :
    ∃ G : Finset (Finset (Fin n)), G.card = F.card ∧
      (∀ s ∈ l, ∀ x ∈ G, x.erase s ∈ G) ∧
      ∀ S : Finset (Fin n), (proj S G).card ≤ (proj S F).card := by
  induction l with
  | nil => exact ⟨F, rfl, by simp, fun S => le_rfl⟩
  | cons s l ih =>
    obtain ⟨G, hcard, hcl, hproj⟩ := ih
    refine ⟨Down.compression s G, (Down.card_compression s G).trans hcard, ?_, ?_⟩
    · intro s' hs' x hx
      rcases List.mem_cons.1 hs' with rfl | hs'
      · exact Down.erase_mem_compression_of_mem_compression hx
      · exact erase_closed_down s s' G (hcl s' hs') x hx
    · intro S
      exact (proj_down_card_le s S G).trans (hproj S)

theorem down_closed_of_erase {n : ℕ} {G : Finset (Finset (Fin n))}
    (h : ∀ s : Fin n, ∀ x ∈ G, x.erase s ∈ G) :
    ∀ x ∈ G, ∀ y : Finset (Fin n), y ⊆ x → y ∈ G := by
  have key : ∀ d : Finset (Fin n), ∀ x ∈ G, x \ d ∈ G := by
    intro d
    induction d using Finset.induction_on with
    | empty =>
      intro x hx
      simpa using hx
    | insert a d _ ih =>
      intro x hx
      rw [Finset.sdiff_insert]
      exact h a _ (ih x hx)
  intro x hx y hyx
  have h1 := key (x \ y) x hx
  rwa [Finset.sdiff_sdiff_eq_self hyx] at h1

theorem forward {n r : ℕ} (scope : Fin r → Finset (Fin n)) (cap : Fin r → ℕ) (t : ℕ)
    (A : Finset (Fin r × Finset (Fin n)))
    (ht : t ≤ ((Finset.univ : Finset (Finset (Fin n))).filter
      (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ A)).card)
    (hcap : ∀ i : Fin r, (A.filter (fun e => e.1 = i)).card ≤ cap i) :
    ∃ F : Finset (Finset (Fin n)), F.card = t ∧
      (∀ x ∈ F, ∀ y : Finset (Fin n), y ⊆ x → y ∈ F) ∧
      ∀ i : Fin r, (F.filter (fun a => a ⊆ scope i)).card ≤ cap i := by
  obtain ⟨F₀, hF₀sub, hF₀card⟩ := Finset.exists_subset_card_eq ht
  obtain ⟨G, hGcard, hGcl, hGproj⟩ := exists_compressed (List.finRange n) F₀
  refine ⟨G, hGcard.trans hF₀card, ?_, ?_⟩
  · exact down_closed_of_erase (fun s x hx => hGcl s (List.mem_finRange s) x hx)
  · intro i
    have h1 : (G.filter (fun a => a ⊆ scope i)).card ≤ (proj (scope i) G).card := by
      apply Finset.card_le_card
      intro a ha
      rw [Finset.mem_filter] at ha
      exact mem_proj.2 ⟨a, ha.1, Finset.inter_eq_left.2 ha.2⟩
    have h2 : (proj (scope i) F₀).card ≤ (A.filter (fun e => e.1 = i)).card := by
      apply Finset.card_le_card_of_injOn (fun p => (i, p))
      · intro p hp
        obtain ⟨x, hx, rfl⟩ := mem_proj.1 hp
        have hx' := hF₀sub hx
        rw [Finset.mem_filter] at hx'
        exact Finset.mem_filter.2 ⟨hx'.2 i, rfl⟩
      · intro p _ q _ hpq
        exact (Prod.mk.inj hpq).2
    exact h1.trans ((hGproj (scope i)).trans (h2.trans (hcap i)))

theorem backward {n r : ℕ} (scope : Fin r → Finset (Fin n)) (cap : Fin r → ℕ) (t : ℕ)
    (F : Finset (Finset (Fin n))) (hFcard : F.card = t)
    (hFcl : ∀ x ∈ F, ∀ y : Finset (Fin n), y ⊆ x → y ∈ F)
    (hFcap : ∀ i : Fin r, (F.filter (fun a => a ⊆ scope i)).card ≤ cap i) :
    ∃ A ∈ ((Finset.univ : Finset (Fin r × Finset (Fin n))).filter
        (fun e => e.2 ⊆ scope e.1)).powerset,
      t ≤ ((Finset.univ : Finset (Finset (Fin n))).filter
        (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ A)).card ∧
      ∀ i : Fin r, (A.filter (fun e => e.1 = i)).card ≤ cap i := by
  refine ⟨((Finset.univ : Finset (Fin r × Finset (Fin n))).filter
    (fun e => e.2 ⊆ scope e.1)).filter (fun e => e.2 ∈ F), ?_, ?_, ?_⟩
  · exact Finset.mem_powerset.2 (Finset.filter_subset _ _)
  · rw [← hFcard]
    apply Finset.card_le_card
    intro x hx
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun i => ?_⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact Finset.inter_subset_right
    · exact hFcl x hx _ Finset.inter_subset_left
  · intro i
    refine le_trans ?_ (hFcap i)
    apply Finset.card_le_card_of_injOn (fun e => e.2)
    · intro e he
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter] at he
      obtain ⟨⟨⟨-, hsub⟩, hmem⟩, hi⟩ := he
      rw [hi] at hsub
      exact Finset.mem_filter.2 ⟨hmem, hsub⟩
    · intro e he e' he' hee
      rw [Finset.mem_coe, Finset.mem_filter] at he he'
      exact Prod.ext (he.2.trans he'.2.symm) hee

end PEqualNP.Outside.L_lib_658

theorem PEqualNP.Outside.L_lib_658 : (∀ (n r : Nat) (scope : Fin r → Finset (Fin n)) (cap : Fin r → Nat) (t : Nat),
  let Site := Fin n
  let Slot := Fin r × Finset Site
  let full := (Finset.univ : Finset Slot).filter (fun e => e.2 ⊆ scope e.1)
  let words := (Finset.univ : Finset (Finset Site))
  (∃ A ∈ full.powerset,
    t ≤ (words.filter (fun x => ∀ i : Fin r, (i, x ∩ scope i) ∈ A)).card ∧
    ∀ i : Fin r, (A.filter (fun e => e.1 = i)).card ≤ cap i) ↔
  ∃ F : Finset (Finset Site), F.card = t ∧
    (∀ x ∈ F, ∀ y : Finset Site, y ⊆ x → y ∈ F) ∧
    ∀ i : Fin r, (F.filter (fun a => a ⊆ scope i)).card ≤ cap i) := by
  intro n r scope cap t
  constructor
  · rintro ⟨A, -, ht, hcap⟩
    exact PEqualNP.Outside.L_lib_658.forward scope cap t A ht hcap
  · rintro ⟨F, hFcard, hFcl, hFcap⟩
    exact PEqualNP.Outside.L_lib_658.backward scope cap t F hFcard hFcl hFcap
