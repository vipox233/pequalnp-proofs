import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38162

private lemma fin3_third (a b : Fin 3) (h : a ≠ b) : ∃ u : Fin 3, u ≠ a ∧ u ≠ b := by
  fin_cases a <;> fin_cases b <;> first | contradiction | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩

private lemma fin3_ne_three (a b c m : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m ≠ a) (hmb : m ≠ b) (hmc : m ≠ c) : False := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases m <;> simp_all

private lemma fin3_ne_shifted (a m : Fin 3) (b1 b2 : Fin 2) (hne : b1 ≠ b2)
    (hma : m ≠ a) (hmb1 : m ≠ a + if b1 = 0 then 1 else 2)
    (hmb2 : m ≠ a + if b2 = 0 then 1 else 2) : False := by
  fin_cases a <;> fin_cases b1 <;> fin_cases b2 <;> fin_cases m <;> simp_all

private lemma exists_other_two {r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hcover : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    (∀ x (i : Fin 3), ¬ rowOK x i → ∀ j : Fin 3, j ≠ i → rowOK x j) ∧
    (∀ y (i : Fin 3), ¬ colOK y i → ∀ j : Fin 3, j ≠ i → colOK y j) := by
  constructor
  · intro x i hxi j hji
    by_contra hxj
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp_all
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    obtain ⟨y, hyk⟩ := (hnondeg k).2
    obtain ⟨m, hxm, hym⟩ := hcover x y
    have hm : m = i ∨ m = j ∨ m = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all
    rcases hm with rfl | rfl | rfl
    · exact hxi hxm
    · exact hxj hxm
    · exact hyk hym
  · intro y i hyi j hji
    by_contra hyj
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> simp_all
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨2, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
      · exact ⟨1, by decide, by decide⟩
      · exact ⟨0, by decide, by decide⟩
    obtain ⟨x, hxk⟩ := (hnondeg k).1
    obtain ⟨m, hxm, hym⟩ := hcover x y
    have hm : m = i ∨ m = j ∨ m = k := by
      fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases m <;> simp_all
    rcases hm with rfl | rfl | rfl
    · exact hyi hym
    · exact hyj hym
    · exact hxk hxm

private lemma upper {n r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hcover : ∀ x y, ∃ i, rowOK x i ∧ colOK y i)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) :
    ∃ (send : (Fin n → Fin r) → Nat) (back : Nat → (Fin n → Fin c) → Nat)
      (pick : Nat → Nat → (Fin n → Fin 3)),
      (∀ (x : Fin n → Fin r) (y : Fin n → Fin c) (j : Fin n),
        let i := pick (send x) (back (send x) y) j
        rowOK (x j) i ∧ colOK (y j) i) ∧
      ((Finset.univ : Finset (Fin n → Fin r)).image send).card = 3^n ∧
      ((Finset.univ : Finset ((Fin n → Fin r) × (Fin n → Fin c))).image
        (fun v => (send v.1, back (send v.1) v.2))).card = 6^n := by
  classical
  have ⟨hrow2, hcol2⟩ := exists_other_two rowOK colOK hcover hnondeg
  choose xr hxr using fun i : Fin 3 => (hnondeg i).1
  choose yc hyc using fun i : Fin 3 => (hnondeg i).2
  let miss : Fin r → Fin 3 := fun x =>
    if ¬ rowOK x 0 then 0 else if ¬ rowOK x 1 then 1 else 2
  have hmiss_ok : ∀ x (b : Fin 2), rowOK x (miss x + if b = 0 then 1 else 2) := by
    intro x b
    simp only [miss]
    by_cases h0 : ¬ rowOK x 0
    · simp only [h0]
      fin_cases b
      · exact hrow2 x 0 h0 1 (by decide)
      · exact hrow2 x 0 h0 2 (by decide)
    · simp only [h0, ↓reduceIte]
      push Not at h0
      by_cases h1 : ¬ rowOK x 1
      · simp only [h1]
        fin_cases b
        · exact hrow2 x 1 h1 2 (by decide)
        · exact h0
      · simp only [h1, ↓reduceIte]
        push Not at h1
        fin_cases b
        · exact h0
        · exact h1
  have hmiss_xr : ∀ a : Fin 3, miss (xr a) = a := by
    intro a
    fin_cases a
    · simp [miss, hxr 0]
    · have h0 : rowOK (xr 1) 0 := hrow2 (xr 1) 1 (hxr 1) 0 (by decide)
      simp [miss, h0, hxr 1]
    · have h0 : rowOK (xr 2) 0 := hrow2 (xr 2) 2 (hxr 2) 0 (by decide)
      have h1 : rowOK (xr 2) 1 := hrow2 (xr 2) 2 (hxr 2) 1 (by decide)
      simp [miss, h0, h1]
  let pickBit : Fin 3 → Fin c → Fin 2 := fun m y =>
    if colOK y (m + 1) then 0 else 1
  have hpickBit_ok : ∀ m y, colOK y (m + if pickBit m y = 0 then 1 else 2) := by
    intro m y
    simp only [pickBit]
    by_cases h : colOK y (m + 1)
    · simp [h]
    · simp only [h, ↓reduceIte]
      have hne : m + 2 ≠ m + 1 := by fin_cases m <;> decide
      exact hcol2 y (m + 1) h (m + 2) hne
  have hpickBit_yc : ∀ (m : Fin 3) (b : Fin 2),
      pickBit m (yc (m + if b = 0 then 2 else 1)) = b := by
    intro m b
    fin_cases b
    · simp only [pickBit]
      have hne : m + 1 ≠ m + 2 := by fin_cases m <;> decide
      have hok : colOK (yc (m + 2)) (m + 1) := hcol2 (yc (m + 2)) (m + 2) (hyc (m + 2)) (m + 1) hne
      simp [hok]
    · simp only [pickBit]
      have : ¬ colOK (yc (m + 1)) (m + 1) := hyc (m + 1)
      simp [this]
  let e3 : (Fin n → Fin 3) ≃ Fin (3^n) := Fintype.equivFinOfCardEq (by simp)
  let e2 : (Fin n → Fin 2) ≃ Fin (2^n) := Fintype.equivFinOfCardEq (by simp)
  let dec3 : Nat → (Fin n → Fin 3) := fun s =>
    if h : s < 3^n then e3.symm ⟨s, h⟩ else fun _ => 0
  let dec2 : Nat → (Fin n → Fin 2) := fun t =>
    if h : t < 2^n then e2.symm ⟨t, h⟩ else fun _ => 0
  let send : (Fin n → Fin r) → Nat := fun x => (e3 (fun j => miss (x j))).val
  let back : Nat → (Fin n → Fin c) → Nat := fun s y =>
    (e2 (fun j => pickBit (dec3 s j) (y j))).val
  let pick : Nat → Nat → (Fin n → Fin 3) := fun s t j =>
    dec3 s j + if dec2 t j = 0 then 1 else 2
  have hdec3_send : ∀ x, dec3 (send x) = fun j => miss (x j) := by
    intro x
    simp [dec3, send, (e3 _).isLt]
  have hdec2_back : ∀ s y, dec2 (back s y) = fun j => pickBit (dec3 s j) (y j) := by
    intro s y
    simp [dec2, back, (e2 _).isLt]
  refine ⟨send, back, pick, ?_, ?_, ?_⟩
  · intro x y j
    simp only [pick, hdec3_send, hdec2_back]
    exact ⟨hmiss_ok (x j) _, hpickBit_ok (miss (x j)) (y j)⟩
  · have himg : (Finset.univ : Finset (Fin n → Fin r)).image send = Finset.range (3^n) := by
      ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      · rintro ⟨x, rfl⟩; exact (e3 _).isLt
      · intro hs
        refine ⟨fun j => xr (e3.symm ⟨s, hs⟩ j), ?_⟩
        simp [send, hmiss_xr]
    rw [himg, Finset.card_range]
  · have himg : ((Finset.univ : Finset ((Fin n → Fin r) × (Fin n → Fin c))).image
        (fun v => (send v.1, back (send v.1) v.2))) = Finset.range (3^n) ×ˢ Finset.range (2^n) := by
      ext ⟨s, t⟩
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨⟨x, y⟩, h⟩
        have hs : send x = s := congrArg Prod.fst h
        have ht : back (send x) y = t := congrArg Prod.snd h
        exact ⟨hs ▸ (e3 _).isLt, ht ▸ (e2 _).isLt⟩
      · rintro ⟨hs, ht⟩
        let a := e3.symm ⟨s, hs⟩
        let b := e2.symm ⟨t, ht⟩
        refine ⟨(fun j => xr (a j), fun j => yc (a j + if b j = 0 then 2 else 1)), ?_⟩
        have h1 : send (fun j => xr (a j)) = s := by simp [send, hmiss_xr, a]
        have h2 : back s (fun j => yc (a j + if b j = 0 then 2 else 1)) = t := by
          simp [back, dec3, hs, a, hpickBit_yc, b]
        exact Prod.ext h1 (h1 ▸ h2)
    rw [himg, Finset.card_product, Finset.card_range, Finset.card_range, ← mul_pow]; rfl

private lemma lower {n r c : Nat}
    (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop)
    (hnondeg : ∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i))
    (send : (Fin n → Fin r) → Nat) (back : Nat → (Fin n → Fin c) → Nat)
    (pick : Nat → Nat → (Fin n → Fin 3))
    (hworks : ∀ (x : Fin n → Fin r) (y : Fin n → Fin c) (j : Fin n),
      let i := pick (send x) (back (send x) y) j
      rowOK (x j) i ∧ colOK (y j) i) :
    3^n ≤ ((Finset.univ : Finset (Fin n → Fin r)).image send).card ∧
    6^n ≤ ((Finset.univ : Finset ((Fin n → Fin r) × (Fin n → Fin c))).image
      (fun v => (send v.1, back (send v.1) v.2))).card := by
  classical
  choose xr hxr using fun i : Fin 3 => (hnondeg i).1
  choose yc hyc using fun i : Fin 3 => (hnondeg i).2
  have hsend_inj : Function.Injective (fun a : Fin n → Fin 3 => send (fun j => xr (a j))) := by
    intro a1 a2 heq
    ext j
    by_contra hne
    have hne' : a1 j ≠ a2 j := fun h => hne (congrArg Fin.val h)
    obtain ⟨u, hu1, hu2⟩ := fin3_third (a1 j) (a2 j) hne'
    let y : Fin n → Fin c := fun _ => yc u
    have h1 := hworks (fun k => xr (a1 k)) y j
    have h2 := hworks (fun k => xr (a2 k)) y j
    dsimp only at heq h1 h2
    rw [heq] at h1
    set m := pick (send (fun k => xr (a2 k))) (back (send (fun k => xr (a2 k))) y) j
    have hm1 : m ≠ a1 j := fun h => hxr (a1 j) (h ▸ h1.1)
    have hm2 : m ≠ a2 j := fun h => hxr (a2 j) (h ▸ h2.1)
    have hmu : m ≠ u := fun h => by rw [h] at h1; exact hyc u h1.2
    exact fin3_ne_three (a1 j) (a2 j) u m hne' hu1.symm hu2.symm hm1 hm2 hmu
  constructor
  · have hsub : (Finset.univ : Finset (Fin n → Fin 3)).image (fun a => send (fun j => xr (a j))) ⊆
        (Finset.univ : Finset (Fin n → Fin r)).image send := by
      intro s hs
      rcases Finset.mem_image.mp hs with ⟨a, _, rfl⟩
      exact Finset.mem_image.mpr ⟨fun j => xr (a j), Finset.mem_univ _, rfl⟩
    calc 3^n = (Finset.univ : Finset (Fin n → Fin 3)).card := by simp
      _ = ((Finset.univ : Finset (Fin n → Fin 3)).image (fun a => send (fun j => xr (a j)))).card :=
          (Finset.card_image_of_injective _ hsend_inj).symm
      _ ≤ ((Finset.univ : Finset (Fin n → Fin r)).image send).card := Finset.card_le_card hsub
  · let mkY : (Fin n → Fin 3) → (Fin n → Fin 2) → (Fin n → Fin c) := fun a b j =>
      yc (a j + if b j = 0 then 1 else 2)
    let f : (Fin n → Fin 3) × (Fin n → Fin 2) → Nat × Nat := fun p =>
      (send (fun j => xr (p.1 j)), back (send (fun j => xr (p.1 j))) (mkY p.1 p.2))
    have hfinj : Function.Injective f := by
      rintro ⟨a1, b1⟩ ⟨a2, b2⟩ heq
      have ha : a1 = a2 := hsend_inj (congrArg Prod.fst heq)
      subst ha
      have hback : back (send (fun j => xr (a1 j))) (mkY a1 b1) =
                   back (send (fun j => xr (a1 j))) (mkY a1 b2) := congrArg Prod.snd heq
      have hb : b1 = b2 := by
        ext j
        by_contra hne
        have hne' : b1 j ≠ b2 j := fun h => hne (congrArg Fin.val h)
        have h1 := hworks (fun k => xr (a1 k)) (mkY a1 b1) j
        have h2 := hworks (fun k => xr (a1 k)) (mkY a1 b2) j
        rw [hback] at h1
        set m := pick (send (fun k => xr (a1 k))) (back (send (fun k => xr (a1 k))) (mkY a1 b2)) j
        have hma : m ≠ a1 j := fun h => hxr (a1 j) (h ▸ h1.1)
        have hmb1 : m ≠ a1 j + if b1 j = 0 then 1 else 2 := fun h => hyc _ (h ▸ h1.2)
        have hmb2 : m ≠ a1 j + if b2 j = 0 then 1 else 2 := fun h => hyc _ (h ▸ h2.2)
        exact fin3_ne_shifted (a1 j) m (b1 j) (b2 j) hne' hma hmb1 hmb2
      exact Prod.ext rfl hb
    have hsub : (Finset.univ : Finset ((Fin n → Fin 3) × (Fin n → Fin 2))).image f ⊆
        (Finset.univ : Finset ((Fin n → Fin r) × (Fin n → Fin c))).image
          (fun v => (send v.1, back (send v.1) v.2)) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨⟨a, b⟩, _, rfl⟩
      exact Finset.mem_image.mpr ⟨(fun j => xr (a j), mkY a b), Finset.mem_univ _, rfl⟩
    calc 6^n = (3 * 2)^n := rfl
      _ = 3^n * 2^n := mul_pow 3 2 n
      _ = (Finset.univ : Finset ((Fin n → Fin 3) × (Fin n → Fin 2))).card := by simp
      _ = ((Finset.univ : Finset ((Fin n → Fin 3) × (Fin n → Fin 2))).image f).card :=
          (Finset.card_image_of_injective _ hfinj).symm
      _ ≤ _ := Finset.card_le_card hsub

end PEqualNP.Outside.L_meta_38162

theorem PEqualNP.Outside.L_meta_38162 : ∀ (n r c : Nat) (rowOK : Fin r → Fin 3 → Prop) (colOK : Fin c → Fin 3 → Prop),
  (∀ x y, ∃ i, rowOK x i ∧ colOK y i) →
  (∀ i, (∃ x, ¬ rowOK x i) ∧ (∃ y, ¬ colOK y i)) →
  let Rows := Fin n → Fin r
  let Cols := Fin n → Fin c
  let Labels := Fin n → Fin 3
  let works := fun (send : Rows → Nat) (back : Nat → Cols → Nat)
      (pick : Nat → Nat → Labels) =>
    ∀ (x : Rows) (y : Cols) (j : Fin n),
      let i := pick (send x) (back (send x) y) j
      rowOK (x j) i ∧ colOK (y j) i
  let messages := fun (send : Rows → Nat) =>
    ((Finset.univ : Finset Rows).image send).card
  let transcripts := fun (send : Rows → Nat) (back : Nat → Cols → Nat) =>
    ((Finset.univ : Finset (Rows × Cols)).image
      (fun v => (send v.1, back (send v.1) v.2))).card
  (∃ send back pick, works send back pick ∧
    messages send = 3^n ∧ transcripts send back = 6^n) ∧
  ∀ send back pick, works send back pick →
    3^n ≤ messages send ∧ 6^n ≤ transcripts send back := by
  intro n r c rowOK colOK hcover hnondeg
  exact ⟨PEqualNP.Outside.L_meta_38162.upper rowOK colOK hcover hnondeg,
         fun send back pick hw => PEqualNP.Outside.L_meta_38162.lower rowOK colOK hnondeg send back pick hw⟩
