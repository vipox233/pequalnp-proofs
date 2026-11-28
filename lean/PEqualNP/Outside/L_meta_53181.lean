import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_53181 : (∀ (n g B : Nat) (L : Fin g → Finset (Fin (n+1) × Bool)) (weight : Fin g → Nat)
  (S : Finset (Fin (n+1))) (R : Finset (Fin g)) (sw : Fin (n+1) → Bool) (off : Fin g → Bool),
  (∀ i ∉ R, ∀ l ∈ L i, l.1 ∉ S → xor (sw l.1) l.2 = off i) →
  letI : ∀ q : Prop, Decidable q := Classical.propDecidable
  let V := Sum Bool (Sum (Fin (n+1)) (Fin g × Bool))
  let pin := fun (b : Bool) => (Sum.inl b : V)
  let var := fun (v : Fin (n+1)) => (Sum.inr (Sum.inl v) : V)
  let aux := fun (i : Fin g) (b : Bool) => (Sum.inr (Sum.inr (i,b)) : V)
  let M := B+1
  (∃ x : Fin (n+1) → Bool, x 0 = false ∧
    (Finset.univ : Finset (Fin g)).sum (fun i =>
      if ∃ l ∈ L i, ∃ r ∈ L i, xor (x l.1) l.2 ≠ xor (x r.1) r.2 then weight i else 0) ≤ B) ↔
  ∃ P ∈ S.powerset, ∃ modes : {i // i ∈ R} → Option Bool, ∃ side : V → Bool,
    side (pin false) = false ∧ side (pin true) = true ∧
    let arc := fun (u v : V) (c : Nat) => if side u = false ∧ side v = true then c else 0
    let force := fun (v : V) (b : Bool) =>
      if b then arc v (pin true) M else arc (pin false) v M
    let fixed := force (var 0) (sw 0) + S.sum (fun v => force (var v) (xor (decide (v ∈ P)) (sw v)))
    let bill := fun (i : Fin g) =>
      if hi : i ∈ R then
        let setting := modes ⟨i,hi⟩
        if setting.isNone then arc (pin false) (pin true) (weight i)
        else (L i).sum (fun l => force (var l.1) (xor (setting.getD false) (xor (sw l.1) l.2)))
      else
        arc (aux i false) (aux i true) (weight i) +
        (L i).sum (fun l =>
          let endpt := if l.1 ∈ S then pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) else var l.1
          arc endpt (aux i false) M + arc (aux i true) endpt M)
    fixed + Finset.univ.sum bill ≤ B) := by
  intro n g B L weight S R sw off hoff
  intro V pin var aux M
  let inst : ∀ q : Prop, Decidable q := Classical.propDecidable
  constructor
  · rintro ⟨x, hx0, hsum⟩
    let mixed : Fin g → Prop := fun i => ∃ l ∈ L i, ∃ r ∈ L i, xor (x l.1) l.2 ≠ xor (x r.1) r.2
    let val : Fin g → Bool := fun i => decide (∃ l ∈ L i, xor (x l.1) l.2 = true)
    have hval : ∀ i, ¬ mixed i → ∀ l ∈ L i, xor (x l.1) l.2 = val i := by
      intro i hm l hl
      by_cases h : ∃ l ∈ L i, xor (x l.1) l.2 = true
      · obtain ⟨r, hr, hrt⟩ := h
        have hv : val i = true := decide_eq_true ⟨r, hr, hrt⟩
        rw [hv]
        by_contra hne
        exact hm ⟨l, hl, r, hr, by rw [hrt]; exact hne⟩
      · have hv : val i = false := decide_eq_false h
        rw [hv]
        by_contra hne
        exact h ⟨l, hl, by simpa using hne⟩
    let P : Finset (Fin (n+1)) := S.filter (fun v => x v = true)
    have hPmem : ∀ v, v ∈ S → decide (v ∈ P) = x v := by
      intro v hv
      cases hxv : x v
      · exact decide_eq_false (by simp [P, hxv])
      · exact decide_eq_true (by simp [P, hxv, hv])
    let modes : {i // i ∈ R} → Option Bool := fun i => if mixed i.1 then none else some (val i.1)
    let side : V → Bool := Sum.elim id (Sum.elim (fun v => xor (x v) (sw v))
      (fun p => if mixed p.1 then p.2 else xor (val p.1) (off p.1)))
    have hpin : ∀ b, side (pin b) = b := fun b => rfl
    have hvar : ∀ v, side (var v) = xor (x v) (sw v) := fun v => rfl
    have haux : ∀ i c, side (aux i c) = if mixed i then c else xor (val i) (off i) := fun i c => rfl
    refine ⟨P, by simp [P], modes, side, rfl, rfl, ?_⟩
    intro arc force fixed bill
    have hforce : ∀ v b, side v = b → force v b = 0 := by
      intro v b h
      subst h
      cases hs : side v <;> simp [force, arc, hs, hpin]
    have hfixed : fixed = 0 := by
      have h0 : force (var 0) (sw 0) = 0 := hforce _ _ (by rw [hvar, hx0]; simp)
      have h1 : S.sum (fun v => force (var v) (xor (decide (v ∈ P)) (sw v))) = 0 :=
        Finset.sum_eq_zero (fun v hv => hforce _ _ (by rw [hvar, hPmem v hv]))
      show force (var 0) (sw 0) + S.sum (fun v => force (var v) (xor (decide (v ∈ P)) (sw v))) = 0
      rw [h0, h1]
    refine le_trans ?_ hsum
    rw [hfixed, zero_add]
    apply Finset.sum_le_sum
    intro i _
    show bill i ≤ (if mixed i then weight i else 0)
    by_cases hi : i ∈ R
    · have hb : bill i = (if (modes ⟨i,hi⟩).isNone then arc (pin false) (pin true) (weight i)
          else (L i).sum (fun l => force (var l.1) (xor ((modes ⟨i,hi⟩).getD false) (xor (sw l.1) l.2)))) :=
        dif_pos hi
      rw [hb]
      by_cases hm : mixed i
      · have hmo : modes ⟨i,hi⟩ = none := if_pos hm
        rw [hmo, if_pos hm]
        simp [arc, hpin]
      · have hmo : modes ⟨i,hi⟩ = some (val i) := if_neg hm
        rw [hmo]
        have hz : (L i).sum (fun l => force (var l.1) (xor ((some (val i)).getD false) (xor (sw l.1) l.2))) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          apply hforce
          rw [hvar]
          have := hval i hm l hl
          revert this
          generalize x l.1 = a
          generalize l.2 = b
          generalize val i = c
          generalize sw l.1 = d
          cases a <;> cases b <;> cases c <;> cases d <;> simp
        have hn : ¬ ((some (val i)).isNone = true) := by simp
        rw [if_neg hn, hz]
        exact Nat.zero_le _
    · let endpt : (Fin (n+1) × Bool) → V := fun l =>
        if l.1 ∈ S then pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) else var l.1
      have hb : bill i = arc (aux i false) (aux i true) (weight i) +
          (L i).sum (fun l => arc (endpt l) (aux i false) M + arc (aux i true) (endpt l) M) :=
        dif_neg hi
      have he : ∀ l ∈ L i, side (endpt l) = xor (xor (x l.1) l.2) (off i) := by
        intro l hl
        by_cases hS : l.1 ∈ S
        · have : endpt l = pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) := if_pos hS
          rw [this, hpin, hPmem _ hS]
        · have : endpt l = var l.1 := if_neg hS
          rw [this, hvar]
          have := hoff i hi l hl hS
          revert this
          generalize x l.1 = a
          generalize l.2 = b
          generalize off i = c
          generalize sw l.1 = d
          cases a <;> cases b <;> cases c <;> cases d <;> simp
      rw [hb]
      by_cases hm : mixed i
      · rw [if_pos hm]
        have hz : (L i).sum (fun l => arc (endpt l) (aux i false) M + arc (aux i true) (endpt l) M) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          simp [arc, haux, hm]
        rw [hz]
        simp only [arc]
        split_ifs <;> simp
      · rw [if_neg hm]
        have hz : (L i).sum (fun l => arc (endpt l) (aux i false) M + arc (aux i true) (endpt l) M) = 0 := by
          apply Finset.sum_eq_zero
          intro l hl
          have h1 := he l hl
          rw [hval i hm l hl] at h1
          simp only [arc, haux, if_neg hm, h1]
          cases xor (val i) (off i) <;> simp
        rw [hz]
        simp only [arc, haux, if_neg hm]
        cases xor (val i) (off i) <;> simp
  · rintro ⟨P, hP, modes, side, hf, ht, hcost⟩
    have hpin : ∀ b, side (pin b) = b := by
      intro b
      cases b
      · exact hf
      · exact ht
    let arc := fun (u v : V) (c : Nat) => if side u = false ∧ side v = true then c else 0
    let force := fun (v : V) (b : Bool) =>
      if b then arc v (pin true) M else arc (pin false) v M
    let fixed := force (var 0) (sw 0) + S.sum (fun v => force (var v) (xor (decide (v ∈ P)) (sw v)))
    let endpt : Fin g → (Fin (n+1) × Bool) → V := fun i l =>
        if l.1 ∈ S then pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) else var l.1
    let bill := fun (i : Fin g) =>
      if hi : i ∈ R then
        if (modes ⟨i,hi⟩).isNone then arc (pin false) (pin true) (weight i)
        else (L i).sum (fun l => force (var l.1) (xor ((modes ⟨i,hi⟩).getD false) (xor (sw l.1) l.2)))
      else
        arc (aux i false) (aux i true) (weight i) +
        (L i).sum (fun l => arc (endpt i l) (aux i false) M + arc (aux i true) (endpt i l) M)
    have hcost' : fixed + Finset.univ.sum bill ≤ B := hcost
    have hfix : fixed ≤ B := le_trans (Nat.le_add_right _ _) hcost'
    have hbill : ∀ i, bill i ≤ B := fun i =>
      le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
        (le_trans (Nat.le_add_left _ _) hcost')
    have harc : ∀ u v, arc u v M ≤ B → ¬ (side u = false ∧ side v = true) := by
      intro u v h hc
      have h2 : arc u v M = B + 1 := if_pos hc
      rw [h2] at h
      exact absurd h (Nat.not_succ_le_self B)
    have hforce : ∀ v b, force v b ≤ B → side v = b := by
      intro v b h
      cases b
      · have h' : force v false = arc (pin false) v M := if_neg (by simp)
        rw [h'] at h
        have := harc (pin false) v h
        rw [hpin] at this
        cases hs : side v
        · rfl
        · exact absurd ⟨rfl, hs⟩ this
      · have h' : force v true = arc v (pin true) M := if_pos rfl
        rw [h'] at h
        have := harc v (pin true) h
        rw [hpin] at this
        cases hs : side v
        · exact absurd ⟨hs, rfl⟩ this
        · rfl
    have h0 : side (var 0) = sw 0 := hforce _ _ (le_trans (Nat.le_add_right _ _) hfix)
    have hS : ∀ v ∈ S, side (var v) = xor (decide (v ∈ P)) (sw v) := fun v hv =>
      hforce _ _ (le_trans (Finset.single_le_sum
        (f := fun v => force (var v) (xor (decide (v ∈ P)) (sw v))) (fun _ _ => Nat.zero_le _) hv)
        (le_trans (Nat.le_add_left _ _) hfix))
    refine ⟨fun v => xor (side (var v)) (sw v), ?_, ?_⟩
    · show xor (side (var 0)) (sw 0) = false
      rw [h0]
      simp
    · refine le_trans ?_ (le_trans (Nat.le_add_left _ _) hcost')
      apply Finset.sum_le_sum
      intro i _
      show (if (∃ l ∈ L i, ∃ r ∈ L i, xor (xor (side (var l.1)) (sw l.1)) l.2 ≠ xor (xor (side (var r.1)) (sw r.1)) r.2) then weight i else 0) ≤ bill i
      by_cases hm : (∃ l ∈ L i, ∃ r ∈ L i, xor (xor (side (var l.1)) (sw l.1)) l.2 ≠ xor (xor (side (var r.1)) (sw r.1)) r.2)
      swap
      · rw [if_neg hm]
        exact Nat.zero_le _
      rw [if_pos hm]
      obtain ⟨l, hl, r, hr, hne⟩ := hm
      by_cases hi : i ∈ R
      · have hb : bill i = (if (modes ⟨i,hi⟩).isNone then arc (pin false) (pin true) (weight i)
            else (L i).sum (fun l => force (var l.1) (xor ((modes ⟨i,hi⟩).getD false) (xor (sw l.1) l.2)))) :=
          dif_pos hi
        cases hmo : modes ⟨i,hi⟩ with
        | none =>
          rw [hb, hmo]
          have hn : (none : Option Bool).isNone = true := rfl
          rw [if_pos hn]
          have h2 : arc (pin false) (pin true) (weight i) = weight i := if_pos ⟨hpin false, hpin true⟩
          rw [h2]
        | some b =>
          exfalso
          have hB := hbill i
          rw [hb, hmo] at hB
          have hn : ¬ ((some b).isNone = true) := by simp
          rw [if_neg hn] at hB
          have hB' : (L i).sum (fun l => force (var l.1) (xor b (xor (sw l.1) l.2))) ≤ B := hB
          have hk : ∀ l ∈ L i, side (var l.1) = xor b (xor (sw l.1) l.2) := fun l hl =>
            hforce _ _ (le_trans (Finset.single_le_sum
              (f := fun l => force (var l.1) (xor b (xor (sw l.1) l.2))) (fun _ _ => Nat.zero_le _) hl) hB')
          apply hne
          show xor (xor (side (var l.1)) (sw l.1)) l.2 = xor (xor (side (var r.1)) (sw r.1)) r.2
          rw [hk l hl, hk r hr]
          generalize sw l.1 = a
          generalize l.2 = c
          generalize sw r.1 = d
          generalize r.2 = e
          cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp
      · have hb : bill i = arc (aux i false) (aux i true) (weight i) +
            (L i).sum (fun l => arc (endpt i l) (aux i false) M + arc (aux i true) (endpt i l) M) :=
          dif_neg hi
        have hB := hbill i
        rw [hb] at hB
        have hk : ∀ l ∈ L i, arc (endpt i l) (aux i false) M + arc (aux i true) (endpt i l) M ≤ B :=
          fun l hl => le_trans (Finset.single_le_sum
            (f := fun l => arc (endpt i l) (aux i false) M + arc (aux i true) (endpt i l) M)
            (fun _ _ => Nat.zero_le _) hl) (le_trans (Nat.le_add_left _ _) hB)
        have he : ∀ l ∈ L i, side (endpt i l) = xor (xor (xor (side (var l.1)) (sw l.1)) l.2) (off i) := by
          intro l hl
          by_cases hSl : l.1 ∈ S
          · have : endpt i l = pin (xor (xor (decide (l.1 ∈ P)) l.2) (off i)) := if_pos hSl
            rw [this, hpin, hS _ hSl]
            generalize decide (l.1 ∈ P) = a
            generalize l.2 = b
            generalize off i = c
            generalize sw l.1 = d
            cases a <;> cases b <;> cases c <;> cases d <;> simp
          · have : endpt i l = var l.1 := if_neg hSl
            rw [this]
            have := hoff i hi l hl hSl
            revert this
            generalize side (var l.1) = a
            generalize l.2 = b
            generalize off i = c
            generalize sw l.1 = d
            cases a <;> cases b <;> cases c <;> cases d <;> simp
        have hl1 := harc _ _ (le_trans (Nat.le_add_right _ _) (hk l hl))
        have hl2 := harc _ _ (le_trans (Nat.le_add_left _ _) (hk l hl))
        have hr1 := harc _ _ (le_trans (Nat.le_add_right _ _) (hk r hr))
        have hr2 := harc _ _ (le_trans (Nat.le_add_left _ _) (hk r hr))
        have hne' : side (endpt i l) ≠ side (endpt i r) := by
          rw [he l hl, he r hr]
          intro h
          apply hne
          show xor (xor (side (var l.1)) (sw l.1)) l.2 = xor (xor (side (var r.1)) (sw r.1)) r.2
          revert h
          generalize xor (xor (side (var l.1)) (sw l.1)) l.2 = a
          generalize xor (xor (side (var r.1)) (sw r.1)) r.2 = b
          generalize off i = c
          cases a <;> cases b <;> cases c <;> simp
        have hw : side (aux i false) = false ∧ side (aux i true) = true := by
          revert hl1 hl2 hr1 hr2 hne'
          generalize side (endpt i l) = a
          generalize side (endpt i r) = b
          generalize side (aux i false) = c
          generalize side (aux i true) = d
          cases a <;> cases b <;> cases c <;> cases d <;> simp
        rw [hb]
        have h2 : arc (aux i false) (aux i true) (weight i) = weight i := if_pos hw
        rw [h2]
        exact Nat.le_add_right _ _
